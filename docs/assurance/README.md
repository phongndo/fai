# Assurance: how the Rust implementation is held to the Lean specification

This directory describes, and records, what this repository can show about its Rust compiler
relative to the Lean semantics in `spec/`. It was built as an experiment (branch
`experiment/lean-rust-conformance`); the last section says which parts are worth keeping.

**What it is not.** Nothing here makes the compiler formally verified end to end. One pass's
permissions are proved, one checker is proved and runs on the pass's real outputs in the tests
and, when asked (`--check-dce`, `FIR_CHECK_DCE`), in the compiler itself,
one transformation validator runs on every compilation but is not proved, and several links
(scalarization, `cf.try` lowering, module composition, instruction selection, encoding) are
tested only. The table under [Guarantees](#guarantees) is the exact status of each link.

Files here:

| File | What | Made by |
|---|---|---|
| `dce.md` | Dead code elimination from the theorem to the binary, link by link: what is proved, checked, tested, assumed, and trusted | by hand |
| `layer-audit.md` | The HFIR → MFIR → LFIR boundaries audited, a vertical slice, the DCE checkers compared and measured, the observation tooling, and source lines in native code | by hand |
| `op-contracts.json` | Per op kind (536 kinds, modifiers included): identity, fields, modifiers, layers, typing, declared effects, and the DCE permission with its evidence | `lake exe gen-rust manifest` |
| `proofs.lock.json` | Reviewed fingerprints of the 40 registered claims: statement, hypothesis count, axioms, and fingerprints of the `Fir` definitions they depend on | `lake exe fir-audit --update` |
| `proofs.md` | The claims as Lean prints them, with axioms and dependency counts | `lake exe fir-audit --report` |
| `adversarial.md` | The last `cargo xtask mutate` run: each planted defect and the diagnostic that caught it | `cargo xtask mutate` |

## The one command

```sh
nix develop -c cargo xtask verify full     # the required check (CI runs it: .github/workflows/verify.yml)
nix develop -c cargo xtask verify fast     # local, partial: says what it skipped, never claims "full"
nix develop -c cargo xtask mutate [NAME…]  # the checkers' own adversarial tests
```

`verify full` succeeds only if every one of these ran and passed (`target/verify/report.md` and
`report.json` record each, with times, the revision, whether the tree was dirty, and every
toolchain's version):

1. **Tools and environment.** `cargo`, `rustc`, `lake`, `clang`, `cbindgen`, and off AArch64
   `aarch64-unknown-linux-gnu-cc` and `qemu-aarch64` must be on `PATH`. Variables that weaken
   checks (`FIR_REF`, `FIR_FUZZ`, `FIR_CC`, …) are cleared for every child; `FIR_REF=none` in
   the environment fails the run outright.
2. **Lean from scratch.** `spec/.lake/build` is removed and `lake build` rebuilds the library,
   `fir-ref`, the generators, and `fir-audit` (about 80 s here). `--no-lean-clean` skips the
   removal.
3. **Generated files.** `gen-rust` (ops, contracts, manifest), `gen-builder` (Rust and C), and
   cbindgen's header must reproduce the committed files byte for byte.
4. **Proof audit.** `fir-audit` against the lock (below).
5. **`cargo fmt --check`** and **`cargo clippy --workspace --all-targets -D warnings`** with
   the workspace lints (below).
6. **Every Rust suite, debug and release**, with `FIR_REQUIRE_FULL=1` (a test that would skip
   for lack of the Lean reference, a native toolchain, or an emulator fails instead) and the
   fuzz counts set explicitly (200 programs, seed 1).
7. **The C API tests under AddressSanitizer.**
8. **Evidence.** Each suite writes what it actually did to `FIR_EVIDENCE`
   (`crates/fir/tests/common/evidence.rs`). The run fails if a required suite (21 of them, the ABI torture test included, and on Linux the C corpus, every one of whose `-O` builds must have been checked by the proved DCE checker) wrote
   nothing, recorded a skip or a failure, ran fewer programs than configured, compared fewer
   runs with `fir-ref` than it had run lines, or if any op constructor that a component claims
   to support was never exercised by that component's differential comparison. The coverage is
   reported at two levels: constructors (required: 106 of 106 for the interpreter, 61 of 61 for
   instruction selection) and kinds with modifiers (reported separately, out of 509 and 197). The
   threshold is "at least one comparison per claimed constructor": anything higher would be an
   arbitrary number, and anything lower would let a claim of support go untested.

   Coverage comes from `RunOutput::profile`, which counts actual interpreter dispatches, including
   a halting op but excluding unentered functions/regions and anything after UB, a trap, or the
   fuel limit. LFIR profiles count entered `aarch64.code` containers and reached instructions;
   synthesized returns and implicit yields are not source ops. Tests aggregate a profile only
   after that particular run agrees with `fir-ref` (the fixture suite also compares the profiled
   run with the CLI). For instruction selection, the profile is an **interpreter proxy for
   native execution**: the exact module compiled, including optimized or directly selected HFIR,
   on the same arguments, whose normalized result agrees with the native run. It is not a hardware
   trace. Address comparisons assembled from several layouts contribute no coverage unless one
   complete profiled run matches. Evidence records these counts under `executed ops`; the old
   static `ops_of` counter and `ops` field are gone, and the gate ignores static and zero counts.
   The baseline static counter reported 243 and 139 kinds before floats; executed coverage is now
   318 of 509 and 161 of 197 (all 106 and 61 claimed constructors, floats included). Counting is an array increment indexed by
   the kind's generated contract, so it stays on in every run (0.36 s for a 3M-iteration loop
   under `fir run`, against 0.42 s when it hashed the op's name). No constructor threshold has been relaxed.

Legitimate platform differences stay legitimate: a fixture whose functions the backend declares
it can't compile (holes, integers over 64 bits, non-64-bit data layouts, offsets the lowering
can't represent) is counted per reason, and any other compile failure fails the test.

## Interfaces

### Op contracts, generated from Lean (`fir::contract`)

The op declarations in `spec/Fir/Syntax.lean` already generate `OpKind` and the tables.
`lake exe gen-rust contracts` adds `compiler/ir/src/generated/contracts.rs`: `OpKind::contract()`,
an exhaustive match over every variant *and modifier* (no wildcard, so a kind the Lean name
table doesn't spell is a Rust compile error), and `KINDS`, one representative per op name.
Each `OpContract` carries the printed name, whether the kind calls (Lean's `callee?`), and its
dead code elimination permission: `Dce::Delete(Evidence::Proved(theorem))`,
`Dce::Delete(Evidence::Trusted(why))`, or `Dce::Keep`. `gen-rust manifest` writes the same with
the declarations as JSON. The generator refuses contradictions (a deletable kind that is a
terminator, calls, allocates stack memory, has no typing rule, or declares a write, alloc,
free, diverge, unwind, sync, or extern effect).

Passes read permissions from the contract instead of keeping lists: `dce` deletes a kind only if
`contract().dce.allows(policy)`, and `copyprop` stops at kinds whose contract says they call. The
policy (`fir::contract::Policy`) is `AllowTrusted` or `VerifiedOnly`; the repository's policy is
verified-only (`tests/contracts.rs` fails on any trusted permission unless
`FIR_ALLOW_TRUSTED=1`). No permission is trusted today; the variant exists so that new dialects
(floats) can ship an unproved permission that is visibly unproved.

Each Rust component that dispatches on kinds declares what it does with each, next to its code,
matching every variant with `clippy::wildcard_enum_match_arm` denied:
`fir::interp::support`, `fir::lower_support` (keep, expand, scalarize, scalarize or keep for
the `agg.*` ops that make and take apart the structs calls pass whole, lower exceptions, or
refuse, with what backs each), and `fir::backend::aarch64::isel::support`, which instruction
selection's own error path now uses. `tests/contracts.rs` checks them against the declarations
(an HFIR-only op the lowering doesn't rewrite, an op instruction selection claims outside MFIR,
an MFIR op it refuses, …), and the evidence check holds each claim of support to a differential
comparison that exercised it. A declaration is not a proof: matching declarations say nothing
about whether the Rust interpreter computes what Lean does. That is what the differential tests
and the checkers are for.

### Dead code elimination: proved permissions, a seam, and a proved checker

* `spec/Fir/DceKinds.lean` defines `PureKind k` (the kind's part of `Dce.Pure`: no call, no stack
  allocation, not a terminator, and `∀ loc res vs, ReadOnly (evalSimple loc k res vs)`) and the
  classification `dcePerm`, and proves `dcePerm_sound : ∀ k, dcePerm k = .delete → PureKind k`
  for every kind the pass deletes: constants, `poison`, `copy`, `select`, bitwise ops,
  comparisons, extensions, truncations, `int.add`/`sub`/`mul`, divisions, and shifts whose
  modifiers don't trap, `ptr.null`/`offset`/`field`/`index`, `ty.*`, `mem.global`, and the value
  building blocks including `union.get.ub` (a wrong variant is UB, so deleting it is allowed) but
  not `union.get.trap` (a trap is observable). Before, 27 of these kinds were "read off
  `evalSimple`" in a comment. `Pure.of_kind` turns `PureKind` into `Pure` for an op with no
  regions and variable operands; `dcePerm_erase` shows the classification reads only modifiers,
  which is what lets a table indexed by op names stand for every kind. `freeze_changes_core`
  proves that `freeze`, whose declaration lists no effects, changes the core: an empty effects
  list is not evidence of purity (`ptr.addr`, `ptr.with_addr`, and `func.addr` are in the same
  position).
* The pass never edits a body directly (`compiler/transforms/src/dce.rs`): `plan(&Body)` proposes a
  `Candidate` (ops to delete); `check(&mut Body, Candidate)` independently recounts reads and refuses
  any op the contract keeps under the policy, any op with regions or holes, duplicates, ops not
  in the body, and any deletion whose result a remaining op reads; only the `Accepted` value it
  returns (no other constructor) can be applied. `Accepted` holds that body's exclusive borrow,
  and `apply(Accepted, &mut Remarks)` consumes it without accepting a destination: it cannot be
  used on another body, after an intervening edit, or twice (compile-fail doctests cover all
  three, each differing by one line from a doctest that compiles, since stable rustdoc doesn't
  check the expected error codes; the allocation validator's approval is tested the same way). Dropping it cancels the edit. A refusal is a pass error with the reason
  (`PassError { rejected: true, .. }`), and the body is unchanged.
* `spec/Fir/DceCheck.lean` is a decidable checker over Lean programs, `checkFunc tgt src`, with
  `checkFunc_sound : checkFunc tgt src = true → src.Decided mod → tgt.Refines mod src`.
  `fir-ref check-dce SRC TGT` runs it and returns canonical source and target snapshots along
  with the function count. `tests/dce_check.rs` matches that receipt byte for byte to its
  immutably borrowed modules, including globals, external declarations and all functions; a
  bare success count or a receipt for different code/context is refused. The function's source
  file must also be unchanged. This is test evidence about those snapshots, not a compiler
  authorization or a proof of whole-module composition: `checkFunc_sound` remains conditional
  on `Decided`, with both functions interpreted in one fixed module. The tests run the Rust pass on every fixture
  and 200 random programs (and their MFIR lowerings), after the other passes so there is dead
  code, and has the proved checker accept each result: 944 functions with 13,672 deletions in the
  last run. So for these inputs the Rust pass's output is backed by a proof, whatever bugs the
  Rust pass or the Rust checker has; for other inputs, it is backed by the Rust checker, which
  states the same conditions (more strictly) but is not proved.

### Register allocation and frame lowering: a validator on the real output

`crates/fir/src/backend/aarch64/regcheck.rs`, `validate(input, output, shapes, nrets)`, runs on
every allocation in every build (`regalloc::allocate` returns its error; `compile` propagates
it). It is given the code before allocation and after rewriting, spilling, and frame lowering,
and nothing from the allocator. Its approval owns the output and exclusively borrows the input
and shares the ABI shapes; consuming `Accepted::apply()` commits exactly that output to that
input. The allocator rewrites a private proposal, so a refusal or cancelled approval leaves the
original untouched. Assignments remain untrusted proposals and are revalidated on every use;
malformed mappings are refused before rewriting. Function index, indirect-call signatures,
fixed frame metadata, and original instructions' source locations must stay unchanged.
Compile-fail and runtime adversarial tests cover these boundaries. A forward dataflow over the output tracks, for each location (the
31 registers, each spill slot, each save slot below `x29`), the set of input values it holds;
joins intersect. It walks each output block in step with the input block: every input
instruction must appear with the same opcode and immediates, physical registers unchanged and
virtual ones renamed, reading registers that hold the values the input reads; a 64-bit move the
rewriter left out makes its destination live wherever its source is (when the next output
instruction is also a move, both readings are tried, with a budget); the only insertions allowed
are spill loads and stores (directly from `sp`, or through `x16` computed as `sp` plus a constant),
saves and restores in aligned 8-byte slots below `x29`, and the frame allocation in place of
the prologue's placeholder (a realignment only as `mov x16, sp`, `and sp, x16, #-align`); the
exception pseudo-instructions clobber x16.
Calls clobber the caller-saved registers and read the argument registers; at each `ret` every
callee-saved register must hold its value at entry; the frame must cover the outgoing arguments,
the locals, every spill slot used, and the saves. `tests/regcheck.rs` refuses eleven
corruptions (two values in one register, a value across a call in `x9`, a missing save, a
dropped spill store, a reload from the wrong slot, an operand renamed wrong, an opcode or a
constant changed, a frame too small, an extra instruction, a retargeted branch), each for its
reason. The old `regalloc::check` (the assignment only, against the input; debug builds only)
remains as a second, weaker check; it is not described as validating spill code or frames.

### Narrow address exemptions in the AArch64 comparison

The interpreter can now make another address choice the semantics allows
(`fir::interp::Addresses::From(base)`, `run_detail_in`): allocations first-fit from `base`, and a
one-past-the-end pointer equal to the next allocation's start (the oracle may say either). The
AArch64 test reruns each comparable run under two such layouts (where qemu puts the stack and a
PIE heap). A native or LFIR result passes if it matches the reference or either layout's run, or
differs only at integer tokens whose values differ between those runs. The previous rule excused
every integer difference, and arithmetic traps, in any module that observes an address; under
it, `tests/aarch64/address-unrelated.fir` with a miscompiled multiply would pass. Now it fails
(mutation `miscompile-next-to-an-address`), and the fixtures that legitimately differ are
counted: 21 address tokens excused across 13 runs in the last full run, and one fixture
(`provenance.fir`'s `cmp_end`) that matches another layout exactly.

First fit packs allocations in one order under every base, so bits just above an allocation's
alignment could agree in every sampled layout by accident: track A's review found `s71-p534`
(`FIR_FUZZ_SEED=71`), a zero-size 8-aligned slot with bit 3 set in each layout, counted as a
difference when the native stack aligned it to 16, though the semantics only requires a multiple
of 8. The comparison now also runs each comparable run under `Addresses::Scatter` (two seeds,
each in two phases): every allocation is placed on its own, in a pseudo-random region, at an odd
multiple of its alignment in one phase and an even one in the other, so the lowest bit that moves
is the allocation's alignment, which the semantics forces, rather than a sample's agreement
(`review_forced_address_bits_come_from_alignment`).

### The proof audit (`fir-audit`)

`spec/Audit.lean` (its own executable: it imports `Lean`, which `Fir` avoids so `fir-ref` stays
small) loads the compiled environment and checks the claims registered in
`spec/Audit/Claims.lean`:

* each claim is a theorem; its transitive axioms (Lean's `collectAxioms`) are among `propext`,
  `Classical.choice`, and `Quot.sound`, plus any the claim approves with a reason (none do);
  `sorryAx` is never approved;
* no declaration in a `Fir` module is an `axiom` or uses `sorryAx` directly;
* every theorem in a `Fir` module with a bold headline docstring, or whose conclusion is one of
  `Func.Refines`, `Dce.PureKind`, `OpOut.Refines`, `Simulation`, `SimulationS`,
  `Behavior.Refines`, is registered as a claim or a supporting lemma (33 were unregistered when
  the audit was first run);
* a claim the Rust side relies on names a *binding*, a theorem in `Audit/Claims.lean` that writes
  the statement out and is proved by the claim; the audit requires the two statements to be the
  same expression (the bindings for `dcePerm_sound` and `checkFunc_sound` state exactly what
  `contracts.rs` and `fir-ref check-dce` cite);
* each claim's statement, hypothesis count, axioms, and the fingerprints of every `Fir`
  definition its statement depends on (through definitions, inductive types, and theorem
  statements, not proofs) must match `proofs.lock.json`. A difference is reported as *needing
  review*, with the old and new statements or the changed definitions, and `fir-audit --update`
  records the review. A fingerprint says that something changed, not that the new statement is
  still adequate; that judgment is the reviewer's.

### Rust and FFI lints

`fir` is `#![forbid(unsafe_code)]`. The workspace denies `unsafe_op_in_unsafe_fn`,
`clippy::undocumented_unsafe_blocks`, `clippy::missing_safety_doc`, and
`clippy::not_unsafe_ptr_arg_deref`. `fir-capi` no longer allows `missing_safety_doc` crate-wide:
each of its 134 unsafe exports has a `# Safety` section derived from its own pointer parameters (for
the 86 op exports, generated by `gen-builder capi`; the 48 others written from their
signatures, with the ownership-transferring ones, such as `fir_module_free` and `fir_func_end`,
saying what they free), the raw-pointer helpers (`with_module`, `with_builder`, `list`, `cstr`,
…) state their preconditions, and every unsafe block says which contract discharges it. Raw
pointers stay at that seam; the core is safe Rust. The C tests run in every verification, and
under AddressSanitizer in the full one. No noisy lint groups were enabled.

## Guarantees

| Link | Status | Backed by |
|---|---|---|
| Op declarations → Rust `OpKind`, tables, builders, C API, contracts | generated, checked fresh | gen-rust, gen-builder, cbindgen; `verify` compares bytes |
| DCE: which kinds may be deleted | **proved** | `Fir.Dce.dcePerm_sound` (+ `Pure.of_kind`, `dcePerm_erase`) |
| DCE: a deletion is a refinement | **proved** (per function, fixed module, `Decided` source) | `Fir.Dce.refines` |
| DCE: the checker that runs is the proved one, and relates functions name by name | **proved** | `Fir.Dce.checkFuncL_eq` (the counting checker `fir-ref check-dce` runs equals `checkFunc`), `Fir.Dce.checkModule_sound` (per name, over `Module.find?`; the function a call runs in a verified module, by reading) |
| DCE: the Rust pass's output on the tested inputs | **checked by a proved checker** | `Fir.Dce.checkModule_sound` via `fir-ref check-dce` in `tests/dce_check.rs`, on one `dce` step and on every step of the `-O` pipeline |
| DCE: the `-O` binaries the C corpus runs | **checked by a proved checker**, every step | `fcc -O --check-dce` in `fcc_corpus` (AArch64) and `fcc_x86_64_corpus` (x86-64, the programs it compiles); `verify full` requires every program's build checked ([dce.md](dce.md)) |
| DCE: the Rust pass's output on any input | checked (unproved checker) by default; **by the proved checker on request** | `passes::dce::check`, every run; with `fir compile`/`fcc`/`fir opt --check-dce FIR-REF` or `FIR_CHECK_DCE` (`backend::optimize`, `passes::reference`), every step of that run |
| DCE: the Rust checker's rules against the proved checker's | tested | `the_rust_and_lean_checkers_agree_on_random_candidates`; mutation `dce-checker-weaker-than-proved` ([layer-audit.md](layer-audit.md#3-the-dce-checker-lean-and-rust)) |
| DSE, forwarding, copy propagation | proved relations; Rust passes tested | `Fir.Dse/Fwd/CopyProp.refines`; `tests/opt.rs` |
| Composing passes, optimizing a whole module | **open** | intermediate programs' `Decided`ness and refinement over calls are not proved |
| HFIR lowering: expansion | proved (per function) | `Fir.Lower.Proof.Expand.refines`, `lowerFunc_refines` |
| HFIR lowering: scalarization, `cf.try`, the module | **open**; tested | `tests/lower.rs` against `fir-ref lower` and runs |
| Interpreter (Rust) vs Lean semantics | tested | `tests/run.rs`, `tests/fuzz.rs`, LFIR runs in `tests/aarch64.rs` |
| Instruction selection | tested | LFIR runs in both interpreters, native runs |
| What "LFIR refines MFIR" means | **not defined in Lean**: `Fir.AArch64Machine` has no behaviors or refinement; the tests' comparison is the only statement | `tests/aarch64.rs` ([layers-as-built.md](../design/layers-as-built.md#4-mfir--lfir-what-selection-and-allocation-keep-change-and-lose)) |
| Stack exhaustion | **not modeled as a limit**: HFIR and MFIR stacks are unbounded; the LFIR machine's is 1 MiB, and running past it is `ub out-of-bounds`; native code's is the OS's | none ([layers-as-built.md](../design/layers-as-built.md#6-gaps), G8) |
| C ABI: structs and arrays by value (AAPCS64) | registers carry a composite's defined bytes exactly: **proved** (`Fir.AArch64.roundTrip`, `pieces_flatten`); the classification against C: tested | `tests/abi.rs` (random signatures against GCC, both directions and `...`), `tests/capi/e2e.c`, native fixture runs |
| Register allocation and frame lowering | checked on every compile (unproved validator, ABI assumptions) | `regcheck::validate` |
| Assembly text and encoding | tested | native runs under qemu |
| Data layout at the backend | checked on every compile: AAPCS64's or refused | `isel::check_module` |
| Native addresses → source locations (`fir compile -g`) | tested | `tests/debug_lines.rs` |
| x86-64 backend: selection, allocation, assembly | tested; the allocation's assignment checked on every compile (unproved check; not the rewritten code) | native runs only (`tests/x86_64.rs`, `fcc_x86_64_corpus`): no LFIR dialect or semantics yet (decision: x86-64 target) |
| Effects and tiers in the op declarations | declared only | not read by anything that relies on them; `freeze_changes_core` shows one is incomplete |

**Trusted base** (beyond Lean's kernel and the three standard axioms): the Lean compiler that
builds `fir-ref` (the proved checker runs as compiled code); the text round trip (the Rust
printer's output parsed by the Lean parser, itself tested against `fir-ref fmt`; the receipt
shows they agree on each checked text, not that the text means what the in-memory module does);
that the `fir-ref` given to `--check-dce` is built from these proofs (`verify full` rebuilds it);
the Rust `check` and `erase_many` for compilations without `--check-dce`; the allocation validator's code and its ABI assumptions
(callees preserve `x19`–`x28`, `x29`, `sp`, and the caller's frame; program accesses never reach
the spill or save areas, which would be out of bounds and so UB); qemu, the cross toolchain, and
the assembler.

## Remaining obligations

1. **Prove the allocation validator** against `Fir.AArch64Machine`: acceptance implies that the
   output refines the input as LFIR programs. The validator is shaped for it (it reads only the
   two programs), but the proof needs a simulation between machines with different register
   files and a frame, and the ABI assumptions as hypotheses about callees.
2. **Make the proved DCE checker the default.** It now runs in the tests, in the C corpus's
   `-O` builds, and in any compilation that asks (`--check-dce`, `FIR_CHECK_DCE`); it is no longer quadratic
   (`checkFuncL`, proved equal to `checkFunc`, linear in size times nesting depth by construction: 0.7 s for one function of 128,000 ops, mostly
   parsing and printing). By default the compiler still runs only the Rust `check`, which a
   differential test holds to the same verdicts on random candidates but nothing proves equal,
   and which checks a candidate, not the output (`erase_many` is trusted). Running it by default
   needs Lean in process or in the toolchain. Also open for DCE: `Decided` (assumed) and
   composition (obligation 3). [dce.md](dce.md#next-steps-by-value-per-cost).
3. **Module composition and `Decided`.** Every pass theorem is about one function in a fixed
   module with a `Decided` source; optimizing every function of a module, and running passes in
   sequence, needs refinement to compose over calls and `Decided` to be preserved or replaced.
4. **Scalarization, `cf.try` lowering, and whole-module lowering** (decision: Lowering proofs).
5. **Effects.** The declared effects are unchecked and, for `freeze`, `ptr.addr`, `ptr.with_addr`,
   and `func.addr`, incomplete. Either prove them (an `effects` ⇒ property theorem per kind, like
   `dcePerm_sound`) or keep them out of every decision.
6. **Instruction selection rules** against ISA semantics, and the encoding.
7. **The audit's semantic fingerprints over-approximate**: changing an error message in the
   interpreter flags every claim whose semantics reaches it (mutation
   `changed-semantic-dependency`). That is noisy but safe; a finer dependency notion (only
   definitions that can affect the propositions) would need care to stay sound.

## Overhead and ergonomics

Measured on the development machine (x86-64 Linux, qemu-user for AArch64):

* **`cargo xtask verify full`: about 2 min 40 s** with Cargo's caches warm: 80 s rebuilding Lean
  from scratch, 2 s for the proof audit, about 40 s for each of the debug and release test runs
  (which include 200 random programs per fuzzing suite, the native runs under qemu, and about 400
  `fir-ref check-dce` calls), 1 s for the C tests under ASan. The verification before this work
  (`cargo test`, about 50 s, with Lean built by hand) checked less and could pass while skipping
  the reference, the native runs, or compilation failures.
* **Allocation validation runs on every compile.** On one thread it costs about 40 µs per
  function of 100 ops that spills (`cargo run --release --example bench_aarch64 synthetic:2000`),
  4.6 times the allocation itself, which is very cheap; it runs in the parallel allocation phase,
  which takes 9 ms of a 37.5 ms backend for 200,000 ops, where selection and assembly output
  dominate. It is not optimized; a reverse index from values to locations would remove most of
  its cost.
* **DCE's seam** adds one walk of the body to recount reads (the checker) per run. The proved
  checker runs in the tests (about 400 short `fir-ref` processes) and in the C corpus's `-O`
  builds; with `--check-dce` a compilation costs one `fir-ref` process per `dce` step that
  changed the module (about 15 ms per program on the corpus, nearly all process start and the
  text round trip).
* **The audit** takes 2 s. The lock changes whenever a definition a claim depends on changes,
  which for the interpreter is often: `lake exe fir-audit --update` after reading the diff of
  `proofs.lock.json` (statements are shown in full; dependencies as names with fingerprints).
* **New ops** now need a decision in three `support` functions (the compiler says where), a
  contract regeneration, and at least one differential comparison per claimed constructor.
  That is the intended friction: the float round's ops can't be half-integrated silently.
* **`cargo xtask mutate`** takes about 18 minutes (most mutations rebuild part of the Lean
  development and relink the generators); it is a periodic check of the checkers, not part of
  every verification.

## What the checkers found

No miscompilation surfaced: the proved DCE checker accepted every output of the Rust pass, and
the allocation validator accepted every real allocation. What they found were gaps in the
assurance itself, each of which let a defect pass silently:

1. **Untested claimed support.** Instruction selection has cases for `ptr.field` and
   `ptr.index`, but every pipeline lowers HFIR first, so no differential test ever reached them.
   The coverage check refused the first full verification for it. The AArch64 test now also
   compiles core-op HFIR without lowering (163 more native comparisons, all matching).
2. **Compile failures counted as skips.** The AArch64 test counted any failure to lower or
   compile as "not compiled" and passed. With allocation validation on, a refused allocation
   would have been silently skipped. Now only the backend's declared limits are skips.
3. **The address exemption excused unrelated miscompiles** in any module that observes an
   address (shown by `tests/aarch64/address-unrelated.fir` and mutation
   `miscompile-next-to-an-address`). One of the excused cases (`provenance.fir`'s `cmp_end`) was
   in fact another legal behavior, now matched exactly.
4. **Unproved purity.** 27 of DCE's 30 deletable constructors were justified by reading
   `evalSimple`; they are now proved, and the proof found nothing wrong with the old list.
5. **Declared effects are incomplete**: `freeze` (proved), `ptr.addr`, `ptr.with_addr`, and
   `func.addr` declare no effects but change the core. Nothing relies on effects today; anything
   that starts to would be wrong.
6. **33 assurance theorems were unregistered** (no report existed), and the allocation check ran
   only in debug builds, on the assignment rather than the code.
7. **The audit's own bug**, found by `cargo xtask mutate`: in Lean 4.35 `ConstantInfo.value?` is
   `none` for theorems, so the first version's scan for `sorry` never looked at a proof (claims
   were still covered by `collectAxioms`). Five of the harness's own mutations were also wrong
   on the first run (a malformed op declaration, a docstring split, too-loose expectations); the
   harness reported each as "setup failed" or "caught for another reason", not as a pass.

## Landing on main with the float round

Main gained floats (`f32`/`f64` through Lean, both interpreters, the passes, and AArch64 with a
second register class), the `fcc` C frontend, and its own fix for the address exemption (a
taint analysis) while this work was under way. Merging them exercised the checks on new code:

* The ops' contracts made the 20 new float op kinds compile errors in exactly the three `support`
  declarations until each was decided; DCE's permissions for the float ops are proved
  (`dcePerm` defers to main's `Dce.floatPure`, and `dcePerm_sound` uses main's
  `readOnly_evalFloat`); the audit refused 20 unregistered float theorems until they were
  registered (19 claims, one supporting lemma), and asked for review of every claim whose
  semantics the float work changed (only `Simulation.refines`' statement changed: the oracle is
  now a structure that also picks NaNs).
* The lint policy refused main's six new C API exports and a test's inline assembly until each
  had its safety contract or justification.
* The allocation validator was extended to the float register class (`d0`…`d31`, float spill and
  scratch registers, `d8`…`d15` as callee-saved, `fmov` between virtual registers left out). The
  C frontend's corpus then found a false rejection (`newton.c`: a left-out float move before an
  `fmov d1, xzr`), fixed by considering every later input instruction a left-out move could
  stand for. A corrupted assignment claiming `u32::MAX` spill slots made main's home check try to
  allocate 68 GB; slots are now bounded by the virtual registers first.
* The direct-HFIR native builds found an instruction-selection bug: a `mem.load` of a struct,
  a core op over an HFIR value, was selected as one wide integer (`lsl x0, x0, #64`, which doesn't
  assemble). Selection refuses aggregate, union, and slice values now (`aggregate_values_need_lowering`).
* The release test run found that main's `float::tests::sqrt_agrees_with_the_host` fails in
  release builds (it passes in debug): the host-side NaN check was optimized into one that missed
  the NaN of a negative square root. The test reads the NaN off the bits behind a barrier now; the
  interpreter's result was right.
* The address exemption is now main's taint analysis composed with the layouts: a difference must
  be in a tainted outcome, and a tainted integer that another legal address layout moves must stay
  within the bits the layouts moved (review finding 5 applied to main's rule, which accepted any
  number in a tainted position).

Main's varargs round (`va.start`, `va.arg`, `va.end`, variadic functions) followed:

* The three new op kinds were compile errors in the `support` declarations until decided; the
  Lean `Pure` predicate now excludes `va.start`, so `PureKind` and the proved DCE permissions
  carry that condition, and the proved DCE checker compares the functions' variadic flags (the
  refinement theorem needs them equal). The audit asked for review of the pass theorems that
  gained `tgt.variadic = src.variadic`.
* The lint policy refused the four new C API exports until each had its safety contract.
* The random native programs found a false rejection by the allocation validator: in a variadic
  function, an input `mov v34, v30` between two spilled registers (done by the spill code alone)
  was matched to the output move of the next, kept, `mov v35, v30`. The validator then forgot
  that `v34`'s slot held its value, and the error surfaced only in a later block, past the
  block-local backtracking. A kept input move now records that every location holding its source
  holds its destination too (true after any move), so either alignment leaves the same facts.
  `builder_rebuilds_backend_lfir`'s program 21 is the regression test.

## What an independent review found

A Codex review (GPT-6.1 Sol) of this branch at `326b0d4` reported eight defects, each with a
reproduction; all are fixed, and the reproductions run as regression tests
(`crates/fir/tests/review_regcheck.rs`, and tests in `tests/aarch64.rs` and `xtask`):

1. **Full verification accepted stale evidence**: the AddressSanitizer phase didn't clear its
   evidence directory, so with an inherited test runner that skipped the ASan tests, last run's
   files passed. Every phase now starts from an empty directory, evidence carries the run's id
   and evidence from another run is refused, inherited test runners are cleared, and a log with
   filtered-out tests fails the check.
2. **The allocation validator accepted `and sp, x16, #-16` without x16 holding `sp`**, which moves
   `sp` anywhere. Realignment is now accepted only as `mov x16, sp` then `and sp, x16, #-align`
   with the function's alignment.
3. **It accepted overlapping save slots** (`[x29, #-8]` and `[x29, #-9]`), which corrupt a
   callee-saved register (shown under qemu). Save slots must be aligned 8-byte slots below `x29`.
4. **It didn't know that the exception pseudo-instructions clobber x16** when emitted, so a spill
   address in x16 survived them; natively the "spill" overwrote the exception flag. They now
   clobber x16 in the validator's model, and can't take x16 as an operand.
5. **The address comparison treated a moving integer as any number**: `addr & 255` could come out
   as 256. An excused integer may now differ only within the span of bits that moved between
   legal layouts (whose bases are bitwise complements, so that span is the real one). This
   narrower rule then showed that pre-allocation LFIR didn't realign `sp` for over-aligned
   locals; instruction selection now does.
6. **The validator refused valid frames of 16 MiB or more** (a false rejection).
7. **The audit skipped private theorems** when looking for unregistered ones.
8. **A mutation had silently stopped running** after the contracts gained a field; every
   mutation's anchor is now checked by a test.

The reviewer found no counterexample in DCE's permissions and checker, the approval bindings,
the generated contracts and support declarations, execution profiling, or the audit's axiom
collection and fingerprints.

## Recommendation

The architecture improves AI-assisted development where it turns a claim into something a
machine refuses when false, and the experiment found real gaps that way within hours. In order
of value per cost:

1. **Adopt `cargo xtask verify full` with evidence.** It is the piece that caught the most: an
   untested backend path, a silent-skip path, and the possibility of passing with the reference
   or the emulator missing. An agent can't declare success on a run that skipped work. Cheap to
   keep: the suites only append counts.
2. **Adopt the narrowed address comparison.** Small code, removes a real blind spot in the
   strongest end-to-end test, and the alternative layouts are legitimate behaviors of the
   semantics rather than a tolerance.
3. **Adopt generated contracts with exhaustive `support` declarations** for optimization
   permissions and component support. They make a new op (the float round's) a compile error in
   exactly the places that must decide, and keep permissions in the language where they are
   proved. Keep the manifest small; it is a report, not a second source of truth.
4. **Adopt checked transformation seams where a proved checker exists or is planned** (DCE now;
   the allocation validator as the next proof target). The plan/check/apply shape costs little
   and keeps passes from mutating around validation. Running the proved checker in the tests
   and the C corpus's builds gives proof-backed results there today (`--check-dce` gives them
   for any compilation that asks); running it in process, by default, is the
   step that would make it hold for every input.
5. **Adopt the proof audit, with care about churn.** Rejecting `sorry`, custom axioms, and
   unregistered theorems is high value and quiet. The dependency fingerprints are noisy (any
   interpreter change asks for review of every claim); keep them, but expect `--update` to be
   routine and review the statement diffs, which are the part that matters.
6. **Keep `cargo xtask mutate` as a periodic check** (18 minutes), not a gate. Its value was
   finding the audit's bug and keeping the checkers honest; its mutations need maintenance when
   code moves (anchors must exist, or the mutation reports itself broken).

What does not merit adoption as is: the evidence's op counts at modifier level as a gate (243 of
401 kinds; a gate there would be an arbitrary threshold), and treating the declared `effects` as
anything but documentation until they are proved.
