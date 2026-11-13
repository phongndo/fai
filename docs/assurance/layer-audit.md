# Layer audit: HFIR → MFIR → LFIR, one slice through them, and one Lean–Rust gap

An audit of the layer boundaries at `046a67d`, with the work it led to. Five questions:

1. What each boundary supports, checks, loses, and leaves unclear, exposed with real programs.
2. Whether one small program survives every layer, executed and compared with a reference.
3. Whether the proved DCE checker can check what the Rust pass really produces, and whether the
   Rust checker the compiler runs implements the same rules: cost, and what the proof covers.
4. What exists for observing an experiment (IR before and after a pass, correctness, timing),
   and what was missing.
5. Which information to preserve for a concrete use, and a recovery rule that is tested.

Every number here was measured on the development machine (x86-64 Linux, qemu-user for
AArch64) and can be reproduced with the commands given.

## 1. The boundaries

### HFIR → MFIR (`fir lower`)

- **Supports.** HFIR: every op, the building blocks included (`agg`, `union`, `slice`,
  `int.*.overflow`, `cf.try`, `ptr.field`/`ptr.index`), values of any type but function types and
  `va_list`. MFIR: the core ops, `func.invoke`, and still `agg.make`/`extract`/`insert` with
  composite values (`verify.rs:345-352`); memory is accessed by scalars only. Per op the
  lowering keeps, expands (overflow, `ptr.field`, `ptr.index`), scalarizes (`union`, `slice`,
  `agg`), or lowers (`cf.try`) (`lower::support`, `lower.rs:35-148`).
- **Checked on every run:** the input verifies (callers), the output verifies as MFIR
  (`lower_checked`). **In the tests only:** Rust's lowering equals Lean's `lowerModule` byte for
  byte (`tests/lower.rs`, `tests/fuzz.rs`), and runs of the lowering refine runs of the source.
  **Proved:** the expansion step only (`Lower.Proof.Expand.refines`, `lowerFunc_refines`, for a
  `Decided` source without holes or temporary-looking names). Scalarization, `cf.try` lowering,
  and the whole module are open.
- **Lost:** field identity (`ptr.field … %a, 1` becomes `ptr.offset.inbounds %a, 4`); index
  types (`ptr.index` becomes `i128` arithmetic); `inbounds` and the padding bytes of aggregate
  loads and stores, which become one `ptr.offset.wrap` access per field with alignment narrowed;
  FIR unions, which become a tag plus every variant (signatures change arity: `@get(%u)` becomes
  `@get(%u.0, %u.1, %u.2)`); which `cf.blocks` was a `cf.try`. Kept: locations (all ops but the
  extracts that take struct parameters apart, which have no source op), names, facts on scalars,
  UB modifiers.
- **Unclear:** the same op is typed differently by layer (a composite `cf.if` verifies in MFIR,
  and no backend takes it); Lean scalarizes, lowers exceptions, then expands, while Rust fuses
  scalarizing and expanding and lowers exceptions after, which only text equality on the tested
  inputs relates.

### MFIR → LFIR (instruction selection, allocation, emission)

- **Supports.** Every MFIR op, `agg.*`, and `ptr.field`/`ptr.index` (`isel::support`); integers
  over 64 bits only in ops whose low 64 bits depend only on the operands' low 64 bits; composites
  only in `agg.*`, copies, calls, returns, and `va.arg`; on macOS no variadics and no
  stack-passed composites.
- **Checked on every run:** 64-bit pointers and addresses, and (new, see below) the rest of the
  data layout; the allocation validator (`regcheck::validate`, unproved, with ABI assumptions).
  **In the tests only:** selection, by running LFIR in both interpreters and natively; the LFIR
  verifier (`fir compile` never verifies the LFIR it emits). **Proved:** that registers carry a
  composite's defined bytes exactly (`Fir.AArch64.roundTrip`). No Lean or SMT selection.
- **Lost:** names, SSA, and types (virtual registers); UB modifiers and per-allocation bounds (an
  out-of-bounds stack read is `ub out-of-bounds` in HFIR and MFIR and returns the neighbour's
  `99` in LFIR, a legal refinement); every fact (`facts.fir`'s `@percent 200` is `ub fact` in
  HFIR and returns 200 in LFIR); alignment; provenance in the assembly; source locations in the
  assembly (fixed, section 5).
- **Unclear:** `ptr.field`/`ptr.index` are implemented twice (`lower.rs` and `isel.rs`) with
  nothing relating them; `poison`/`freeze` are sound only because each value is computed into one
  register once; the Apple ABI's extension of narrow arguments isn't done (not confirmed: no Mac).

### Gaps the audit exposed

| | Gap | Status |
|---|---|---|
| G1 | A 64-bit layout with `int … 64:4` compiled a struct passed to C with its `i64` where C doesn't look: the C callee saw `b=0` for `2` (confirmed natively) | **fixed**: the backend refuses any layout but AAPCS64's (`isel::check_module`; `layer_audit_foreign_data_layouts_are_refused`) |
| G2 | With `valist 8:8`, `va.start` wrote AAPCS64's 32 bytes into an 8-byte `va_list`, over the frame: 42 in HFIR and MFIR, `stuck: @first doesn't preserve x29` in LFIR, a segfault natively; the allocation validator's assumption (program accesses never reach the save area) hid it | **fixed**, same check |
| G3 | An MFIR `cf.if` yielding a struct passes both verifiers, then selection refuses it with "HFIR only: lower the module to MFIR first" though it is MFIR | open: MFIR has no written legality contract per target |
| G4 | `int.add.overflow.s` on `i64` lowers to `i65` ops that verify, then selection refuses them | open |
| G5 | A source value named like a lowering temporary (`%.e0`) makes the lowering fail to verify (Rust and Lean alike) | open (refused, not miscompiled) |
| G6 | Facts are dropped by selection, so `check` facts never become checks | open; the design says they become instructions |
| G7 | `tests/lower.rs` skips runs whose arguments don't parse at both layers, so functions whose signatures scalarization changes are never compared there | open |
| — | `docs/design/01-layers.md` describes the target (proved lowering, SMT-checked selection, a proved allocation checker, scheduling, MFIR without building blocks), not what exists | a note there now points to `README.md#guarantees`, which is accurate |

The real programs (`unions`, `struct_calls`, `switches`, `float_aggregates`, `linked_list`,
`goto` from `frontends/c/tests`) found none of these: their Rust and Lean lowerings are
byte-identical, every layer verifies in both tools, and every run agrees across layers,
interpreters, and the native binary. The gaps came from hand-written edge cases.

## 2. A vertical slice

A struct accumulator updated in a counted loop through a `switch` with fall-through and a
default, signed arithmetic, and a call:

```c
struct acc { int sum; int count; };
static int classify(int x) {
  switch (x & 3) { case 0: return 1; case 1: x += 10; /* falls through */ case 2: return x;
                   default: return -x; }
}
long slice(int n) {
  struct acc a = {0, 0};
  for (int i = -n; i < n; i++) { a.sum += classify(i); a.count++; }
  return (long)a.sum * 3 + a.count;
}
```

```sh
fai-cc slice.c --emit hfir -o slice.hfir
fir lower slice.hfir > slice.mfir
fir opt slice.mfir -O > slice.mfir-O
fir compile slice.mfir-O --emit lfir-vregs -o slice.lfir-vregs
fir compile slice.mfir-O --emit lfir -o slice.lfir
fir run slice.LAYER @slice N; fir-ref run slice.LAYER @slice N      # each layer, both interpreters
fai-cc slice.c [-O] -o slice.o && cc slice.o harness.c && qemu-aarch64 ./a.out
aarch64-unknown-linux-gnu-cc -O1 slice.c harness.c && qemu-aarch64 ./a.out   # the reference
```

For `n` in 0, 1, 2, 3, 7, 100, 1000 the results (0, 8, 37, 66, 140, 1550, 15500) agree at all
eight points: GCC, `fai-cc` with and without `-O` natively, and HFIR, MFIR, MFIR after `-O`, and
LFIR before and after allocation in `fir run` (and in `fir-ref run`, which runs LFIR on
`Fir.AArch64Machine`). The design works as a system on it. What the slice showed besides:

- **The optimizer has almost nothing to do on C.** `-O` made one change in the whole module (a
  load forwarded from the store before it). `fai-cc` keeps every local in memory, and the passes
  match only adjacent accesses, so the loop loads and stores `i`, `a.sum`, and `a.count` every
  iteration. Promotion of non-escaping slots (mem2reg/SROA) is the missing piece, in the frontend
  or as an MFIR pass.
- **Locations reach LFIR but not the assembly** (73–89% of LFIR instructions carry one): see
  section 5.
- **Each lowering step is visible and small**: `ptr.field.inbounds struct<C>{i32, i32} %a, 1`
  becomes `%.e1: i64 = int.const 4; ptr.offset.inbounds %a, %.e1`, and selection then
  materializes the constant (`movz x0, 4; add x0, x20, x0`) instead of folding it.

The slice is now a permanent check for the whole corpus: `tests/fai_cc.rs` runs every program's
`main` not only in HFIR but at MFIR, MFIR after `-O`, and LFIR before and after allocation, under
Arm's NaN rule (the canonical-NaN rule `fir run` uses by default gives other, equally legal,
NaN payloads than the LFIR machine, which `float_arith` shows). All 57 comparable programs match
the native output at every layer; the other 10 call `printf` or C helpers whose results the
interpreter's world doesn't model. The corpus test takes 23 s.

## 3. The DCE checker: Lean and Rust

### What exists, checked rather than assumed

- `Fir.Dce.checkFunc tgt src` is proved: `checkFunc_sound : checkFunc tgt src = true →
  src.Decided mod → tgt.Refines mod src`. `fir-ref check-dce SRC TGT` runs it, compiled by Lean.
- The compiler runs a different checker, `passes::dce::check`, on a *candidate* (ops to delete)
  before `apply` deletes them. Nothing proves it equal to the Lean one.
- Before this work, the proved checker ran only in `tests/dce_check.rs`, on the output of one
  configuration (`fwd,copyprop,dse` then one `dce`), over the fixtures and 200 random programs:
  never on the C corpus and never on the `-O` pipeline as the compiler runs it (to a fixed point).

### Can the proved checker check real outputs? Yes

`fir opt FILE -O --check-dce FIR-REF` now runs the proved checker on every `dce` step of the real
pipeline (`fir::passes::reference::CheckDce`, an observer of the pipeline), and matches its
receipt, both modules as Lean parsed and printed them, to the modules submitted. A step is
skipped only if the module's printed text is unchanged, not on the pass's own count of zero
deletions (a review found that a `dce` changing the module while reporting zero went unchecked;
`check_dce_checks_steps_that_report_no_changes_but_change_the_module` covers it).

| Input | DCE steps checked | Function pairs | Deletions | Refused |
|---|---|---|---|---|
| C corpus, 67 programs (`fai-cc --emit mfir`, then `-O`) | 71 | 1,055 | 3,462 | 0 |
| Fixtures and 200 random programs (and their lowerings), `-O`, in `tests/dce_check.rs` | 344 | — | 14,759 | 0 |

**Cost.** On the C corpus, `-O` takes 1.4 ms per module; with `--check-dce`, about 20 ms (95 ms
against 1,355 ms for all 67), almost all of it starting `fir-ref` and printing and parsing the
modules. It grows quadratically with the size of a function, because `deletable` scans the rest
of the region for readers of each deleted op (`opsReads`):

| One function of | DCE in Rust | `fir-ref check-dce` |
|---|---|---|
| 2,000 ops (1,000 deleted) | 0.1 ms | 16 ms |
| 8,000 ops | 0.4 ms | 91 ms |
| 32,000 ops | 1.5 ms | 1.0 s |
| 128,000 ops | 6.6 ms | 20.9 s |

Fine as an opt-in and in CI over a corpus; not as an always-on check until the checker computes
the set of read names once per region (a one-pass variant proved equal to `deletable`).

### Does the Rust checker implement the same rules? Here is how far that is established

By construction and by reading:

| Rule | Rust `dce::check` (compiler) | Lean `checkFunc` (proved) |
|---|---|---|
| The kind may be deleted | `contract().dce.allows(policy)`: the contract is generated from Lean's `dcePerm`, and `verify` checks it is fresh | `dcePerm k == .delete` |
| No regions; operands are variables | checked | checked |
| No remaining op reads a result | by value ids, anywhere in the body | by names, in the rest of the region in the target, at any depth (the same in SSA) |
| The output is the source minus the deletions | **not checked**: `apply` calls `erase_many`, which is trusted | checked op by op: kind, results, operands, location, region parameters, labels |
| Parameters, results, variadicity, everything outside functions, the source file | unchanged by construction | checked |
| Under `Policy::AllowTrusted` | deletes kinds with a trusted permission | refuses them (there are none today, and the policy is verified-only) |

Empirically, **`the_rust_and_lean_checkers_agree_on_random_candidates`** (new, in
`tests/dce_check.rs`, required by `verify full`) gives both checkers the same candidates:
each kind of unread op the plan leaves (calls, loads, `freeze`, trapping arithmetic,
terminators) deleted alone, once per function, and random mixes from the plan, those ops, and any
op. A Rust acceptance the proved checker refuses, or the reverse, fails the test.

| Run | Both accepted | Both refused | Rust refused, target doesn't verify | Disagreements |
|---|---|---|---|---|
| Default (fixtures + 50 programs), 1 s | 78 | 1,761 | 2,640 | 0 |
| `FIR_FUZZ=4000` (fixtures + 1,000 programs), 13.6 s | 1,045 | 23,274 | 13,984 | 0 |

Planted weakenings of the Rust checker alone (the planner left correct, so no pass output shows
them) are caught at the default size: letting `freeze` go (19 disagreements), `func.call` (89),
`mem.load` (141). The first is now `cargo xtask mutate dce-checker-weaker-than-proved`. Before
this test the same defect passed every suite: the existing mutation `dce-checker-also-wrong`
needs the planner to be wrong too.

### What the proof covers, exactly

For one `dce` step checked by `--check-dce` or the tests: each function of the target refines the
same function of the source, **in the source module** (calls go to the source's callees), for
every argument, oracle, and monotone world, **if** the source function is `Decided` (no run reaches
a choice the reference semantics leaves open, such as an address that may belong to two
allocations). It does not cover:

- `Decided`, which nothing checks (C programs that turn integers into pointers are the likely
  place to lose it);
- composing the per-function results into the optimized module, whose other functions changed
  too, or composing steps across passes (`Func.Refines.trans` composes steps of one function in a
  fixed module);
- the other passes (`fwd`, `copyprop`, `dse` have proved relations but no checker of outputs);
- compilations without `--check-dce` (the compiler runs the unproved Rust checker; `fai-cc -O`
  and `fir compile -O` never run the proved one);
- the trusted base: Lean's compiler (`fir-ref` runs as compiled code), the Rust printer and the
  Lean parser (the receipt shows they agree on these modules, not that the Rust in-memory module
  is what was printed), and `erase_many`.

### Options for closing the gap, by cost

1. **Run the proved checker in CI over a corpus** (done for the tests; the C corpus run is
   `fir opt … --check-dce`): cheap, covers the configurations tested.
2. **A linear checker in Lean**, proved equal to `deletable`: needed before anything always-on.
3. **Call it in process** (Lean's C output linked into `fir` behind `@[export]`): removes the
   process and the files, not the text round trip; adds Lean's runtime to the binary.
4. **Port `checkOps` to Rust as an output checker** and keep the agreement test: always-on and
   linear, still unproved, but it would check the output rather than trust `erase_many`.

## 4. Making experiments observable

**Already there:** `fir lower`; `fir opt --passes P,… --remarks --stats --verify-each`;
`fir compile --emit mfir|lfir-vregs|lfir|asm`; `fir run` at every layer (LFIR on the AArch64
machine); `fir-ref run|lower|check-dce`; `tests/opt.rs` (every fixture and random program, each
run of the optimized module must refine the original's); `examples/bench.rs` (parse, verify,
print), `bench_aarch64.rs` (the backend), `build_bench.rs` (the builder).

**Added:**

- Every pass carries its assurance, `Proved("Fir.Dse.refines")` or `Experimental(why)`;
  `fir opt --list-passes` prints them. Experimental passes run only with `fir opt
  --experimental` (or `Pipeline::parse_experimental`), print a warning, and can't be in `-O`
  (a unit test checks the default pipeline). None exists yet; the gate is ready for the first.
- `Pipeline::run_observed` shows an observer the module before and after every pass run, and
  lets it reject a step. `fir opt` uses it for `--print-before P`, `--print-after P` (`all`
  for every pass), `--print-changed`, and `--dump-dir DIR` (numbered files to diff:
  `000-input.fir`, `001-r1-fwd.fir`, …), and for `--check-dce`.
- `FIR_PASSES=p,q cargo test -p fir --test opt` runs the whole differential suite on that
  pipeline instead of `-O` (experimental passes allowed); `verify full` clears it.
- `-` reads standard input, so `fir opt F -O --check-dce R | fir compile - -g -o prog` checks
  exactly what is compiled.

A pass experiment, end to end:

```sh
fai-cc prog.c --emit hfir -o prog.hfir && fir lower prog.hfir > prog.mfir
fir opt prog.mfir --passes fwd,dce --print-changed --stats --check-dce spec/.lake/build/bin/fir-ref > prog.opt
fir run prog.mfir; fir run prog.opt                         # same outcome, or a refinement
FIR_PASSES=fwd,dce cargo test -p fir --test opt             # correctness on every fixture and random program
fir compile prog.opt -g -o prog && qemu-aarch64 ./prog       # natively, with source lines
```

## 5. Raising selectively

No general reconstruction is attempted: after lowering, field identity, union structure, and
`cf.try` are gone or ambiguous (offset 0 is a struct and its first field; a union's variants
overlap), and LFIR keeps no names or types.

**The use chosen:** attributing native code back to the source and to FIR ops. A native crash
(G2's segfault), a qemu trace, or a profile of a pass experiment gives addresses; the LFIR
carried each instruction's location, and the emitter dropped it.

**What is preserved:** `fir compile -g` (`Options::debug_lines`) writes `.file` for each
function's source file and `.loc FILE LINE COL` before each instruction whose location differs
from the last. Instructions no op accounts for (prologues, epilogues, spill code, the trap stub)
go to a synthetic file, `<fir: no source>`, line 1, as do functions without a source file and
FIR locations on line 0. DWARF's own "no source" (line 0) is dropped by GNU as 2.46, which
would leave an epilogue attributed to the op before it; LLVM's assembler keeps it.

**The recovery rule:** a machine address recovers the `line:col` of the FIR ops its instruction
was selected for, a set (ops share locations), or no source. `tests/debug_lines.rs` compiles every
fixture with and without `-O`, assembles it with the AArch64 C compiler, reads the line table
with `llvm-dwarfdump`, and requires:

- **fidelity:** every instruction has a row, and it is the location the emitter attached to it
  (this caught the GNU line-0 behavior: with line 0, all 100 modules fail);
- **soundness:** every recovered location is in the file of the function containing the address,
  read from the object's own DWARF file table, and is the location of an op of that function in
  the module before lowering.

A review found three cases the fixtures lacked, now in
`line_zero_escaped_file_names_and_modules_without_files`: an op on line 0 (it inherited the
previous line), a module with no source files (it got no line table), and a file name needing
escapes (the test had read names off the assembly, undecoded).

On the fixtures, 1,678 of 16,742 instructions have a location (most fixtures have none); with
`FIR_DEBUG_LINES_DIR` pointing at the C corpus's HFIR, 163,304 of 206,878 (79%), all faithful
and sound.

**Next candidate, not built:** recovering field paths in MFIR (`ptr.offset.inbounds %slot, k`
over a `mem.stack.of T` slot, with an access of type `S`, recovers the leaf fields of `T` at
offset `k` of type `S`, a set). Its use would be a promotion pass for the starved optimizer of
section 2; it waits for that pass, since a recovery rule without a consumer has nothing to be
right about.

## Files

- `crates/fir/src/passes/mod.rs`: `Assurance`, `Observer`, `run_observed`,
  `parse_experimental`; `passes/reference.rs`: `CheckDce`.
- `crates/fir/src/bin/fir.rs`: `fir opt` observation flags, `--list-passes`, `--check-dce`,
  `fir compile -g`, `-` for standard input.
- `crates/fir/src/backend/aarch64/isel.rs`: the data layout check (G1, G2);
  `emit.rs`: line info.
- Tests: `tests/dce_check.rs` (the `-O` pipeline, the agreement test), `tests/debug_lines.rs`,
  `tests/aarch64.rs` (`layer_audit_foreign_data_layouts_are_refused`), `tests/opt.rs`
  (`FIR_PASSES`), `fir-capi/tests/fai_cc.rs` (every layer).
- `xtask`: `dce_agreement` and `debug_lines` evidence required; the mutation
  `dce-checker-weaker-than-proved`; `FIR_PASSES` and `FIR_DEBUG_LINES_DIR` cleared.
