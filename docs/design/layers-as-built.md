# The layers as built: what HFIR, MFIR, and LFIR mean today

[01-layers.md](01-layers.md) describes the layers FIR is aiming for. This file describes what the
code implements, read from the Lean spec (`spec/Fir`), the Rust implementation (`crates/fir`),
and the tests, as of `1ac29a2`. Each claim names where it comes from. What is proved, checked, or
only tested is in [the assurance report](../assurance/README.md#guarantees); the measured audit
of the boundaries is [layer-audit.md](../assurance/layer-audit.md).

In short: HFIR and MFIR are two subsets of one language with one semantics. LFIR is a different
language that runs on a different machine over the same memory, events, and outcomes. Lean
defines refinement for the first machine only, so "LFIR implements MFIR" is defined only by the
test harness that compares them.

## 1. One semantics, two machines

**What a function means.** `Behaves world mod f args b` (`Fir.Behavior`): calling `f` can produce
behavior `b`. A behavior is a trace of events, each a call to an external function with its
arguments and results, plus how the run ended: `ret`, `threw`, `trap R`, `ub K`, `diverge`,
`hole`, `stuck`, or `ambiguous`. A run with infinitely many events has no ending. Two sources
fill in what a module doesn't decide:

- the **oracle** (`Oracle`) answers every free choice: what `freeze` of `poison` gives,
  allocation ids, tags, and addresses, whether an allocation fails, one-past-the-end
  comparisons, and NaN results (keyed by op and operands, decision: NaN choice);
- the **world** (`World`) answers each external call. It can do only what the external
  function's declared effects allow (`Answer.valid`); an answer outside them is replaced by zeros.
  So an extern's effect list is part of the program's meaning, and a native callee that exceeds
  it breaks the contract unnoticed.

`fir run` and `fir-ref run` use the oracle and the world that always answer 0 (canonical NaNs,
first-fit addresses from `0x1000`, externs that return zeros and change nothing).

**What correct means.** `Func.Refines mod tgt src`: for every monotone world and all arguments
(`poison` included), every behavior of `tgt` refines some behavior of `src`. Refinement
(`Fir.Refinement`) allows anything where the source is UB or stuck, any value where the source
has `poison`, and any byte where the source byte is `poison` or a `va_list` cursor. Traps must
keep their reason, and events must match: same callee, arguments that refine, the same results.
An `ambiguous` run (an address that fits several exposed allocation-and-tag candidates, where
the choice matters: two allocations, or two tags of one that an active `noalias` or `readonly`
scope tells apart) refines only a UB or stuck source, and nothing refines it, so refinement
isn't reflexive on it. Every refinement theorem therefore assumes the source is `Decided`: no
run of it ends `ambiguous`.

**Which machine runs what.**

| Modules | Machine | Behaviors and refinement defined in Lean |
|---|---|---|
| HFIR and MFIR | `Fir.Interp` (Rust: `interp.rs`). It never reads the module's layer: an op means the same in both. | Yes: `Behaves`, `Func.Refines`, `Func.Decided` |
| LFIR for AArch64 | `Fir.AArch64Machine` (Rust: `compiler/interp/src/aarch64_machine.rs`): registers and flags over `Fir.Interp`'s core (memory, allocations, events, oracle), ending in the same `Outcome` | No: the machine has `step` and `run` (a printed outcome), and no `Behaves` or refinement against a source |

**The rest of the meaning:**

- **The data layout.** A module's `memspace` line (pointer and address size, pointer and integer
  alignments, the `va_list` size) determines sizes, offsets, `struct<C>` layout, and the width of
  `ptr.addr` at every layer (decision: Data layout). It is chosen in HFIR, and nothing later
  changes it (`Fir.Space`). The AArch64 backend accepts only the default layout, which is
  AAPCS64's (`isel::check_module`). So HFIR is not hardware-neutral: a frontend has to pick its
  target's layout when it writes HFIR.
- **Byte order:** little-endian (decision: Byte order). **Floats:** round to nearest, ties to
  even; no flags, no rounding modes (`Fir.Float`). The result doesn't depend on the host's FP
  environment (`tests/float_env.rs`).
- **Facts.** `assume`, `check`, and `proved` all mean the same thing: a violated fact is UB, and
  `poison` passes (`Fir.Trust`, `checkResults`). Nothing in the compiler reads the trust level.
  No pass relies on a fact, `check` facts never become checks, and nothing upgrades a fact to
  `proved`. Facts survive lowering and are dropped by instruction selection.
- **Stack size.** In HFIR and MFIR it is unbounded. `mem.stack` never fails, and calls nest
  without limit; only running out of addresses is UB (`addressSpace`, when an address is first
  observed). The LFIR machine's stack is bounded. See G8.

## 2. Each layer

The verifier (`Fir.Verify`, `verify.rs`) checks a module against its layer before anything else
(`Layer.allows`, `Layer.valueTy`). Counts are from `docs/assurance/op-contracts.json`.

### HFIR

- **Ops (243 kinds):** the 220 shared with MFIR, the 22 HFIR-only ones (`ptr.field`,
  `ptr.index`, `int.{add,sub,mul}.overflow`, `union.*`, `slice.*`, `cf.try`), and `func.ret`.
- **Values:** `iN`, `bN`, `ptr`, `f32`, `f64`, and structs, arrays, unions, and slices of them.
  No function types and no `va_list` (`Ty.isHValue`). Several results may include composites.
- **Meaning:** `Fir.Interp`. Some meanings that matter when lowering:
  - A struct or array value is the tuple of its parts. A load or store of one is a scalar
    access per leaf, at `ptr.offset.wrap` by the leaf's offset, with alignment
    `gcd(align, offset)`. Padding is neither read nor written (decision: Aggregate values).
  - A `union` is a tagged sum value. It has no layout and can't be stored, so it is not C's
    `union`: `fcc` represents a C union as a struct of its size.
  - A slice is a pointer and a length.
- **Made by:** `fcc --emit hfir`, the builder and C API, or text. **Read by:** `fir lower`;
  `fir run`; `fir opt` (passes don't check the layer and are proved over the shared semantics, so
  they run on HFIR too); and `fir compile`, which lowers first (`backend::prepare`).

### MFIR

- **Ops (223 kinds):** the 220 shared ops, `func.invoke` and `func.invoke.indirect` (MFIR only),
  and `func.ret`. Of the building blocks only `agg.make`, `agg.extract`, and `agg.insert` remain.
  `ty.size`, `ty.align`, and `ty.offset` remain as layout constants.
- **Meaning:** `Fir.Interp`, exactly as for HFIR. MFIR has no meaning of its own; it is a subset
  of the same language, plus `func.invoke` (a call whose exception jumps to a block).
- **No target in it yet.** MFIR has no target legality declaration and no target queries. Apart
  from the data layout it inherits, it is target-independent.
- **Three different "MFIRs".** The set of modules the verifier accepts, the set the lowering
  produces, and the set the backend compiles are not the same:

  | | Composite (struct, array) values | Integers | Other limits |
  |---|---|---|---|
  | The verifier accepts | Anywhere a value can be, except loads, stores, and `select`: also loop state, `cf.if` and `cf.blocks` results, block arguments, and holes | Any width | — |
  | The lowering produces | Only where calls pass them whole: parameters, call arguments and results, `va.arg` results, a function's only result. They are made by `agg.make` and taken apart by `agg.extract` | Wider than the source's: one more bit for checked `add`/`sub`, twice the width for checked `mul`, twice the address size for `ptr.index.inbounds` | Temporaries `%.s*`, `%.x*`, `%.e*` |
  | AArch64 selection accepts | What the lowering produces, minus composites whose pointers a register word would split: `struct<packed>{i8, ptr}` lowers, and selection refuses it | Over 64 bits only in ops whose low 64 bits depend only on the operands' low 64 bits | AAPCS64's layout. No holes. For macOS, `backend::aarch64::compile` also refuses variadics and composites passed on the stack, but `fir compile` calls selection directly and skips that check (G12) |

  The decision log says region state and holes stay scalar outside HFIR (decision:
  Aggregates), and the lowering follows that, but the verifier doesn't enforce it (G9). That
  difference is G3. The difference between the lowering's output and what selection accepts is
  G4.

### LFIR (`layer lfir aarch64`)

- **Ops (292 kinds):** 291 `aarch64.*` ops and `func.ret`, kept only for a body that returns its
  parameters. A function's body is `aarch64.code { ^b0: … }`: labeled blocks of instructions
  that name registers as immediates and have no operands or results (decision: LFIR for
  AArch64). There are two forms: over virtual registers (`--emit lfir-vregs`, after selection) and
  over physical registers with a frame (`--emit lfir`, after allocation).
- **Types** appear only in signatures, which follow MFIR's rules, and in `blr`'s callee
  signature. There is no SSA, no facts, and no UB modifiers.
- **Meaning:** `Fir.AArch64Machine`. It differs from MFIR's machine in these ways:
  - A register holds a word: 64 bits, or a pointer with its provenance. It is never `poison`;
    where MFIR has `poison`, the machine takes an oracle choice.
  - Memory is flat for integer addresses. An access through an integer reaches whichever live
    allocation holds those bytes, exposed or not. Bounds and lifetimes are checked; alignment,
    `noalias`, and `readonly` are not.
  - The stack is one allocation of 1 MiB (`stackSize`), so reading past one slot into the next
    within it is defined.
  - Calls follow AAPCS64 (`Fir.AArch64Abi`). A callee must preserve `x19`–`x29`, `sp`, and
    `d8`–`d15`, and the machine gets **stuck** at a return that doesn't. Return addresses aren't
    modeled.
  - Exceptions use a slot outside memory (decision: Exceptions at run time).
- **Stuck is reachable.** In HFIR and MFIR, verified modules are meant never to get stuck (the
  verifier's stated invariant, not proved). The LFIR verifier
  doesn't even aim for that: reading an unwritten register, using the wrong register class, or
  clobbering a callee-saved register all get stuck. A stuck run refines nothing defined, so a
  statement with LFIR as the target (P5) must treat a stuck LFIR run as a failure wherever the
  source is defined. Proving that the LFIR verifier rules stuck runs out is a separate question.
- **Below LFIR,** the assembly has no provenance, a real OS stack (typically 8 MiB on Linux),
  and real alignment. Source lines appear only with `fir compile -g`.

## 3. HFIR → MFIR: what lowering keeps, changes, and loses

**The claim:** each lowered function refines the HFIR one, with arguments and results mapped as
the lowered signature takes them (`sigParams`, `sigRets`): structs and arrays whole, everything
else as its scalars (`Lower.lowerValue`). **Proved:** the expansion step only
(`Lower.Proof.Expand.refines`, `lowerFunc_refines`), per function, in the source module, for a
`Decided` source without temporary-looking names whose expanded ops take variables. **Tested:**
the Rust text equals Lean's (`tests/lower.rs`, `tests/fuzz.rs`), and each fixture run of the
lowering gives the same outcome as the HFIR run, or the same events before HFIR UB
(`RunOutput::lowers_to`). The C corpus is also run at every layer
(`crates/fir-capi/tests/fcc.rs`).

| Item | What happens | Semantic loss? |
|---|---|---|
| Behavior | Refines the source (claimed; see above for what is proved) | — |
| Signatures | Unions, slices, and several results become their scalars. Structs and arrays stay whole as the C ABI's unit. A native caller of a lowered function sees the MFIR signature | No, but the interface changes: `@get(%u)` becomes `@get(%u.0, %u.1, %u.2)` |
| Names | Scalars keep theirs; aggregate parts become `%n.0`, `%n.1`, …; new temporaries are `%.s*`, `%.x*`, `%.e*`. Neither form is reserved, so a source that already uses one can't be lowered (G5) | No |
| Locations | Kept on every op that comes from an op; the `agg.extract`s that take a struct parameter apart have none | No |
| Facts | Kept on scalars, the only values they apply to | No |
| UB modifiers | Kept. `ptr.field.inbounds` becomes `ptr.offset.inbounds`, and `ptr.index.inbounds` an exact product with `int.trunc.nsw` | No |
| Field and element identity | `ptr.field %a, 1` becomes `ptr.offset … 4`, and `ptr.index` becomes integer arithmetic. Offset 0 is both a struct and its first field | Information only: layout facts are now constants |
| Aggregate loads and stores | Become one scalar access per leaf, at `ptr.offset.wrap`, alignment `gcd(align, offset)` | **None.** That is HFIR's own definition. What's lost is only the fact that the leaves were one access |
| Unions | Become a tag plus every variant's scalars, `poison` for those it doesn't hold. `union.get.trap` becomes a compare and `cf.check.tag`; `union.get.ub` becomes copies | No |
| Slices | `slice.get`/`set` become a compare and `cf.check.bounds` (`.trap`), then `ptr.offset.inbounds` and the access | No |
| Checked arithmetic | Becomes arithmetic one bit wider (twice the width for `mul`): `i64` overflow needs `i65`/`i128` (G4) | No; the backend can't take it |
| `cf.try` | Becomes a `cf.blocks` with the handler as a block; calls that may throw become `func.invoke` | Information only: which `cf.blocks` was a `try` |
| Holes | Become the same hole at each scalar type. A hole of an empty struct or array has no scalars, so it disappears: a run that stops at it in HFIR goes on in MFIR (G11) | **Yes**, for empty composites |

## 4. MFIR → LFIR: what selection and allocation keep, change, and lose

**The claim:** the native program, and the LFIR at either stage, refine the MFIR program, with
values passed as AAPCS64 says. **Defined only by the tests** (`tests/aarch64.rs`, `tests/abi.rs`):

- the outcomes are compared as printed text;
- `poison` in the source matches any value;
- values that depend on addresses are found by a taint analysis and rerun under other address
  layouts the semantics allows;
- NaNs follow Arm's rule (an oracle the semantics allows, `Oracle.arm`);
- runs whose source is UB, stuck, ambiguous, a hole, or out of fuel are not compared.

**Proved pieces:** registers carry a composite's defined bytes exactly
(`Fir.AArch64.roundTrip`), and Arm's FP results are ones FIR allows (`Fir.AArch64Proofs`).
**Checked on every compile:** the data layout (`isel::check_module`) and the allocation
(`regcheck::validate`, unproved). `fir compile` doesn't run the LFIR verifier on its own output.

| Item | What happens |
|---|---|
| UB and `poison` | UB modifiers become a concrete choice: `.nsw`/`.nuw`/`.ub` wrap, and `poison` is 0. Each choice is one the source allows. Soundness for `freeze` relies on each value being computed into one register once |
| Facts | Dropped, `check` included (G6). A violated fact, which is UB in MFIR, does whatever the code does (`facts.fir`'s `@percent(200)` returns 200) |
| Bounds, lifetimes, provenance | Stack slots merge into one frame, already in the LFIR machine, so an out-of-bounds stack read that is UB in MFIR reads the neighbouring slot. Heap and global bounds, lifetimes, and provenance are kept in the LFIR machine and gone in the assembly |
| Alignment | Not checked by the LFIR machine. Natively, it is the hardware's |
| Names, SSA, types | Gone: virtual registers, then physical ones |
| Locations | Kept on LFIR instructions. In the assembly, with `-g` only, as DWARF lines (`tests/debug_lines.rs`) |
| Stack | Becomes finite: 1 MiB in the LFIR machine and the OS stack natively. MFIR has no such limit (G8) |
| Calling convention | AAPCS64 for every function, internal ones included. Several scalar results use `x0`/`x1` (or `d0`/`d1`), then memory at `x8`. Exceptions use an error-return slot |

## 5. What remains unknown

1. **Whether real programs are `Decided`.** Every theorem assumes it, and nothing checks it. C
   code that turns integers into pointers is where it is most likely to fail.
2. **Whether scalarization, `cf.try` lowering, and whole-module lowering are correct.** They are
   tested, not proved. Scalarization changes signatures, so `Func.Refines`, which compares two
   functions with the same arguments in one module, can't even state it (P4).
3. **Whether LFIR refines MFIR.** Nothing defines it in Lean (P5). The register allocation
   validator can't be proved until it is.
4. **Whether passes compose.** Each theorem covers one function in a fixed module. Running
   passes in sequence over a whole module is open
   ([obligation 3](../assurance/README.md#remaining-obligations)).
5. **What stack exhaustion means.** HFIR and MFIR have no limit. The LFIR machine's 1 MiB stack
   turns exhaustion into `ub out-of-bounds`, and native code segfaults (G8). Every compiler has
   this gap; FIR hasn't said what it assumes.
6. **Callbacks.** The semantics doesn't model an external function calling back into the
   module (decision: External call semantics). A C program that passes a FIR function to
   `qsort` runs natively, but the semantics only covers it as far as the callee's declared
   effects describe it.
7. **The Apple ABI's extension of narrow arguments**, which hasn't been confirmed (there is no
   Mac in CI).
8. **Op effects.** The declared effects are not checked against the semantics and are
   incomplete for some kinds (`freeze_changes_core`). Nothing relies on them yet.

## 6. Gaps

G1–G7 come from the [audit](../assurance/layer-audit.md#gaps-the-audit-exposed); G8–G10, and
G5's wider form, were found while writing this file, and G11 and G12 by an independent review of
it. Every open gap but G7 (a test's coverage)
was reproduced at `1ac29a2` with `fir check`, `run`, `lower`, and `compile`, and G8 natively
under qemu.

| | Gap | Status |
|---|---|---|
| G1, G2 | Layouts other than AAPCS64's miscompiled C calls and overran `va_list` | fixed: refused by `isel::check_module` |
| G3 | An MFIR `cf.if` yielding a struct verifies, then selection refuses it as "HFIR only" | open; the cause is G9 |
| G4 | `int.add.overflow.s` on `i64` lowers to `i65` ops that verify, then selection refuses them | open |
| G5 | A source name the lowering also makes breaks it ("defined more than once"). That covers temporaries like `%.e0`, and also a scalar name: `%s.1: i32` next to `%s: struct<C>{i32, i32}` verifies and runs as HFIR, and its lowering doesn't verify. `fcc` renames clashing locals to this same form (`x.1`, `nameValue`). The corpus doesn't hit it | open (refused, not miscompiled) |
| G6 | Facts are dropped by selection, and no trust level means anything to the compiler | open |
| G7 | `tests/lower.rs` skips runs whose arguments don't parse at both layers, so it never compares functions whose signatures scalarization changes | open |
| G8 | **HFIR and MFIR stacks are unbounded; LFIR's and native code's are not.** A recursive MFIR function with a 64-byte slot returns `100000` for `@deep(100000)` in `fir run`. The LFIR machine gives `ub out-of-bounds (offset -8, …, allocation size 1048576)`, and qemu crashes with a segfault. The target is less defined than its source. No test exercises it: fixtures don't recurse that deep | open (P6) |
| G9 | **MFIR's verifier accepts composite loop state, `cf.if`/`cf.blocks` results, and holes,** which decision Aggregates says stay scalar outside HFIR. `cf.loop iter(%s: struct<C>{i32, i32} = %s0)` verifies and runs as MFIR | open (P1) |
| G10 | `fir check` prints a composite hole's type as `type#0` (`bin/fir.rs:99` prints a `Ty` without the module's type table) | open, cosmetic |
| G11 | **The lowering drops holes of empty composites.** `%s: struct<C>{} = copy ?h: struct<C>{}`, then returning 7, runs as `hole ?h` in HFIR and returns 7 after lowering, which doesn't refine it: an empty composite has no scalars to carry the hole (`Lower.lean`, scalarizing) | open |
| G12 | **`fir compile --os darwin` skips the macOS checks.** The CLI calls `select` and `allocate` itself (`bin/fir.rs`), not `backend::aarch64::compile`, so it emits a variadic function for macOS that the library refuses | open |

## 7. Proposed shared-IR changes

These tighten or complete the shared definitions; none changes what an op means or adds a
layer. Each must land in Lean and Rust together, as the verifier and the lowering already do.

| | Change | Closes | Cost |
|---|---|---|---|
| P1 | **Enforce decision Aggregates in both verifiers.** Outside HFIR, the parameters of every region but a function's entry, region results, block arguments, and holes must be scalars. Composites stay legal only where calls pass them whole (function parameters and results included) and in `agg.*` | G3, G9 | Small: `Verify.lean`, `verify.rs`, and a `tests/layers/errors` fixture. The lowering already produces only this |
| P2 | **Make the lowering's names unable to clash.** Reserve names starting with `.` in HFIR (the verifier rejects them; temporaries keep them), and give a part `%n.i` a fresh suffix when the source already uses that name, in `Lower.lean` and `lower.rs` alike | G5. `Expand.refines`'s `NoTemps` hypothesis then follows from verification | Small. The reservation also rejects HFIR that lowers today (`%.e0 = int.const 7`, returned). The alternative, fresh names for temporaries too, rejects nothing but means restating `NoTemps` |
| P3 | **Target legality as data.** One predicate per target, generated for Rust like the op contracts: which integer widths and composite positions each op takes. `fir check --target aarch64` would run it, and selection would use it for its refusals | G4 reported at MFIR, not as a selection failure. This is the design's "target legality rule", in its smallest form | Medium |
| P4 | **Refinement through a value encoding.** `Func.RefinesVia enc` (arguments encoded and results decoded as the lowered signature takes them: `sigParams`/`sigRets`, with `lowerValue` for the parts that become scalars) and `Module.Refines` (every function replaced at once, so calls go to the target's callees) | Makes items 2 and 4 of section 5 statable. `Func.Refines` stays the case `enc = id` | Medium (definitions only); the proofs are the open obligations |
| P5 | **Behaviors for LFIR.** `AArch64.Behaves` from the machine's existing `step`, and `Implements` between an MFIR function and its LFIR, with `Fir.AArch64Abi` as the encoding and the stuck outcomes above ruled out (or treated as failures) | Item 3. Gives the test harness's comparison a stated relation, and states [obligation 1](../assurance/README.md#remaining-obligations) | Medium |
| P6 | **A resource-exhaustion outcome.** A target may stop for lack of stack at any point where its trace so far refines the source's. The LFIR machine would report it when `sp` leaves the stack instead of `ub out-of-bounds`, and the native test runtime would map a guard-page fault to it | G8, item 5. It keeps "UB" meaning the source's fault | Medium. A new outcome isn't enough: `Behavior.Refines` compares whole traces, so it must also let an exhausted target's events refine a prefix of a source behavior's, infinite ones included |
| P7 | **Decide what trust levels mean.** Either `check` facts on values (ranges, `nonnull`, `align`) become checks with a new trap reason, lowered in HFIR → MFIR, or the trust tag is documented as advisory. A fact lets `poison` pass and `cf.check` of `poison` is UB, so the check has to let `poison` through rather than be a plain `int.cmp` and `cf.check`. `noalias` and `readonly` constrain accesses for a whole call and would need scope tracking at run time | G6 | Advisory: small. Checks: medium (a trap reason, a poison-passing check, and its proof) |

Raising lowered MFIR back to fields (a field-path side table) is deliberately not proposed until a
promotion pass needs it ([layer-audit.md §5](../assurance/layer-audit.md#5-raising-selectively)).
