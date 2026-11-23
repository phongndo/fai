# Plan: the promotion round

The C round ([04-plan.md](04-plan.md)) ended with a compiler that builds Lua and SQLite
correctly and whose proofs and speed don't meet. `-O` holds only passes with Lean refinement
proofs, and gains 1% to 6%. The pass that gains more, `mem2reg`
([05-optimizing-c.md](05-optimizing-c.md)), is experimental and unproved. This round closes
that gap or finds out that it can't be closed: promotion proved (the headline proof decision
"FIR-1 scope" names), in `-O`, and worth having there.

It starts from a measurement, not from the proof
([promotion-baseline.md](../performance/promotion-baseline.md)): on Lua and SQLite the
experimental pipeline is correct and does not pay. So the order below is "make it pay, then
prove it", with a stop rule after each.

## Done when

1. `mem2reg` is in `-O`, and every pass in `-O` still has a Lean refinement proof registered in
   the proof audit, with the Rust pass bound to it at least as DCE is (a proved checker on
   request, a tested transcription by default).
2. `fcc -O` executes no more instructions than GCC `-O0` on each of the 7 Lua workloads and on
   speedtest1 (`projbench.py count`), and takes no more time than GCC `-O0` on the same,
   natively (`projbench.py time`). Today it executes 2.27× on Lua and 1.16× on speedtest1.
3. `fcc -O` compiles `lvm.c` and `sqlite3.c` in at most twice today's `-O` time and memory.
4. `fai verify full` passes, and Lua's suite and speedtest1's `--verify` hash still match.

## Tracks

| Track | What | Done when | Depends on |
|---|---|---|---|
| Z: Baseline | Promotion on Lua and SQLite: behavior, instructions, compile time | **done**: [promotion-baseline.md](../performance/promotion-baseline.md) | — |
| B: Make promotion pay | The allocator gives promoted values registers, or one home each; the validator scales on promoted code | checkpoint 1, below | Z |
| S: Selection | The local rules [c-baseline.md](../performance/c-baseline.md#2-instruction-selection-one-op-at-a-time-generated-code) lists: immediates, compare-and-branch, no-op and repeated extensions, scaled indices | `fcc -O`, without promotion, executes at most 1.3× GCC `-O0`'s instructions on Lua | — |
| P: Promotion proved | `mem2reg`'s rewrite relation refines, in Lean, and the Rust pass is bound to it | `Fir.Promote.refines` (or a checker's soundness) is a registered claim with no hypothesis beyond the other passes' (`Decided` source, one function, a fixed module); P1 is **done** | P2 onward: checkpoint 1 |
| V: Validator proved | `regcheck::validate` against `Fir.AArch64Machine` (obligation 1 of [assurance](../assurance/README.md#remaining-obligations)) | acceptance implies LFIR refinement, registered | B (which changes the validator's state) |

B and S are independent and both are in the tested tier already (instruction selection and
allocation have no proofs to keep), so neither changes what is proved. P1 was done first
because it is cheap and sizes the rest; P2 to P6 wait for checkpoint 1.

## Checkpoints and the stop rule

1. **After B: promotion pays.** `fcc-promo` executes at least 10% fewer instructions than
   `fcc -O` on each of Lua (its 7 workloads' geometric mean, with `lvm.c` promoted) and
   speedtest1, no more than `-O` in `sqlite3VdbeExec` and `luaV_execute`, and compiles
   `lvm.c` and `sqlite3.c` within twice `-O`'s time and memory. **If it doesn't**, with
   coalescing and split intervals both in, stop the round here: promotion as designed isn't
   worth its proof, and the proof budget goes unspent. What is then worth keeping is the
   verification tooling (`fai verify`, `fai mutate`, the evidence gate, the proof audit).
2. **After P2: the invariant holds.** That nothing else reaches a promoted slot is proved for
   every core computation and every step of the machine. **If it turns out false** (an op that
   reaches an allocation without a pointer to it), that is a finding about the semantics to
   fix first, with its counterexample as a theorem, as `freeze_changes_core` is. **If it is
   true and costs more than about twice the estimate below**, stop and take the open decision
   under [Alternatives](#alternatives-not-taken) to the owner.
3. **Done when**, above.

Nothing else starts before checkpoint 3: no JIT, Wasm, GPU, new frontend, or x86-64 work.

## Track B: make promotion pay

The baseline's findings, in the order they cost:

- **A block parameter is a move on every edge.** Promotion threads each live variable through
  `cf.blocks` as block parameters. Instruction selection gives each parameter and each
  argument its own virtual register and moves between them; the allocator takes hints only
  from moves to or from physical registers. `lvm.c`'s code goes from 6,328 `mov`s to 54,724.
  Give a parameter and its arguments one home when their intervals don't interfere, so the
  move disappears (the validator already accepts a `mov` the output left out).
- **Promoted values are spilled, and then cost more than the slot they replaced.** An interval
  is the hull of a value's uses, without holes, so a variable live across a large function
  takes a stack slot, and a move between two spilled values is a load and a store through
  scratch registers, with `x16` computing far slot addresses (`movk`: 890M executions in
  speedtest1). `sqlite3VdbeExec` executes 5.6× the instructions it does with `-O`. Split
  intervals at region boundaries (or allocate per region with one home per value across
  them), and prefer the promoted values of the innermost loop.
- **The validator's cost.** `aarch64.regcheck` takes 36 s of CPU time in `sqlite3.c`'s 20 s
  compile, and `lvm.c` doesn't finish in 4.5 minutes and 7.5 GiB. Profile it on the promoted
  `luaV_execute` first; the likely cause is that every omitted `mov` adds the destination to
  each location's set of values, which never shrinks. Dropping values that are dead in the
  input needs a liveness pass over the input, and must not change a verdict: the differential
  run of [compile-speed.md](../performance/compile-speed.md) (186,468 validations, identical
  verdicts and messages) is the check.
- **A gate that sees it.** `fai experiment` measures the `.fir` corpus, which said promotion was
  32% better. Before promotion moves into `-O`, an experiment must also build and count Lua
  and SQLite (`projbench.py --configs`, which this round's baseline added).

A cheaper stopgap exists and is not the plan: have `mem2reg` skip slots it would thread through
a `cf.blocks` with many blocks. It would hide the regression and give up the interpreter
loops, which are where Lua and SQLite spend their time.

## Track P: promotion proved

`mem2reg`'s correctness argument has four parts
([05-optimizing-c.md](05-optimizing-c.md#what-it-rests-on)). The proof follows them, in two
phases that match what the pass does to the cores:

- **Forwarding, stores kept.** Every load of a promoted field becomes a copy of the value the
  field holds, threaded through region results, loop parameters, and block parameters. The
  stores still run, so the two machines have equal cores and the lockstep framework
  (`Fir.CodeRel`) applies as it does for `fwd`; what is new is an invariant relating the
  target's promoted values to the source's memory ("field `f` of slot `s` is tracked at
  `%x`").
- **Deleting the stores**, then the offsets and (separately, `stackdce`) the allocation. Now the
  cores differ, in the slot's bytes only.

| Step | What | Size | Status |
|---|---|---|---|
| P1 | **One op on a slot** (parts 2 and 3 of the argument): a load of a tracked field gives the tracked value and changes nothing; a store sets it and keeps the other fields; no load and no store elsewhere changes it; a fresh slot holds `poison` | `Fir/Slot.lean`, 313 lines | **done**: four registered claims |
| P2 | **Nothing else reaches the slot** (part 1): an invariant `Private a` of the core (no scope on `a`, no exposed tag of `a`, no byte in memory and no global address whose pointer reaches `a`) and of the stack (only the slot's own names hold a pointer to `a`), kept by every core computation whose operands don't reach `a` and by every step of the machine, with the slot's bytes unchanged | estimate: 1,500 to 3,000 lines. `Fir.Space` proves a much simpler fact (the space is fixed) for the same 49 named computations and the control layer in 586 lines; this one needs a postcondition per computation ("the result doesn't reach `a`") | next |
| P3 | **Forwarding in one region**: the simulation for a slot whose accesses are in straight-line code, with any ops between them | estimate: 500 to 800 lines, on P2 | |
| P4 | **Threading** (part 4): values through `cf.if` results, loop parameters, and block parameters, where live. The rewritten ops contain rewritten regions, which `OpsRel` doesn't relate today | estimate: 1,000 to 2,000 lines; the least certain | |
| P5 | **Store deletion**: cores equal except in the slot's bytes. Needs P2 in relational form (two runs that differ only in `a`'s bytes stay so), which is why P2 should be proved that way once | estimate: 500 to 1,000 lines | |
| P6 | **Binding**: a Lean checker for a `mem2reg` step, proved sound from P3 to P5, run as `fir-ref check-dce` is; the Rust pass's output checked by it in the tests, and on request in the compiler | as DCE's: about 500 lines of Lean, the plumbing exists | |

`stackdce` is not in the round. Deleting an allocation renumbers the later ones, and the
source's oracle must then be rebuilt to answer the target's choices at shifted positions: a
separate proof, and `mem2reg` without it already removes the accesses. (The baseline's `fcc-m2r`
column is that pipeline: within 6% of `fcc-promo` on every workload.)

The estimates are from one data point: P1 took 313 lines and compiled at the second build,
because `Fir.Dse`, `Fir.Fwd`, and `Fir.MemRules` already had every lemma it needed. P2 has no
such base.

### What P2 has to face

Read from the semantics while sizing it:

- **The semantics is built for it.** An allocation is reached only through a pointer that
  names it or a bare address whose candidates are *exposed* pairs (`fromExposed`, `resolveIn`);
  allocation ids are fresh (`freshId`); an external function reads and writes only what its
  arguments, the globals, and the exposed allocations reach (`externReach`, `Answer.valid`). No
  place was found that reaches an allocation otherwise.
- **`Quiet` is part of it.** A load records its access in the marks of every scope on the
  allocation, so it changes the core unless no scope watches the slot. Scopes open on a call's
  pointer arguments and on `const` globals, so a slot whose pointer is never passed has none.
- **To check: a `bN` argument's fragments.** `RVal.pairs`, which `externRoots` starts from,
  counts a pointer argument, and the pointers and byte fragments in a composite's leaves, but
  not the fragments in a top-level `bN` argument. An external function given a pointer's
  bytes as a `b64` therefore can't reach its allocation in the semantics, while native code
  receives the address in a register. That doesn't threaten promotion (the model lets the
  callee reach less, not more), but it looks like a gap between the semantics and the machine,
  and should be decided before P2 fixes its definition of "reaches".
- **Addresses.** `realize` places an allocation among those that already have addresses. A
  promoted slot never gets one (its pointer is only loaded and stored through), so it doesn't
  move the others: needed for P5, where the slot's bytes differ.

## Alternatives not taken

Recorded for the owner; none is decided here.

- **Locals that aren't memory.** If HFIR had frame-local variables (`var.new`, `var.get`,
  `var.set`: a cell in the frame, with no address), a frontend that knows a local's address is
  never taken would emit them, and promotion would be a rewrite on environments only: part 1
  of the argument would hold by construction (a callee can't see the caller's frames, as DCE
  already uses), and P2 would not be needed. It moves "is this local promotable?" into the
  frontend, which is outside the proved base, and doesn't cover struct fields or locals whose
  address is taken in dead code. It is a change to the IR's design, so it is the owner's call;
  checkpoint 2 is where it becomes worth asking.
- **Promotion as a tested pass in `-O`.** Would break the rule that `-O` holds only proved
  passes, which is the project's thesis. Not taken.

## Progress

### Track Z: baseline (done)

[promotion-baseline.md](../performance/promotion-baseline.md). Behavior matches on both
projects. Against `fcc -O`, promotion executes 5% fewer instructions on Lua without its
interpreter loop, 2.5% fewer in SQLite outside `sqlite3VdbeExec`, and 5.6× more inside it;
`lvm.c` does not compile with it in practical time and `sqlite3.c` takes 14× longer.
`projbench.py` gained `--configs` (any of its configurations, and fcc with an experimental
pipeline: `fcc-m2r`, `fcc-promo`) and `--plain` (files those compile with `-O`).

### Track P1: one op on a slot (done)

`spec/Fir/Slot.lean`, registered in the proof audit (44 claims), each under the role
"promotion: one op (mem2reg is not proved)":

- `Slot.load_tracked`: through a pointer into an allocation no scope watches (`Quiet`), whose
  bytes at the pointer's offset encode a value `v` of the load's type (`Fwd.Exact`), a load is
  UB or gives `v` and leaves the core exactly as it was. `load_tracked_op` states it for the
  op, as "does what `copy v` does".
- `Slot.store_tracked`: a scalar store there leaves the offset holding the stored value's
  encoding, the allocation unwatched, and the space unchanged; `store_quiet` says only that
  allocation's bytes changed, and `store_keeps` that every range the store doesn't overlap
  reads as before.
- `Slot.load_keeps`: a scalar load through any pointer changes no allocation's bytes, no scope,
  and not the space. `store_elsewhere`: a store that resolves to another allocation leaves this
  one's bytes and the scopes.
- `Slot.fresh_tracks`: at a field's type (`Slot.Field`: whole-byte integers, pointers,
  floats), the `poison` op gives one value of that type without changing the core, and fresh
  bytes are its encoding.

These are single ops under hypotheses the simulation will have to supply (`Quiet`, and where
each pointer points). They say nothing yet about a program.

## Not in this round

- JIT, VM embedding, Wasm, GPUs, a second frontend, floats on x86-64, an object writer.
- Module composition and `Decided` (obligation 3), scalarization and `cf.try` lowering
  (obligation 4), instruction selection against ISA semantics (obligation 6): the round's
  theorem is at the other passes' bar, one function in a fixed module with a `Decided` source.
- `stackdce`'s proof.
