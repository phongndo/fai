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

Two gaps are in play, and the work below closes them separately. The **speed gap** is fcc's
code against GCC `-O0`'s: instruction selection (track S) closes most of it, and does so
without any proved pass. The **thesis gap** is that the proved passes are not the ones that
make code fast: only promotion proved and in `-O` (track P) closes that. S alone would leave
the project with a faster compiler and the same thesis gap.

## What this is for, and the rule

The owner's goal for fai is **a compiler environment that moves fast, stays durable, and is
easy for agents to verify**. For the work below that means:

1. **A step's test decides.** Each step names its test before the work starts. A change that
   fails its test is taken out, not kept with an explanation. Step 4 was kept against its
   tests for one revision and has been reverted.
2. **The verdict is one command, and it is PASS or FAIL.** `fai verify full` says whether the
   tree is correct. `fai gate` says whether Lua and SQLite are still right and no worse than
   what was accepted ([benchmarks/projects/README.md](../../benchmarks/projects/README.md#the-gate)).
   Neither needs judgment to read: exit 0 or 1, with the reasons printed.
3. **A gain is kept by a baseline, not by memory.** `benchmarks/projects/gate.json` holds what
   was accepted and moves one way: `fai gate --update` refuses unless the gate passes, and the
   file's diff is the record of what a change bought. A trade is made by editing it by hand,
   where it can be seen.

## Done when

1. `mem2reg` is in `-O`, and every pass in `-O` still has a Lean refinement proof registered in
   the proof audit, with the Rust pass bound to it at least as DCE is (a proved checker on
   request, a tested transcription by default).
2. `fcc -O` executes no more instructions than GCC `-O0` on each of the 7 Lua workloads and on
   speedtest1 (`projbench.py count`), and takes no more time than GCC `-O0` on the same,
   natively (`projbench.py time`). It executed 2.27× on Lua and 1.16× on speedtest1 when the
   round began, and executes 1.20× and 0.63× after step 5; time is not measured yet.
3. `fcc -O` compiles `lvm.c` and `sqlite3.c` in at most twice today's `-O` time and memory.
4. `fai verify full` passes, and Lua's suite and speedtest1's `--verify` hash still match.

## Tracks

| Track | What | Done when | Depends on |
|---|---|---|---|
| Z: Baseline | Promotion on Lua and SQLite: behavior, instructions, compile time | **done**: [promotion-baseline.md](../performance/promotion-baseline.md) | — |
| B: Make promotion pay | The allocator gives promoted values registers, or one home each; the validator scales on promoted code | checkpoint 1, below | Z |
| S: Selection | The local rules [c-baseline.md](../performance/c-baseline.md#2-instruction-selection-one-op-at-a-time-generated-code) lists: immediates, compare-and-branch, no-op and repeated extensions, constant offsets and scaled indices in addresses. A jump table for `cf.switch` is parked (step 10) | `fcc -O`, without promotion, executes at most 1.3× GCC `-O0`'s instructions on Lua. **Met: 1.20×** ([selection.md](../performance/selection.md)) | step 1 |
| P: Promotion proved | `mem2reg`'s rewrite relation refines, in Lean, and the Rust pass is bound to it | `Fir.Promote.refines` (or a checker's soundness) is a registered claim with no hypothesis beyond the other passes' (`Decided` source, one function, a fixed module); P1 is **done** | P2 onward: checkpoint 1 |
| V: Validator proved | `regcheck::validate` against `Fir.AArch64Machine` (obligation 1 of [assurance](../assurance/README.md#remaining-obligations)) | acceptance implies LFIR refinement, registered | B (which changes the validator's state) |

B and S are both in the tested tier already (instruction selection and allocation have no
proofs to keep), so neither changes what is proved, and they touch different files
(`isel.rs`; `regalloc.rs` and `regcheck`). They are not independent in what they measure: S
makes `-O` faster, which is what checkpoint 1 compares promotion with, so the baseline is
measured again between them (step 6). P1 was done first because it is cheap and sizes the
rest; P2 to P6 wait for checkpoint 1.

## Next steps, in order

Each step is one piece of work with a test that passes or fails. Steps 1 to 4 are probes: small,
and they decide the order and size of the rest, so they come before any larger work on a
compiler that checkpoint 1 may stop. **Steps 1 to 6 are done**
([selection.md](../performance/selection.md); [Progress](#progress) has each test's result):
steps 1, 2, 3, 5, and 6 passed their tests. Step 4 failed its own and was reverted, so `lvm.c`
again does not compile with promotion: step 7 has to make it, before checkpoint 1 can be
measured on Lua. Steps 7 and 8 are next.

| # | Step | Test | Feeds |
|---|---|---|---|
| 1 | **Lua's instructions by form.** Run the per-address plugin (`benchmarks/c/hist.c`, which `bench.py` uses on the corpus) on the 7 Lua workloads and name each form by function, as c-baseline's table does for the kernels. The baseline has them by mnemonic only | a table that attributes at least 80% of fcc `-O`'s 649M excess over GCC `-O0` to forms | step 5's rules and their order |
| 2 | **Where `-O`'s extra stack traffic comes from.** fcc `-O` makes 301M stack accesses on Lua against GCC `-O0`'s 187M | the 114M split into spill code, the frontend's own slots, and call setup, in `luaV_execute` and outside it | if it is spills, step 8 pays for `-O` itself and moves ahead of step 5 |
| 3 | **Profile the validator on promoted code**: `sqlite3.c` with `fcc-promo` (20 s) and the promoted `lvm.c` (doesn't finish) | where the time and the memory go, by function, with the sizes of the sets per location over the walk | step 7 |
| 4 | **Rejected: it failed its test and was reverted.** One dispatch block for computed `goto`. fcc emits a `switch` over every address-taken label at each `goto *` (`frontends/c/src/Lower.cpp`, `IndirectGotoStmt`), so `luaV_execute` has an edge from every case to every case. Jump to one block that switches. A hypothesis: it should cut the edges promotion threads values over, and the code | `lvm.c` with `fcc-promo` compiles within twice `-O`'s time and memory; Lua's suite passes; `-O`'s instructions on Lua don't go up | whether checkpoint 1 can be measured on Lua at all. It can't help SQLite, whose loop is a plain `switch` |
| 5 | **Selection rules that need no new op** (track S), cheapest first by step 1's table: drop the no-op extension, use immediates, branch on a compare's flags, don't extend what is already extended, fold constant offsets into loads and stores, shift instead of multiplying by a power of two | each rule: the corpus and both projects behave the same, and Lua's instructions go down; all: track S's gate | Done when 2 |
| 6 | **Measure the baseline again**: `-O` and both promotion pipelines on Lua and SQLite, at the revision after step 5 | promotion-baseline's tables, again | checkpoint 1's denominator |
| 7 | **The validator scales** (track B), by what step 3 finds | `sqlite3.c` and `lvm.c` with `fcc-promo` within twice `-O`'s compile time and memory; the differential run's verdicts and messages identical | checkpoint 1 |
| 8 | **The allocator gives promoted values homes** (track B): one home for a block parameter and its arguments, intervals split at region boundaries, and one slot for spilled values that are never live together | checkpoint 1, and Lua's suite passing with promotion | — |
| | **Checkpoint 1**: go on, or stop the round | below | |
| 9 | **P2 to P6** (track P): promotion proved, bound to the Rust pass, and in `-O` | checkpoint 2, then Done when 1 | |
| 10 | **A jump table for `cf.switch`**: the one selection item that needs a new LFIR op (an indirect branch) with Lean semantics, both interpreters, and the emitter. Its ceiling on Lua is about 10% of fcc's instructions: every `b.eq`, `b.cs`, and `cmp` together is 117M of 1,135M, and some of those are ordinary branches | Lua's instructions down, and track S's gate still met | parked until after checkpoint 1 |
| 11 | **Track V**: the validator proved | its track's | after steps 7 and 8 settle its state |

Steps 7 and 8 can run side by side, and are the next thing to do in this plan. Before them come
stages 0 and A of [07-plan.md](07-plan.md), which make the verdicts these steps are judged by
harder to fool, and bound the validator so that step 7's own test can't hang. Step 8 has grown: besides
one home for a block parameter and its arguments and split intervals, spilled values must
share slots. While step 4's change was in and `lvm.c` compiled with promotion, the promoted
`luaV_execute`'s frame was 129 KB, and Lua's deep-recursion tests overflowed the stack with it.

**How the targets add up.** The gates of S and of checkpoint 1 are minimums for going on, and
they don't reach item 2 by themselves: S at 1.3× with promotion at the checkpoint's 10% is
1.17× GCC `-O0` on Lua. Item 2 needs promotion to do on these programs what it does on the
corpus once its values are in registers (32% fewer: 1.3× becomes 0.88×), or S to end nearer
1.1×. After step 5, S stands at 1.20× on Lua, and what is left of the excess is mostly
dispatch (step 10) and the prologue
([selection.md](../performance/selection.md#what-is-left-of--os-excess-on-lua)); promotion's
part is unmeasured until its values get registers. So item 2 is the round's target and may be
reported as missed, with the number, the way 04's "Round status" reports its items.

## Checkpoints and the stop rule

1. **After steps 4 to 8: promotion pays.** `fcc-promo` executes at least 10% fewer instructions
   than `fcc -O` at the same revision (so with track S's rules in both) on each of Lua (its 7
   workloads' geometric mean, with `lvm.c` promoted) and speedtest1, no more than `-O` in
   `sqlite3VdbeExec` and `luaV_execute`, and compiles
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
  speedtest1). `sqlite3VdbeExec` executed 5.6× the instructions it did with `-O` at the
  baseline, and 9.9× after step 5 made `-O` faster. Split
  intervals at region boundaries (or allocate per region with one home per value across
  them), and prefer the promoted values of the innermost loop.
- **Every spilled value has a slot of its own.** The promoted `luaV_execute`'s frame was
  128,832 bytes (3,312 with `-O`) when step 4's change let it compile, and Lua allows 200
  nested C calls: four files of its suite overflowed an 8 MiB stack. Slots must be shared
  between values whose intervals don't meet.
- **The validator's cost.** `aarch64.regcheck` takes 36 s of CPU time in `sqlite3.c`'s 20 s
  compile, and `lvm.c` doesn't finish in 4.5 minutes and 7.5 GiB (with step 4's dispatch
  block, since reverted, it took 5.3 s); one stack sample of it was in `State::join`. Profile it on the promoted `lvm.c` first; the likely cause, not
  established, is that every omitted `mov` adds the destination to each location's set of
  values, which never shrinks, and every join copies the sets. Step 3 measured it: 42 values
  per location on the promoted `luaV_execute`, and about 85% of the time in joins. Dropping
  values that are dead in the input needs a liveness pass over the input. It can only make the
  validator refuse more (a dropped fact is never a reason to accept), so a wrong liveness
  fails a compile and passes no miscompile; it must still not change a verdict on correct
  code: the differential run of [compile-speed.md](../performance/compile-speed.md) (186,468
  validations, identical verdicts and messages) is the check.
- **A gate that sees it**: under [Improvements outside the tracks](#improvements-outside-the-tracks).

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
| P1 | **One op on a slot** (parts 2 and 3 of the argument): a load of a tracked field gives the tracked value and changes nothing; a store sets it and keeps the other fields; no load and no store elsewhere changes it; bytes never written are `poison`'s encoding | `Fir/Slot.lean`, 313 lines | **done**: four registered claims |
| P2 | **Nothing else reaches the slot** (part 1): an invariant `Private a` of the core (no scope on `a`, no exposed tag of `a`, no byte in memory and no global address whose pointer reaches `a`) and of the stack (only the slot's own names hold a pointer to `a`), kept by every core computation whose operands don't reach `a` and by every step of the machine, with the slot's bytes unchanged. Also that a new allocation's id has no bytes yet (the keys of `mem` are among those of `allocs`), which P1's `fresh_tracks` assumes | estimate: 1,500 to 3,000 lines. `Fir.Space` proves a much simpler fact (the space is fixed) for the same 49 named computations and the control layer in 586 lines; this one needs a postcondition per computation ("the result doesn't reach `a`") | next |
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

## Improvements outside the tracks

Found while measuring. Each is small, and none is started.

- **A gate that includes real programs: done**, as `fai gate` ([Progress](#the-gate-done)).
  `fai experiment` still judges a change on the `.fir` corpus alone, which said promotion was
  32% better; `fai gate --configs fcc-promo` is what says it isn't, and both are required
  before a pass moves into `-O`. Not done: running the gate in CI (it fetches Lua and SQLite,
  and takes five minutes), and gating run time on hardware, which needs the AArch64 host.
- **A `bN` argument's fragments** ([What P2 has to face](#what-p2-has-to-face)): whether an
  external function reaches the allocation of a pointer whose bytes it is given as a top-level
  `bN` argument. Today's semantics says no; native code can. **The owner's decision**: change
  `RVal.pairs`, or record that the model is meant so.
- **The decision log's "Next round" row** still names the C round. **The owner's decision**:
  point it at this plan, or elsewhere.

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

### Lua's instructions with `-O` (measured)

[promotion-baseline.md](../performance/promotion-baseline.md#where-luas-instructions-go-with--o):
by mnemonic over the 7 workloads, with `luaV_execute` at 782M of fcc's 1,135M. It is what
steps 1, 2, and 10 start from. No selection rule has been written.

### Steps 1 to 6 (done)

[selection.md](../performance/selection.md) has the measurements. Each step against its test:

| # | Test | Result |
|---|---|---|
| 1 | Attribute at least 80% of `fcc -O`'s 649M excess on Lua to forms | **Passed.** `projbench.py forms` names every executed instruction; the forms where fcc executed more than GCC `-O0` add up to 709M: constants in registers, extensions, register adds, spill reloads, frame addresses |
| 2 | Split `-O`'s extra 114M stack accesses | **Passed.** All of it was the allocator's: 56M spill reloads, every one of an address (each local's address lived in a register, and large functions spilled it), 27M spill stores, and 49M register saves and restores against GCC's 10M. fcc's own slot traffic was GCC's. So the fix was in selection, not allocation: address a slot from `sp` |
| 3 | Name where the validator's time and memory go on promoted code | **Passed.** About 85% is joining block states. On the promoted `luaV_execute` a location holds 42 values on average: an omitted `mov` gives a value a second name, and no name is dropped when it dies |
| 4 | `lvm.c` with `fcc-promo` compiles within twice `-O`; Lua's suite passes; `-O`'s instructions on Lua don't go up | **Failed all three; reverted.** With one dispatch block `lvm.c` compiled with promotion, where it did not, but in 5.3 s against `-O`'s 0.09 s; 4 of Lua's 28 suite files overflowed the stack with promotion (a 129 KB frame; they passed with a 64 MiB stack); and `-O` executed 1.3% more on Lua. It did compile `lvm.c` twice as fast into 2.4× less code with `-O`, which no test of the step asked for. `fai gate` rejects the same change: see below |
| 5 | Each rule keeps behavior; `fcc -O` at most 1.3× GCC `-O0` on Lua | **Passed: 1.20×**, from 2.27×, and 0.63× on speedtest1, from 1.16× (1.19× Clang `-O0`'s, from 2.21×). Lua's suite, the workloads, speedtest1's hash, `fai verify full`, and `fai gate` pass. The rules were measured together, not one by one |
| 6 | The baseline's tables at the new revision | **Done.** Promotion executes 3.4× `-O`'s instructions on speedtest1, does not compile `lvm.c`, and on the rest of Lua executes 1.8% fewer |

What the steps changed: `targets/aarch64/src/isel.rs` (constants, frame slots, pointers plus
constants, and comparisons get no register where an op can take them directly; known
extensions aren't repeated) and `projbench.py forms`. No LFIR op, no Lean definition, and no
proof changed.

### The gate (done)

`fai gate` (`projbench.py gate`, [benchmarks/projects/README.md](../../benchmarks/projects/README.md#the-gate))
is the first of the [improvements outside the tracks](#improvements-outside-the-tracks), made
when step 4 showed what its absence cost: a change that failed its tests was kept on
judgment. It builds Lua and SQLite, checks their behavior, counts every workload's
instructions, and compares with the tracked baseline `gate.json`: PASS or FAIL. Tried on what
this round has: it passes the tree as it is, three times with the same numbers, fails step
4's change (more instructions on every Lua workload), and fails the promotion pipeline (`--configs fcc-promo`: `lvm.c` does not compile in the
time allowed, and with `--plain lvm` several times `-O`'s instructions).

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
  floats), the `poison` op gives one value of that type without changing the core, and bytes
  never written (an empty map) read as its encoding. That a newly made slot has no bytes
  under its id is not proved: it is P2's.

These are single ops under hypotheses the simulation will have to supply (`Quiet`, and where
each pointer points). They say nothing yet about a program.

## Not in this round

- JIT, VM embedding, Wasm, GPUs, a second frontend, floats on x86-64, an object writer.
- Module composition and `Decided` (obligation 3), scalarization and `cf.try` lowering
  (obligation 4), instruction selection against ISA semantics (obligation 6): the round's
  theorem is at the other passes' bar, one function in a fixed module with a `Decided` source.
- `stackdce`'s proof.
