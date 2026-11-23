# Plan: the verification round

[06-plan.md](06-plan.md) is about what the compiler produces: faster code, and promotion
proved. This plan is about the environment that work happens in: whether an agent can find
out, quickly and without judgment, that a change is right, and whether that answer can be
trusted. It comes from 06's steps 1 to 6, where the environment failed in these ways:

| What happened | What it shows |
|---|---|
| The selector change (`ab20520`) passed only after two test fixtures were edited, and no check said so | A change can move what judges it |
| A change that failed its three tests was kept for one revision. `fai gate` now rejects it, and nothing checks that the gate still would | The checkers of speed are not themselves checked |
| `target/projbench-gate/gate-report.json` says `PARTIAL`, left by a trial run, and names no revision | A report can't be matched to a tree |
| The first gate failed the unchanged tree, because Lua seeded its hashes from the clock | A verdict has to repeat |
| The allocation validator ran 4.5 minutes and 7.5 GiB on one file before it was killed | A checker can hang where it should refuse |
| `fai verify full` took 372 s at its last run, and the gate about five minutes more | There is no tier that answers in seconds |
| Checked `i64` addition verifies as MFIR, and selection then refuses it | A layer's verifier doesn't promise that the next stage accepts |
| The lowering test skips the functions whose signatures lowering changes | The unproved part of lowering is the part not compared |

Nothing here changes what an op means, adds a layer, or adds a proof. Those stay in 06.

## The rule

06's rule holds: a step's test decides, and a change that fails it is taken out. This plan adds:

1. **In stages A to C, every test is a command with an exit code, or an entry in
   `fai mutate`.** None is "read the output and judge". Stage 0's tests are tables, because
   probes measure.
2. **A step says beforehand which judging files it will change** (the Moves column below). A
   change to any other judging file fails the step.
3. **Every number is measured or marked a target.** The targets are fixed or dropped by the
   probes in stage 0.

**Judging files** are the files that decide whether other changes pass: tests with their
fixtures and expected outputs; baselines and locks (`benchmarks/projects/gate.json`,
`docs/assurance/proofs.lock.json`, `spec/Audit/Claims.lean`); and the checkers (`tools/fai/src`,
the gate in `projbench.py`, the CI workflows, the verifiers, `regcheck`). The name is not "the
oracle" because the semantics already has one.

## The owner's decisions

None is decided here, and `decisions.md` is not touched.

1. **The two fixture edits in `ab20520`.** `tests/rust/debug_lines.rs` now locates the add at
   `@10:4`, and `tests/rust/regcheck.rs` uses constants that still need their own instructions,
   because a constant no longer gets a register of its own. Recommended: accept, and when
   step 16 lands, also run the original fixtures with laziness off, which shows what they
   tested still holds. Until this branch merges, step 5 lists both files in every verdict.
2. **`fai accept` in CI.** Recommended: yes, as its own Linux job. It fetches Lua and SQLite,
   so `fai verify full` stays offline and unchanged.
3. **What a fact's trust level means.** Selection drops `assume`, `check`, and `proved` alike.
   Recommended: record them as advisory now, and make `check` a real check when a pass first
   relies on a fact.
4. **A hole of an empty composite** (step 15). Lowering drops it today. Recommended: the HFIR
   verifier refuses it, which rejects programs it accepts now. The alternative is to carry the
   hole through lowering at some scalar type.
5. **Where target legality lives** (step 14). Recommended: one Rust predicate first, shared by
   the check and by selection. [layers-as-built.md](layers-as-built.md) proposes generating it
   from Lean, as the op contracts are; that can follow when a proof needs it.
6. Carried from 06: the `bN` argument question, and the decision log's "Next round" row.

## Done when

1. **One command.** `fai accept` ends, for any tree, in one of four lines with four exit codes:
   `PASS` (0), `FAIL` (1), `NOT JUDGED` (2), `PASS, JUDGING FILES CHANGED` (3, with the files).
2. **Bound to the tree.** `fai status` says, for the tree as it is now, which verdicts hold, and
   says `STALE` after any edit.
3. **The checkers are checked.** `fai mutate` catches, besides today's 28: a slowdown of about
   1%, a weakened gate, a dropped judging path, a scalarization error made the same way in Lean
   and Rust, a lazy value built from a stale operand, and a validation over its budget.
4. **A tier in seconds.** A quick tier runs in at most 60 s warm (target, fixed by step 1),
   names what it skipped, and its report gives how many planted defects it catches. If
   checkpoint 3 cancels the tier, this item is reported missed, with `fast`'s measured time.
5. **The allocation validator can't hang.** It is bounded by counted work, so the same tree
   gets the same refusal on every host. The gate's own limits stay in seconds.
6. **One MFIR.** Over the fixtures, the random programs, and the C corpus, a module that
   verifies as MFIR and passes `fir check --target aarch64` is never refused by selection.

## Steps, in order

Numbers are this plan's; 06's are written "06's step 7".

### Stage 0: probes

Small, and they change no tracked file but this plan's Progress. They fix the targets above
and may shrink a later step to a `fai mutate` entry.

| # | Step | Test |
|---|---|---|
| 1 | **Time the loop.** A warm `fai verify fast`, and each debug suite alone | a table of seconds per suite that adds up to within 10% of the whole |
| 2 | **Plant three defects by hand** in a scratch copy, and record whether today's checks catch each, by which command, in how long: (a) a scalarization error made the same way in `Lower.lean` and `lower.rs`; (b) a lazy compare built after the moves into block parameters; (c) one selection rule turned off, sized to cost about 1% on Lua | a row per defect: caught or not |
| 3 | **Measure the judging line on history.** Step 5 fixes what it must name. This probe settles only the exemption for added tests (a new test file; lines only added to one) and how often the line would have fired | which of this branch's commits and how many of main's it flags, with and without the exemption |
| 4 | **What the gate needs inside `fai mutate`.** The copy under `target/mutate/tree` holds tracked files only: no `.git`, no fetched sources | time and disk for building `fcc` there and running the gate twice; whether Lua alone fails defect (c) |

### Stage A: verdicts that can't be fooled

| # | Step | Test | Moves |
|---|---|---|---|
| 5 | **The judging line.** `fai judging [--base REV]` lists every judging file a change adds, edits, or removes, from `git diff` against the merge base with `origin/main`, never from a file a change can write. Only added tests are exempt. `verify`, `gate`, and their reports carry the line. Without git or a base it reads "no base" and changes no other exit code. Merging is the owner's yes | with `--base origin/main` at `313855a` it names exactly the seven files in [Progress](#progress) and exits 3; on a commit that only adds a test file it exits 0; a `fai mutate` entry that drops `tests/` from the list is caught by a unit test of the path list, which needs no git | `tools/fai/src`, `mutate.rs` |
| 6 | **Reports bound to the tree.** Every report records a content hash of the tree (tracked and untracked files, by `git write-tree` on a temporary index, so a dirty tree has an identity), the base revision, the configuration, and for the gate the baseline's hash. `fai status` compares them with the tree as it is | after a gate run `fai status` exits 0; after one byte is appended to a tracked file it prints `STALE` and exits 1; with the byte removed it exits 0 again; a `--plain` run never shows as a pass | `tools/fai/src`, `projbench.py` |
| 7 | **The gate is checked.** `projbench.py gate --self-test` feeds the comparison made-up measurements (equal, 1% more instructions, wrong behavior, a missing workload, a partial build), and `fai verify` runs it. `fai mutate` gains `slower-code` (defect (c): the gate must fail and name a workload) and `gate-tolerance-widened` (the self-test must fail) | both entries caught; the self-test under 5 s (target) | `tools/fai/src`, `mutate.rs`, `projbench.py` |
| 8 | **A budget for the allocation validator.** `regcheck::validate` counts its work (values joined) and refuses over a bound: "not validated: over budget in `@f`", which fails the compile. Making it scale stays 06's step 7 | `fcc-promo` on `lvm.c` ends in that refusal within 60 s and 1 GiB (targets), where it ran 4.5 minutes and 7.5 GiB; `fai gate` still passes, so `-O` never meets the bound; the corpus's verdicts and messages are identical (the differential run of [compile-speed.md](../performance/compile-speed.md)); a `fai mutate` entry that removes the bound is caught | `regcheck.rs`, `mutate.rs` |

### Stage B: one command, in tiers

| # | Step | Test | Moves |
|---|---|---|---|
| 9 | **`fai accept`**: `verify full`, the gate, and the judging line, with one last line. A host that can't run a part reports a host pass, as `verify full` does for its declared gaps, and never `PASS`. In CI, 0 and 3 pass the required check, and 3 puts its list at the top of the job summary | four scratch trees, each with `--base` set to the commit it was made from, give the four exit codes: unchanged 0, defect (c) 1, no baseline 2, an edited fixture 3; a `fai mutate` entry that makes it ignore the gate is caught | `tools/fai/src`, `mutate.rs`, CI if decision 2 is yes |
| 10 | **The quick tier**, if step 1 shows a warm `fast` over 90 s. `fai verify quick` picks suites by the paths changed and prints `QUICK PASSED: not a verification` with what it skipped | at most 60 s warm (target); run over `fai mutate`'s copies, its report gives how many planted defects it catches | `tools/fai/src` |
| 11 | **A gate failure names functions.** The baseline gains instruction counts per function for those over 1% of a workload, and `FAIL` lists the five that rose most. The counts explain a failure and never decide one: the verdict stays on each workload's total | with 06's rejected step 4 applied (`bc57886`) in a scratch worktree, the failure lists `luaV_execute` (expected to be first; not yet measured) | `gate.json` (new fields), `projbench.py` |

### Stage C: the IR and its boundaries

| # | Step | Test | Moves |
|---|---|---|---|
| 12 | **The lowering test compares what lowering changes.** `tests/rust/lower.rs` drops a `// run:` line without a word when its arguments don't parse at both layers. Encode the arguments as the lowered signature takes them, and report skips as evidence | skipped runs go from step 2's count to 0, or each has a named reason; `fai mutate` gains defect (a), caught | `tests/rust/lower.rs`, `mutate.rs`, required evidence |
| 13 | **The MFIR verifier accepts only what lowering produces.** Outside HFIR, composites are legal only where calls pass them whole, in both verifiers | a struct-valued `cf.if` and composite loop state are refused by `fir check` and `fir-ref check` with the same message; every lowered fixture still verifies | `Verify.lean`, `verify.rs`, the proof lock, generated files, new error fixtures, and any MFIR fixture that relied on it (named in the commit) |
| 14 | **`fir check --target aarch64`.** One legality predicate, used by the check and by selection for its refusals (where it lives is decision 5) | over the fixtures, random programs, and the C corpus, the check accepts exactly when selection doesn't refuse; `int.add.overflow.s` on `i64` is refused at the check, naming the op and the width | `isel.rs`, `tools/fir`, a new test |
| 15 | **A hole of an empty composite**, as the owner decides (decision 4). Lowering drops it, so a run that stops at the hole in HFIR goes on in MFIR | if refused: the gap's fixture is refused by both verifiers; either way, any run ending `hole ?h` in HFIR ends so after lowering | `Verify.lean`, `verify.rs`, the proof lock, one fixture |
| 16 | **Lazy values, stated and tested.** A selector option turns laziness off (a register per value, as before `ab20520`). A test compares both ways on the fixtures and random programs, and [layers-as-built.md](layers-as-built.md) says what `freeze` now rests on: a value built again depends only on constants, `sp`, and registers written once | the two ways give the same outcomes; `fai mutate` gains defect (b), caught; the gate's numbers are unchanged | `isel.rs`, a new test, `mutate.rs`; and `tests/rust/debug_lines.rs` and `tests/rust/regcheck.rs` if decision 1 brings the original fixtures back |
| 17 | **Facts**, as the owner decides (decision 3) | if advisory: the docs say so and nothing else changes | the owner's |

## Checkpoints

1. **After stage 0.** Where a probe shows today's checks already catch a defect, the step that
   was to close that gap becomes its `fai mutate` entry and nothing more.
2. **After stage A.** `fai mutate` catches everything, with the new entries. From here 06's
   steps 7 and 8 are judged by verdicts that name fixture edits, can't go stale, and can't hang.
3. **After stage B: Done when 1 to 5.** If the quick tier can't reach two minutes warm while
   catching at least half the planted defects (both targets), it is not built: `fast` stays
   the inner loop, and the time goes to running suites in parallel.
4. **After stage C: Done when 6.**

## How this fits 06

- Stages 0 and A come before 06's steps 7 and 8. They are small, and step 8 here is what keeps
  06's step 7 from hanging on its own test.
- Stage B can run beside 06's steps 7 and 8: it touches `tools/fai` and the harness, and they
  touch `regalloc.rs` and `regcheck`.
- Stage C doesn't block 06's checkpoint 1. Steps 13 to 15 change the Lean verifier, so they
  go in one at a time, each through `fai accept`.

## Parked, each with what starts it

| What | Starts when |
|---|---|
| Refinement through a value encoding, and module refinement (definitions in Lean) | step 12 finds a scalarization bug, or someone begins that proof |
| Behaviors for LFIR and "LFIR implements MFIR" in Lean | 06's step 11 (the validator proved), which can't be stated without it |
| Field paths recovered from lowered MFIR | 06's checkpoint 1 passes: promotion is its only user |
| A resource-exhaustion outcome | Lua's deep-recursion tests still overflow after 06's step 8 shares slots |
| Lowering's names that can clash with the source's | a real program hits it (today it is refused, not miscompiled) |
| Selection split into legalization and selection | x86-64 work resumes and needs the same rules |
| Source lines in a gate failure | step 11 is in, and function names prove too coarse |

## Not in this plan

- Proofs, and anything that makes code faster: 06's tracks.
- Run time on hardware in the gate: it needs the AArch64 Mac.
- New targets, frontends, or ops.

## Progress

Nothing is started. Measured already, at `313855a`:

| What | Measured |
|---|---|
| `fai verify full`, last run | 372 s: debug tests 196 s, Lean from scratch 86 s, release tests 86 s, everything else under 5 s |
| Inside the debug tests | the C corpus suite 101 s, the AArch64 native suite 32 s, three others 11 to 14 s each |
| `fai gate` | about five minutes; the same numbers on five runs of one tree |
| `fai mutate` | 28 planted defects, all caught; none is a slowdown, and none tests the gate |
| Judging files this branch changed (seven) | `tests/rust/debug_lines.rs`, `tests/rust/regcheck.rs`, `benchmarks/projects/gate.json` (new), `benchmarks/projects/projbench.py`, `spec/Audit/Claims.lean`, `docs/assurance/proofs.lock.json`, `tools/fai/src/main.rs` |
| The copy `fai mutate` works in | tracked files only: no `.git` |
