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
the gate in `projbench.py` with the harness and plugin it uses, the CI workflows, the proof
audit, the verifiers, `regcheck`). The list is `tools/fai/src/judging.rs`. The name is not "the
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
   Step 3 found that half of all commits edit a test file, so 3 is for a change that fails
   the tests as they were, or that edits a baseline or a checker; an edit to a test that the
   old tests don't need is listed and passes.
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
| 2 | **Plant three defects** in `fai mutate`'s copy, and record whether today's checks catch each, by which command, in how long: (a) a scalarization error made the same way in `Lower.lean` and `lower.rs`; (b) a lazy value built in one block and used in another that the first doesn't lead to (the first wording, a compare built after the moves into block parameters, can't happen: the moves are in blocks of their own, after the branch); (c) one selection rule turned off, sized to cost about 1% on Lua | a row per defect: caught or not |
| 3 | **Measure the judging line on history.** Step 5 fixes what it must name. This probe settles only the exemption for added tests (a new test file; lines only added to one) and how often the line would have fired | which of this branch's commits and how many of main's it flags, with and without the exemption |
| 4 | **What the gate needs inside `fai mutate`.** The copy under `target/mutate/tree` holds tracked files only: no `.git`, no fetched sources | time and disk for building `fcc` there and running the gate twice; whether Lua alone fails defect (c) |

### Stage A: verdicts that can't be fooled

| # | Step | Test | Moves |
|---|---|---|---|
| 4a | **Counts that don't depend on where the tree is** (found by the baseline run, below). A counted run starts in its work directory and names its program and script without a directory | the gate into two output directories whose names differ in length gives the same count for every workload and configuration; the baseline is then made again, by hand | `projbench.py`, `gate.json` |
| 5 | **The judging line.** `fai judging [--base REV] [--head REV]` lists every judging file a change adds, edits, or removes, from `git diff` against the merge base with `origin/main`, never from a file a change can write; without `--head` it reads the working tree, untracked files included. Only new test files are exempt. `verify`, `gate`, and their reports carry the line. Without git or a base it reads "no base" and changes no other exit code. Merging is the owner's yes. It is information, not the alarm (step 3): the alarm is step 9's | with `--base origin/main --head 313855a` it names exactly the eight files in [Progress](#progress) and exits 3; on a commit that touches none it exits 0; a `fai mutate` entry that drops the tests from the list is caught by a unit test of the list, which needs no git | `tools/fai/src`, `mutate.rs` |
| 6 | **Reports bound to the tree.** Every report records a content hash of the tree (tracked and untracked files, by `git write-tree` on a temporary index, so a dirty tree has an identity), the base revision, the configuration, and for the gate the baseline's hash. `fai status` compares them with the tree as it is | after a gate run `fai status` exits 0; after one byte is appended to a tracked file it prints `STALE` and exits 1; with the byte removed it exits 0 again; a `--plain` run never shows as a pass | `tools/fai/src`, `projbench.py` |
| 7 | **The gate is checked.** `projbench.py gate --self-test` feeds the comparison made-up measurements (equal, 1% more instructions, wrong behavior, a missing workload, a partial build, the baseline's update), and `fai verify` runs it. `fai mutate` gains `slower-code` (defect (c): the gate must fail and name a workload), and `gate-tolerance-widened`, `gate-passes-a-partial-build`, and `gate-baseline-moves-up` (the self-test must fail) | all four entries caught; the self-test under 5 s (target) | `tools/fai/src`, `mutate.rs`, `projbench.py` |
| 8 | **A budget for the allocation validator.** `regcheck::validate` counts its work (values read or written when states are joined, compared, or copied) and refuses over a bound: "not validated: over budget", which fails the compile. Making it scale stays 06's step 7 | `fcc-promo` on `lvm.c` ends in that refusal within 60 s and 1 GiB, where it ran 4.5 minutes and 7.5 GiB; `fai gate` still passes and the test suites still pass with every refusal's message unchanged, so no code that validates today meets the bound (the differential run [compile-speed.md](../performance/compile-speed.md) describes was done once and is not in the tree); a `fai mutate` entry that removes the bound is caught | `regcheck.rs`, `mutate.rs` |

### Stage B: one command, in tiers

| # | Step | Test | Moves |
|---|---|---|---|
| 9 | **`fai accept`**: `verify full`, the gate, and the judging files, with one last line. When a change edits or removes existing test files, it runs **the tests as they were at the base against the changed code**, in a copy: a change that passes them didn't need to move them, and one that fails them is named, with the tests. A host that can't run a part reports a host pass, as `verify full` does for its declared gaps, and never `PASS`. In CI, 0 and 3 pass the required check, and 3 puts its list at the top of the job summary | the verdict is a function of its parts, with a unit test for each of the four exit codes and their order (a `fai` binary judges only its own checkout, so four built trees would test the builds, not the verdict); `fai accept` on this branch exits 3 and names `tests/rust/debug_lines.rs` and `tests/rust/regcheck.rs` as tests the change fails as they were; a `fai mutate` entry that makes it ignore the gate is caught | `tools/fai/src`, `mutate.rs`, CI if decision 2 is yes |
| 10 | **The quick tier** (step 1: a warm `fast` is 212 s, so it is needed). `fai verify quick` leaves out the slow tests by name, the same ones every time, and prints `QUICK PASSED: not a verification` with what it skipped. Choosing by the paths changed was dropped: a fixed list can't miss a dependency | at most 60 s warm (target); its report gives how many of `fai mutate`'s planted defects its tests catch | `tools/fai/src` |
| 11 | **A gate failure names functions.** The baseline gains instruction counts per function for those over 1% of a workload, and `FAIL` lists the five that rose most. The counts explain a failure and never decide one: the verdict stays on each workload's total | with 06's rejected step 4 applied (`bc57886`) in a scratch worktree, the failure lists `luaV_execute` (expected to be first; not yet measured) | `gate.json` (new fields), `projbench.py` |

### Stage C: the IR and its boundaries

| # | Step | Test | Moves |
|---|---|---|---|
| 12 | **The lowering test compares what lowering changes.** A `// run:` line can only give scalar arguments, so a function with a union, slice, struct, or array parameter is never run by itself at either layer: only its callers are. Run each such function on generated values, in HFIR and, with the values encoded as the lowered signature takes them, in its lowering | every fixture function with a composite parameter is compared, and the count is evidence `verify full` requires; `fai mutate` gains defect (a), caught | `tests/rust/lower.rs`, `mutate.rs`, required evidence |
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

The owner said "execute", which is taken as a yes to the five recommendations above; each is
in a commit of its own, and none is written into `decisions.md`.

### Stage 0

| # | Result |
|---|---|
| 1 | **A warm `fai verify fast` takes 212 s**, 207 s of it the debug tests, whose suites run one after another: the C corpus suite 111 s, the AArch64 native suite 32 s, x86-64 14 s, lowering 12 s, the ABI suite 11 s, and nothing else over 6 s (204.6 s of suites in the 207.3 s check). Lean, the audit, and the static checks together take under 4 s when nothing changed. So the quick tier is needed, and it is the corpus and the random programs that it must leave out |
| 3 | **Half of all commits touch a judging file.** Of main's 228 commits the line would have fired on 113 (50%): 91 edit an existing test file, 33 a checker, 6 a baseline. Exempting new test files saves 17 commits (130 without). Counting a test file only when lines are removed or changed still fires on 102 (45%). On this branch it fires on 7 of 15 commits. So the line is information and can't be the alarm; step 9's alarm is the old tests run against the new code |
| baseline | **The gate's counts depended on the output directory's name.** The baseline run (same tree as the accepted baseline, another `--out`) counted 2.31% fewer instructions for lua-trees and 588 fewer for lua-strings. Lua keeps the script's path in each function, and its collector is paced by memory. Step 4a |

Steps 2 and 4 run with the steps that use them (7, 12, 16).

### Stage A

| # | Result |
|---|---|
| 4a | **Passed.** With every counted run started in its work directory, two gate runs into `target/pb-a` and `target/projbench-with-a-much-longer-name-for-this-test` counted the same instructions for all 8 workloads in both configurations, to the instruction |
| 5 | **Passed.** `fai judging --base origin/main --head 313855a` names the eight files below and exits 3; `--base 313855a --head 69137c8` (a commit of two plan files) exits 0; an unknown base exits 2. `fai mutate judging-list-drops-the-tests` is caught |
| 6 | **Passed.** `verify`, `gate`, `mutate`, and `accept` record the tree's hash at their start and end. After `fai accept`, `fai status` says `CURRENT` and exits 0; with one byte appended to `README.md` it says `STALE: verify, gate` and exits 1; with the byte removed, 0 again; the same with an untracked file added and removed. A gate run with `--update` is stale by its own doing: it changes the baseline, which is part of the tree |
| 7 | **Passed, but for `slower-code`, which is not built yet.** `projbench.py gate --self-test` makes 20 checks in well under a second, and `fai verify` runs it. `gate-tolerance-widened`, `gate-passes-a-partial-build`, and `gate-baseline-moves-up` are each caught by it |
| 8 | **Passed.** The budget is 4,096 units of work per input instruction and 2^29 in all. With `-O`, Lua and SQLite (2,376 validations) need at most 632 per instruction and 17.6 million in all, both for `luaV_execute`. With the promotion passes, `lvm.c` is refused in 4.75 s at 479 MB (it had passed 4 billion units after 100 s), and 13 of SQLite's functions need more than 4,000 per instruction (up to 169,774), so `sqlite3.c` no longer compiles with them either: 06's step 7 now has a number to get under. `.text` of both projects is unchanged, the gate passes, and `validator-budget-removed` is caught |

### Stage B

| # | Result |
|---|---|
| 9 | **Passed.** The verdict is a function of its parts, with unit tests for the four exit codes, their order, a host with gaps, and an edited test whose old version still passes. On this tree `fai accept` took about 7 minutes and ended `PASS, JUDGING FILES CHANGED`, exit 3: verification passed (16 checks), the gate was the same as its baseline, and the change **fails the tests as they were at the base**: `line_zero_escaped_file_names_and_modules_without_files` in `tests/rust/debug_lines.rs` and `corrupted_allocations_are_refused` in `tests/rust/regcheck.rs`, the two fixtures `ab20520` edited. The `fai mutate` entry is step 9's last part, below |

### Measured before the round

At `313855a`:

| What | Measured |
|---|---|
| `fai verify full`, last run | 372 s: debug tests 196 s, Lean from scratch 86 s, release tests 86 s, everything else under 5 s |
| Inside the debug tests | the C corpus suite 101 s, the AArch64 native suite 32 s, three others 11 to 14 s each |
| `fai gate` | about five minutes; the same numbers on five runs of one tree |
| `fai mutate` | 28 planted defects, all caught; none is a slowdown, and none tests the gate |
| Judging files this branch changed (eight) | `tests/rust/debug_lines.rs` (+4 -1), `tests/rust/regcheck.rs` (+2 -1), `benchmarks/projects/gate.json` (new), `benchmarks/projects/projbench.py`, `benchmarks/c/cbench.py` (the gate imports it), `spec/Audit/Claims.lean`, `docs/assurance/proofs.lock.json`, `tools/fai/src/main.rs` |
| The copy `fai mutate` works in | tracked files only: no `.git` |
