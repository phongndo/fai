# Compiler experiments: propose, test, measure

This is how to try a change to the compiler (a new pass, a different pipeline, a change to a
pass, a backend, or the lowering) and find out whether it is correct and whether it helps,
without changing any tracked file (Safety lists exactly what it writes). It is written for agents as much as for people:
every step is one command, every result is a file, and every verdict says what it rests on.

## The loop

```sh
nix develop                                       # or prefix each command with `nix develop -c`

# 1. Measure one module, to see what a pipeline does to it (JSON on stdout).
cargo run --release --bin fir -- measure tests/fir1/noalias.fir --passes mem2reg,dce --experimental

# 2. Run the experiment: measure the whole corpus against a baseline, then gate it.
cargo xtask experiment promo --passes mem2reg,stackdce,fwd,copyprop,dse,dce --experimental
cargo xtask experiment my-fwd-change --baseline-rev main        # a code change: this tree vs main

# 3. Read target/experiments/NAME/report.md (or report.json). Exit 1 means REJECTED.

# 4. Before anything lands: the required check, which knows nothing of experiments.
cargo xtask verify full
```

A quick look without the gate (seconds instead of minutes) is `--gate none`; its verdict says
`UNGATED`, and it is not evidence that the change is correct beyond the corpus's own runs.

## What an experiment does

`cargo xtask experiment NAME` (`xtask/src/experiment.rs`) compares a **candidate** (this working
tree, committed or not, with `--passes …`, `-O` by default) with a **baseline** (this tree, or
the tree at `--baseline-rev REV` in a temporary git worktree with its own target directory, with
`--baseline-passes …`, `-O` by default).

1. **Measure.** `fir measure` (`tools/fir/measure.rs`) prepares each `.fir` module under
   `tests/` (not the `errors/` corpora) as `fir compile` would, and counts:

   | Metric | What |
   |---|---|
   | `ops.executed` | ops the interpreter dispatched running the prepared MFIR on the file's `// run:` lines: the primary metric, a deterministic proxy for run time |
   | `mem.executed`, `calls.executed` | the `mem.*` and `func.call*`/`func.invoke*` part of that |
   | `ops.static` | ops in the prepared MFIR |
   | `aarch64.insns`, `x86_64.insns` | instructions each backend emits (AArch64 as Linux ELF on every host) |

   Every count is the same on every host and every run, so a difference is the change's, not
   noise; executed counts are compared only where both sides measured the same runs, and only
   over runs whose source is defined (the optimizer may do anything after UB). Wall time
   (`prepare.us`) is recorded and never compared. For timings on real hardware, see the
   benchmarks (`benchmarks/`), which are a separate track.

2. **Check each run.** Every candidate run must refine the source module's run (the same line;
   when the source is UB, stuck, or out of fuel, the source's events first; allocation numbers
   renumbered when `stackdce` runs: the definition `tests/rust/opt.rs` uses), and the source must
   print what the `// run:` line expects. A module the baseline prepares and the candidate
   doesn't is a failure; one neither prepares (LFIR inputs, lowering limits) is listed, not
   measured. A backend that newly refuses a module is reported as a regression.

3. **Gate** (`--gate quick`, the default). The differential suites run in release with the
   candidate's pipeline (`FIR_PASSES`) and `FIR_REQUIRE_FULL=1`: `opt` (every fixture, `--fuzz`
   random programs, 200 by default, and the memory programs, each optimized run refining the
   original's), `aarch64` and `x86_64` (fixtures and random programs compiled with the pipeline
   and run natively or under qemu, compared with the interpreter and, for the fixtures, the Lean
   reference). The evidence each suite writes must show it tested the candidate's pipeline,
   skipped nothing, failed nothing, and ran the configured number of programs.

4. **Report** `target/experiments/NAME/report.{md,json}`, with each module's measurements under
   `baseline/` and `candidate/` and the gate's logs and evidence under `gate/`.

### Verdicts

| Verdict | Means | Exit |
|---|---|---|
| `REJECTED` | a run didn't refine its source, a module stopped compiling, the gate failed, or the harness couldn't run | 1 |
| `IMPROVED` | no metric got worse, at least one got better, no new backend refusals | 0 |
| `REGRESSED` | the primary metric got worse, or nothing got better while something got worse | 0 |
| `MIXED` | some metrics better, some worse, the primary not worse | 0 |
| `NO CHANGE` | every total is the same | 0 |

The `eligibility` line says what backs the candidate's passes. A pipeline with an experimental
pass (`mem2reg`, `stackdce`: unproved) is **not eligible for the default `-O` pipeline**,
whatever it measures: `-O` holds only passes whose rewrite relation has a Lean refinement proof
(`compiler/transforms/src/lib.rs`, `Assurance`). Passing an experiment is evidence on this
corpus and these random programs, in the interpreter and on the hosts it ran on; it is not a
proof, and nothing here connects a measurement to the Lean theorems.

## Safety

* Nothing tracked is written, and nothing outside build outputs: the report, both measured
  `fir` binaries (copied, so a concurrent build can't swap one mid-run), and the gate's logs and
  evidence go to `target/experiments/NAME/`; the candidate builds where cargo builds
  (`target/`, or `$CARGO_TARGET_DIR`), the baseline in `target/experiments/.baseline-target`,
  both `--locked`; the gate's suites write their scratch files under `target/tmp/`, and its
  `lake build` updates `spec/.lake/` (a no-op when the Lean build is current). A baseline
  revision is checked out as a git worktree in `target/experiments/NAME/baseline-tree`, which
  registers it in the repository's shared git metadata until the experiment ends and removes
  it (a warning says so if it can't); a killed run's registration is reclaimed by the next run
  of the same experiment (`git worktree add -f` on that path only). No other worktree's
  registration is touched.
* The variables that weaken checks (`FIR_REF`, `FIR_FUZZ`, `FIR_CC`, …: `CLEARED` in
  `xtask/src/main.rs`) are cleared for every child; the gate sets only what it means to.
* The candidate's tree is identified by revision, whether it is dirty, and a hash of its diff
  and of every untracked file's name and contents (an unreadable one is an error), so a report
  can't be mistaken for one of another tree. Each binary measured is the one cargo reports
  building (wherever a configured target puts it), copied while a lock keeps another
  experiment's build out of that target directory.
* Every record `fir measure` prints is validated (a pipeline; an error or runs and every
  metric; a count or a refusal per backend; run problems matching the runs and the exit code),
  so a broken measurement rejects the experiment instead of shrinking the comparison.
* The gate requires each suite's evidence from this run, with no skips or failures, the
  candidate's pipeline, the configured number of random programs, and more than zero
  comparisons; on macOS a declared host gap stands in for a suite's work only after those
  integrity checks.
* A module either side can't measure at all (`fir measure` crashing, or exiting other than 0
  or 1) rejects the experiment: it can't silently drop out of the comparison. One that neither
  side can *prepare* (LFIR inputs, lowering limits) is listed as unmeasured.
* The gate tests exactly the pipeline measured: every suite runs `FIR_PASSES` to a fixed point,
  as `fir measure` does, and records it; `--none` (no passes) can only be measured.
* `cargo xtask mutate experiment-rejects-a-miscompile` plants a miscompile (forwarding a store to
  a load through a *different* pointer) and requires the experiment to reject it, so the harness
  is itself tested the way the other checkers are (`docs/assurance/adversarial.md`).

## On CI

`.github/workflows/experiment.yml` runs an experiment on demand on both native hosts (x86-64
Linux and Apple-silicon macOS) and uploads each report:

```sh
gh workflow run experiment.yml --ref BRANCH -f name=promo -f passes=mem2reg,stackdce,fwd,copyprop,dse,dce -f experimental=true
```

The counts are host-independent, so the two reports should agree on every metric; what differs
is the gate, which runs what each host can (below).

## What runs where

`cargo xtask verify full` runs on both hosts in CI (`.github/workflows/verify.yml`), and
`cargo xtask matrix REPORT.json…` puts their reports side by side.

| | x86-64 Linux | Apple-silicon macOS |
|---|---|---|
| Lean build, generated files, proof audit, fmt, clippy, ruff, ty | yes | yes |
| interpreter, optimizer, lowering, text, contracts, DCE checkers (all suites without native code) | yes | yes |
| AArch64 backend: fixtures and random programs | under qemu-user (Linux ELF) | **natively** (Mach-O), except what the backend declares unsupported on macOS (variadic functions, composites passed on the stack), counted per reason |
| x86-64 backend: fixtures and random programs | **natively** | no: host gap (Linux ELF; qemu-user is Linux-only) |
| ABI torture test (AAPCS64 against the C compiler) | under qemu-user | no: host gap (it checks Linux's AAPCS64) |
| Debug lines (DWARF line tables) | assembled by GNU as (cross) | assembled by LLVM's assembler for Linux ELF |
| register-allocation review regressions | under qemu-user | **natively** (Mach-O) |
| C API programs, and under AddressSanitizer | yes | yes |
| C API end to end, native half | under qemu-user | no: host gap (`tests/capi/e2e.c` builds Linux ELF) |
| fcc's C corpus (AArch64 and x86-64) | yes (x86-64 natively) | no: host gap (fcc targets Linux) |
| Verdict | `FULL VERIFICATION PASSED` | `HOST VERIFICATION PASSED ON aarch64-macos` (never "full") |

Nothing in CI runs AArch64 *Linux* code natively: on x86-64 Linux it runs under qemu-user, and
macOS runs AArch64 as Mach-O. A native AArch64 Linux runner would close that gap.
