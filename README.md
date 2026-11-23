# fai

fai is a compiler built as libraries, around one IR, FIR, whose semantics is defined in Lean.
Every op means what `spec/` says it means. The Rust compiler is checked against that
definition, by proofs where there are proofs, by proved checkers, and otherwise by differential
tests. [docs/assurance/README.md](docs/assurance/README.md#guarantees) records exactly which
applies to each part.

## Status

The first phase is the ahead-of-time compiler. Here is what exists:

- **FIR in three layers.** HFIR is built by frontends, MFIR is the optimizer's level, and LFIR is
  a target's instructions. FIR has a text format, a verifier, a builder API (in Rust and in C),
  and a reference interpreter that agrees with Lean's (`fir-ref`).
- **Passes.** The `-O` pipeline (dse, fwd, copyprop, dce) holds only passes with Lean
  refinement proofs. A proved Lean checker can check every DCE step of a compilation on request
  (`--check-dce`); by default, an unproved Rust transcription of it, tested against it, checks
  every DCE step's output. `mem2reg` and `stackdce` are experimental: they are unproved and run only
  when a pipeline opts in (`--experimental`).
- **AArch64 backend.** It compiles MFIR through the `aarch64` LFIR dialect to Linux ELF or
  macOS Mach-O, and checks the register allocation on every compile.
- **x86-64 backend.** It compiles the integer subset of MFIR to Linux ELF. It has no LFIR
  dialect or Lean semantics yet.
- **fcc.** A C compiler built on Clang's front end, going through the C API only. It targets
  AArch64 Linux, and x86-64 Linux for integer programs.

None of this is a stable interface yet.

## Layout

| Directory | What |
|---|---|
| `compiler/` | the compiler as crates: `ir`, `interp`, `lowering`, `transforms`, `codegen`, `driver` |
| `targets/` | backends: `aarch64`, `x86_64` |
| `sdk/` | interfaces: `rust` (the `fir` crate), `c` (`fir-capi`, header `sdk/c/include/fir.h`) |
| `frontends/c/` | fcc |
| `tools/` | commands: `fir/`, the `fir` command (FIR); `fai/`, the `fai` command (`fai verify`, `fai experiment`, …) |
| `spec/` | Lean: semantics, proofs, op declarations, the reference tool, generators, the proof audit |
| `tests/` | `.fir` and C API corpora; `tests/rust/`, the cross-component suites |
| `benchmarks/` | `c/`: fcc against GCC and Clang; `rust/`: library timing |
| `docs/` | [architecture](docs/architecture.md), [design](docs/design/), [assurance](docs/assurance/), [performance](docs/performance/) |
| `nix/` | the development environment |

[docs/architecture.md](docs/architecture.md) has the crates, what depends on what, and where
each layer and each generated file lives.

## Getting started

Everything runs in the dev shell. It provides the same toolchain on x86-64 and AArch64 Linux
and on Apple-silicon macOS:

```sh
nix develop
cargo run --bin fir -- run tests/fir0/loops.fir @countdown 5   # interpret a function
cargo run --bin fir -- compile FILE.fir -O -o out              # --target x86_64 for x86-64
cmake -S frontends/c -B build/fcc -G Ninja                     # fcc: configure,
cmake --build build/fcc                                        # and build
fai verify quick                                               # after every edit: under a minute; says what it left out
fai accept                                                     # the required check (CI): verify full, the gate, the old tests
fai status                                                     # which verdicts are of the tree as it is now
fai experiment NAME --passes P,Q [--experimental]              # propose, test, and measure a change
fai help                                                       # every `fai` command
```

`fai` is the repository's own command (`tools/fai`): the dev shell builds and runs it from the
checkout you're in, and `cargo fai …` does the same anywhere cargo runs. `cargo xtask …`, its
old name, still works.

### Checking a change

No verdict here is read from output and judged: each is one command with an exit code.

| Command | Time | Says |
|---|---|---|
| `fai verify quick` | under a minute once Lean is built | `QUICK PASSED: not a verification`, or what failed. Everything but the three C corpus tests, most of the ABI test's random signatures (20 run), the release build, the sanitizer run, and the check that no test skipped work; what it left out is printed, and the named tests never vary |
| `fai accept` | about 8 minutes | `accept: PASS` (0), `FAIL` (1), `NOT JUDGED` (2: a part could not run, or the tree changed meanwhile), or `PASS, JUDGING FILES CHANGED` with the files (3). It runs `fai verify full` and `fai gate`, and, when the change edits or removes tests that existed at the base, those tests **as they were** against the changed code. On a host that can't run everything (the gate needs one that isn't AArch64) the best it says is `HOST PASS ON host` |
| `fai status` | a second | whether the last `verify full` and the last `gate` of `fcc -O` are of the tree as it is now and passed (`CURRENT`, exit 0), or not (`STALE`, `NOT VERIFIED`, exit 1). A `quick` or `fast` run doesn't change the answer. On AArch64, where the gate can't run, `CURRENT` means verification alone, and says so |
| `fai judging` | a second | the tests, baselines, and checkers the change touches, against the merge base with `origin/main` |
| `fir check FILE --target aarch64 [-O]` | a moment | whether `fir compile` (with `-O`, if given) will accept a module, in the words it would use |

A change that fails its test is taken out, not kept with an explanation. A change that can
only pass by editing what judges it (a test, a baseline, a checker) says so: `fai accept` exits
3 and names the files, and merging is the owner's yes. The parts are also commands of their
own: `fai verify fast|full`, `fai gate` (Lua and SQLite, right and no worse than the accepted
baseline), and `fai mutate` (the checkers checked against planted defects).

[frontends/c/README.md](frontends/c/README.md) covers fcc,
[docs/assurance/README.md](docs/assurance/README.md) covers what `verify full` requires, and
[docs/experiments.md](docs/experiments.md) covers experiments and what CI runs natively on
x86-64 Linux and on Apple-silicon macOS.

## License

Apache-2.0 ([LICENSE](LICENSE)).
