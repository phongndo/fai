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
  (`--check-dce`). `mem2reg` and `stackdce` are experimental: they are unproved and run only
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
| `tools/fir/` | the `fir` command |
| `spec/` | Lean: semantics, proofs, op declarations, the reference tool, generators, the proof audit |
| `tests/` | `.fir` and C API corpora; `tests/rust/`, the cross-component suites |
| `benchmarks/` | `c/`: fcc against GCC and Clang; `rust/`: library timing |
| `docs/` | [architecture](docs/architecture.md), [design](docs/design/), [assurance](docs/assurance/), [performance](docs/performance/) |
| `xtask/`, `nix/` | verification and development environment |

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
cargo xtask verify fast                                        # local; says what it skipped
cargo xtask verify full                                        # the required check (CI)
```

[frontends/c/README.md](frontends/c/README.md) covers fcc, and
[docs/assurance/README.md](docs/assurance/README.md) covers what `verify full` requires.

## License

Apache-2.0 ([LICENSE](LICENSE)).
