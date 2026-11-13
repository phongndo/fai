# Architecture: the crates, what depends on what, and where each layer lives

fai is a compiler built as libraries. Its IR, FIR, has one formal semantics in Lean (`spec/`).
The Rust compiler is a set of crates, each with one job, under `compiler/` and `targets/`. The
interfaces that programs use are in `sdk/`. The C frontend lives in `frontends/`.

This file describes the tree as it is. What is proved, checked, or only tested is described in
[assurance/README.md](assurance/README.md#guarantees), not here.

## The tree

```text
compiler/
  ir/           fai-ir          types and storage, the op table and op contracts (generated from
                                spec/), text format, verifier, builder, integer and float
                                semantics, the aarch64 dialect's vocabulary and AAPCS64 placement
  interp/       fai-interp      the reference interpreter: HFIR and MFIR, and LFIR on the AArch64
                                machine model
  lowering/     fai-lowering    HFIR → MFIR
  transforms/   fai-transforms  pass manager, observers and IR dumps, the proved -O passes, the
                                experimental passes, the bridge to the proved DCE checker
  codegen/      fai-codegen     what both backends share: global data, trap codes, may_throw
  driver/       fai-driver      lower → optimize (optionally DCE-checked) → MFIR for a target;
                                the list of components that declare op support
targets/
  aarch64/      fai-target-aarch64  isel to LFIR, register allocation and its check, emission
  x86_64/       fai-target-x86_64   the integer subset of MFIR to x86-64 Linux
sdk/
  rust/         fir             the Rust interface: re-exports the crates above
  c/            fir-capi        the C API (static and shared library; sdk/c/include/fir.h)
frontends/
  c/            fcc             C via Clang's AST, through the C API only (C++, CMake)
tools/
  fir/main.rs                   the `fir` command (a binary target of package fir)
spec/                           Lean: Fir (semantics, proofs, op DSL), Audit, fir-ref, generators
tests/                          .fir and C API corpora; rust/: the cross-component Rust suites
benchmarks/
  c/                            cbench and bench.py: fcc against GCC and Clang
  rust/                         timing examples for the library
docs/  xtask/  nix/
```

## Dependency direction

These edges are from `cargo metadata`. An arrow points at a dependency. No crate in `compiler/`
or `targets/` depends on `sdk/`, `tools/`, `frontends/`, or `tests/`.

```text
fai-ir               (no dependencies in the workspace)
fai-interp           → fai-ir
fai-lowering         → fai-ir
fai-transforms       → fai-ir
fai-codegen          → fai-ir
fai-target-x86_64    → fai-codegen, fai-ir
fai-target-aarch64   → fai-codegen, fai-interp, fai-ir
fai-driver           → fai-target-aarch64, fai-target-x86_64, fai-transforms, fai-lowering,
                       fai-interp, fai-ir
fir (sdk/rust)       → every crate above (it re-exports them); its targets are the `fir`
                       binary (tools/fir), the suites (tests/rust), the examples (benchmarks/rust)
fir-capi (sdk/c)     → fir
fcc (frontends/c)    links fir-capi's static library through CMake; no Rust dependency
xtask                → nothing in the workspace (it runs cargo, lake, clang, cbindgen)
```

`fai-ir`, `fai-transforms`, and `fai-target-aarch64` have one dev-dependency on `fir`. Their doc
examples are written against the supported interface, and Cargo allows this cycle because it
only applies to doctests. The two targets do not depend on each other.

## The layers in the code

HFIR, MFIR, and LFIR share one representation. A module's `Layer` (in `fai-ir`) says which
part of the one op table it may use, and each op's declaration says the layers it belongs to. So
the layers are values and table entries, not crates:

| Layer | Defined | Produced by | Run by |
|---|---|---|---|
| HFIR | the op table (`compiler/ir/src/generated/ops.rs`) | the builder, the text format, fcc | `fai-interp` |
| MFIR | the same table, the MFIR subset | `fai-lowering` | `fai-interp` |
| LFIR `aarch64` | the same table, the dialect's ops; vocabulary in `compiler/ir/src/dialect/aarch64/` | `fai-target-aarch64` (isel, then regalloc) | `fai-interp`'s machine model (`compiler/interp/src/aarch64_machine.rs`) |
| x86-64 machine code | not an LFIR dialect: no op-table entries, no Lean semantics | `fai-target-x86_64` | only natively, in the tests |

## Formal model, generated code, Rust, and checks

| Lean (`spec/`) | Generated or checked Rust | What keeps them together |
|---|---|---|
| `Fir/Syntax.lean`, `Fir/AArch64Syntax.lean`, `Fir/OpDSL.lean` (op declarations) | `compiler/ir/src/generated/ops.rs` (`lake exe gen-rust`), `builder.rs` (`gen-builder rust`), `sdk/c/src/generated/ops.rs` (`gen-builder capi`) | `cargo xtask verify` regenerates each one and fails on any difference |
| `Fir/DceKinds.lean` (`dcePerm`) and the op declarations | `compiler/ir/src/generated/contracts.rs` and `docs/assurance/op-contracts.json` | the same freshness check; `tests/rust/contracts.rs` checks the components' declarations against them |
| the registered claims (`Audit/Claims.lean`) | — | `lake exe fir-audit` against `docs/assurance/proofs.lock.json` |
| `Fir/Dce*.lean`, `fir-ref check-dce` (the proved checker) | `compiler/transforms/src/reference.rs` (the bridge to it), `--check-dce`, `FIR_CHECK_DCE` | `verify full` requires the C corpora's `-O` builds to be checked on both targets |
| `Fir/Interp.lean`, `Fir/AArch64Machine.lean` | `compiler/interp` | differential tests against `fir-ref run` |
| `Fir/Lower.lean` | `compiler/lowering` | differential tests against `fir-ref lower` |

Every pass carries an `Assurance` label in `fai-transforms`. Only passes labelled `Proved` may
be in the default `-O` pipeline. `mem2reg` and `stackdce` are `Experimental` and run only when a
pipeline opts in (`--passes … --experimental`). `fir opt --list-passes` prints each pass's
label.

## Interfaces

- **Rust:** `fir` (`sdk/rust`), version 0.1. It is not a stable API: its paths are the ones the
  code has always had (`fir::backend::{aarch64, x86_64, prepare, optimize}`, `fir::passes`,
  `fir::interp`, `fir::contract`, the root items), plus `fir::codegen` and `fir::dialect`. The
  `fai-*` crates are `publish = false` internals, and their public modules are not an interface.
- **C:** `fir-capi` (`sdk/c`). `FIR_API_VERSION` is 1.6, and the header is generated by
  cbindgen. Its only Rust dependency is `fir`.
- **C++:** there is no C++ SDK. One would sit beside the C API in `sdk/` and be built on it, as
  fcc is.

## Commands

| Command | Where | Built by |
|---|---|---|
| `fir` (run, check, fmt, opt, compile, lower) | `tools/fir/main.rs` | `cargo build` (package `fir`) |
| `fcc` (C compiler) | `frontends/c` | CMake, linking `libfir_capi.a` |
| `fir-ref`, `fir-audit`, `gen-rust`, `gen-builder` | `spec/` | `lake build` |
| `cargo xtask verify [fast\|full]`, `cargo xtask mutate` | `xtask/` | cargo |
| `cbench.py`, `bench.py` | `benchmarks/c` | python3 in the dev shell |

There is no `fcxx`. A C++ driver would be a frontend in `frontends/`, and its command would sit
beside `fcc`.

## Targets and hosts

- **AArch64:** `fir compile` emits Linux ELF or Darwin Mach-O. fcc emits Linux ELF only.
- **x86-64:** the integer subset of MFIR, Linux ELF only. Floats, variadic definitions,
  structs passed by value, and narrow arguments to C are refused, each with an error that names
  it.
- **Data layouts:** each backend refuses data layouts other than its ABI's.

| Host | Runs AArch64 code | Runs x86-64 code | Timing |
|---|---|---|---|
| x86-64 Linux (CI runs `verify full` here) | under qemu-user (emulated) | natively | x86-64 only; cbench timing does not run |
| Apple-silicon macOS | natively, as Mach-O; Linux binaries only in a Linux VM | no | native AArch64 |
| AArch64 Linux, including a VM on Apple silicon | natively (virtualized, not emulated) | under qemu-user | native AArch64 (cbench `time`) |

Emulated runs count as correctness evidence and as instruction counts (cbench `count`, recorded
as emulated). They never count as timing: cbench `time` refuses to run under emulation.

## Deviations from the suggested layout

- **No `compiler/analysis/`.** No analysis stands alone yet. `may_throw` is shared only by the
  backends, so it lives in `fai-codegen`. Use lists are part of `fai-ir`'s storage.
- **The aarch64 dialect's vocabulary is in `fai-ir`, and its machine model is in `fai-interp`.**
  One generated `OpKind` covers all three layers. The machine model runs inside the
  interpreter, sharing its memory model, and both need AAPCS64's placement. `targets/aarch64`
  holds the compiler for the target.
- **`compiler/interp/` was added.** The interpreter is a real boundary: the passes and the
  lowering do not use it.
- **The binary, suites, and examples are targets of package `fir`.** Their files live in
  `tools/`, `tests/rust/`, and `benchmarks/rust/`. Cargo only gives `CARGO_BIN_EXE_fir` to
  tests of the package that builds the binary, and keeping them in `fir` keeps every
  `cargo test -p fir --test NAME` working.
- **No placeholder directories.** There is no Rust or C++ frontend, no accelerator target, and
  no runtime.

## How this layout was reached

These commits move code and nothing else. Every step was built and passed clippy. Each one
also passed `cargo xtask verify fast`, except the `fai-codegen` and `fai-target-aarch64` steps,
which ran the suites that exercise them (both native backends, the register check, ABI, and
debug lines); `verify fast` passed on the next step. `verify full` ran on the result:

1. Inside the old single `fir` crate, the files that were not one target's compiler moved out
   of `backend/` (the dialect, codegen, and driver modules), with re-exports at the old paths.
2. Crates were split out one at a time, in dependency order: `fai-ir`, `fai-interp`,
   `fai-lowering`, `fai-transforms`, `fai-codegen`, `fai-target-aarch64`, `fai-target-x86_64`,
   and `fai-driver`. Each step widened only the `pub(crate)` items the compiler reported as
   crossing a new boundary (25 in `fai-ir`, one in `fai-interp`).
3. `crates/` became `sdk/`, `tools/`, `tests/rust`, and `benchmarks/rust`, and the C benchmark
   harness moved to `benchmarks/c`.

Paths changed in the Cargo manifests, the Lean generators' header lines, cbindgen's settings,
CMake's include path, xtask's freshness checks and mutation anchors, and the docs. Regenerating
every generated file gives the same bytes, and the proof audit's fingerprints did not change.
