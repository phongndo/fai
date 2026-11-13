# Restructuring fai into library-first crates: dependency map and migration plan

Status: **plan only; no file has moved.** Execution stopped before the first structural change
because it conflicts with the x86-64 backend, which is committed but not integrated with this line
(see "Blocking: the x86-64 line"). Written against `origin/main` at `ddf75e1`.

## What this checkout contains

| Work | Present here? | Where |
|---|---|---|
| AArch64 backend (HFIR → MFIR → LFIR `aarch64` dialect → GNU asm, Linux ELF and Darwin) | yes | `crates/fir/src/backend/aarch64/` |
| x86-64 backend (integer subset of MFIR, Linux only) | **no** | local `main` / `feat/x86-backend` at `31b13e7`, 6 commits from merge-base `1ac29a2`, not on `origin/main` |
| Shared global-data emission between backends (`backend/data.rs`) | **no** | same x86 line (`1316bde`) |
| Proof-backed DCE checking (`CheckDce`, `FIR_CHECK_DCE`, `--check-dce`, required by `verify full`) | yes | `passes/reference.rs`, `backend/mod.rs`, `docs/assurance/dce.md` |
| Promotion passes `mem2reg`, `stackdce` (labelled `Assurance::Experimental`, opt-in only) | yes | `passes/mem2reg.rs`, `passes/stackdce.rs` |
| Default `-O` pipeline (proved passes only: dse, fwd, copyprop, dce) | yes | `passes/mod.rs` (`DEFAULT`, `Pipeline::default_opt`) |
| Pass observers, `--print-before/after/changed`, `--dump-dir` | yes | `passes/mod.rs`, `bin/fir.rs` |
| Differential, fuzz, ABI torture, contract, debug-line, regcheck suites | yes | `crates/fir/tests/`, `crates/fir-capi/tests/`, corpora in `tests/` |
| C benchmark harness `cbench` and the C baseline (native M4 Max timing vs qemu-user counts) | yes | `frontends/c/bench/`, `docs/performance/c-baseline*.md` |
| CLI names | `fir`, `fcc` (renamed from `fai-cc` at `753b752`; old name documented, no alias), Lean `fir-ref`, `fir-audit` | |
| `fcxx` | no, and none is planned here | |

## Current dependency map

Three Cargo packages (`fir`, `fir-capi`, `xtask`), one CMake project (`frontends/c`, which links
`libfir_capi.a` and includes `crates/fir-capi/include/fir.h`), one Lake project (`spec/`).

Inside `fir` (module → modules it uses):

```text
ir ─────────────▶ backend::aarch64::syntax   (Reg, AluOp, Cond, …: the aarch64 LFIR dialect's
                                              immediates are part of the one generated OpKind)
ops (generated) ▶ body, decl, ir
contract ───────▶ generated contracts, interp::support, lower::support,
                  backend::aarch64::isel::support          (components() aggregates all three)
interp ─────────▶ body, contract, float, sem, types, and, as a child module mounted with
                  #[path], backend/aarch64/machine.rs (the LFIR machine, sharing the memory model)
  machine.rs ───▶ backend::aarch64::abi (AAPCS64 placement), interp internals (super::*)
backend::aarch64::abi ▶ ir, types only
lower ──────────▶ body, contract, decl, verify
passes ─────────▶ body, contract, verify (parse only in unit tests)
backend (mod) ──▶ lower_checked, passes (Pipeline, Observer, CheckDce), verify   (= the driver)
backend::aarch64 (isel, lfir, mir, regalloc, regcheck, emit)
                ▶ abi, body, contract, decl, float, interp::vfp_expand_imm, sem, types
bin/fir ────────▶ everything public
```

So the `aarch64` dialect's definition is three files that mirror three Lean files and sit in
`backend/` only by history: `syntax.rs` (`AArch64Syntax.lean`), `abi.rs` (`AArch64Abi.lean`), and
`machine.rs` (`AArch64Machine.lean`, executed by `fir run` on LFIR). The compiler proper is the
rest of `backend/aarch64`.

Two cycles a crate split has to break: `ir → backend::aarch64::syntax` and
`contract::components → backend::aarch64::isel`; and one file, `machine.rs`, that is physically in
the backend but logically in the interpreter. The edges out of `backend/aarch64` and `passes`
into the core are about 95 `crate::` paths, many into private modules (`sem`, `float`, `body`),
plus 52 `pub(crate)` items in the core that the new crate boundaries would cross.

The Lean side already has the separation this restructure wants and should keep: `Fir`
(semantics, proofs, the op DSL; imports only `Init`), `Audit` (links the Lean compiler), and
executables `fir-ref`, `gen-rust`, `gen-builder`, `fir-audit`.

Generated-file paths are written in three places that must move together: the generators' header
comments (`spec/GenRust.lean`, `spec/GenBuilder.lean`), `xtask` (`generated()`, the
`cbindgen.toml`/`fir.h` freshness check), and CMake's include path.

## Target layout, adjusted to the dependency graph

```text
compiler/
  ir/          fai-ir         IR, types, op table (generated), parse/print/verify, builder (generated
                              methods), contract data (generated), sem/float, and the aarch64 LFIR
                              dialect's syntax and AAPCS64 placement (dialect/aarch64; see deviations)
  interp/      fai-interp     the reference interpreter for all three layers, with the aarch64
                              machine model as its child module; used by tests, fir run, the C API
  lowering/    fai-lowering   HFIR → MFIR (lower.rs)
  transforms/  fai-transforms pass manager, Assurance labels, DEFAULT, observers, dumps, passes,
                              CheckDce (the bridge to the proved Lean checker)
  codegen/     fai-codegen    only once the x86 line lands: backend/data.rs is the first code two
                              backends share
  driver/      fai-driver     prepare/optimize/compile (backend/mod.rs), contract::components
targets/
  aarch64/     fai-target-aarch64   isel, lfir, mir, regalloc, regcheck, emit
  x86_64/      fai-target-x86_64    only once the x86 line lands
sdk/
  rust/        fir            facade crate re-exporting the above: keeps `use fir::…` working for
                              fir-capi, the tests, the examples, and any outside user
  c/           fir-capi       unchanged name, lib `fir_capi`, header `sdk/c/include/fir.h`
tools/
  fir/         fir-cli        the `fir` binary (name unchanged)
frontends/c/                  fcc (CMake; unchanged apart from the header path)
spec/                         unchanged; generator header paths updated
tests/                        the corpora as now, plus the cross-component Rust suites (package
                              fai-tests, test binary names unchanged)
benchmarks/c/                 cbench, moved from frontends/c/bench
docs/, xtask/, nix/           paths updated
README.md                     new: entry point and current status
```

Dependency direction (arrows point at dependencies; nothing points up at a frontend or tool):

```text
fcc (C++, CMake) ──▶ fir-capi ──▶ fir (facade) ──▶ fai-driver ──▶ fai-target-* ──▶ fai-codegen ─┐
fir-cli ──────────────────────────▶ fir             │            └───────────────────────────▶ fai-ir
fai-tests ─────────────────────────▶ fir             ├──▶ fai-transforms ──────────────────────▶ fai-ir
                                                     ├──▶ fai-lowering ────────────────────────▶ fai-ir
                                                     └──▶ fai-interp ──────────────────────────▶ fai-ir
xtask: no Rust dependency on the compiler (it runs cargo, lake, clang)
```

### Deviations from the suggested tree, and why

- **The aarch64 dialect's definition stays in the core, not in `targets/aarch64`.** HFIR, MFIR,
  and the LFIR `aarch64` dialect share one `OpKind`, generated from `spec/Fir/Syntax.lean` and
  `spec/Fir/AArch64Syntax.lean`; `decl::Imm::Reg` and the generated `A64*` variants hold `Reg`,
  `Cond`, and friends. Moving `syntax.rs` into the target crate would invert the dependency or
  split the generated op table, which changes the generators and is not a structural move. The
  machine model is the interpreter's (it is mounted inside `interp` and shares its memory model),
  and it needs the AAPCS64 placement in `abi.rs`, so both move down with it. What moves to
  `targets/aarch64` is the compiler: instruction selection, register allocation and its checker,
  and emission. HFIR, MFIR, and LFIR stay identifiable as `Layer` values and op-table tiers, not
  crates.
- **No `compiler/analysis` crate.** There is no standalone analysis code yet (use lists live in
  `body.rs`, the walk in `mem2reg`); an empty crate would be a placeholder.
- **`fai-interp` is added** (not in the suggested tree): it is a real boundary. Passes and
  lowering don't use it; isel uses only `vfp_expand_imm`, which moves to `fai-ir::float`.
- **`fai-codegen` waits for the x86 line.** On this line there is no code two backends share.
- **The `fir` crate name survives as the facade**, so the restructure changes no Rust import
  outside the workspace and no C symbol.

## Blocking: the x86-64 line

Local `main` (= `feat/x86-backend`, `31b13e7`) is 6 commits ahead of and 15 behind `origin/main`.
A trial merge (`git merge-tree`, nothing written) conflicts in 9 files before any restructure:
`fir.h`, `fir-capi/src/lib.rs`, `bin/fir.rs`, `tests/aarch64.rs`, `frontends/c/src/main.cpp`,
`frontends/c/README.md`, `docs/design/01-layers.md`, `docs/design/decisions.md`, `nix/devshell.nix`.
They are feature conflicts, not textual ones:

- **C API version.** This line adds `fir_module_optimize_passes` and `fir_module_compile_passes`
  at `FIR_API_VERSION` 1.5; the x86 line bumps to 1.6 for `target = "x86_64"`.
- **Flag composition.** This line gives `fir compile`, fcc, and the C API `--passes`,
  `--experimental`, and `--check-dce`; the x86 line gives the same three entry points
  `--target x86_64`. The merge has to decide how they combine (and keep `-g` and `--emit lfir`
  refusing x86-64 clearly).
- **The rename.** The x86 line still says `fai-cc` and `FAI_CC_RESOURCE_DIR`; this line renamed them.
- **Test harness.** The x86 line moves 860 lines of `tests/aarch64.rs` into a shared
  `tests/native/mod.rs`; this line edited `tests/aarch64.rs` for experimental pipelines.
- **Dev shell.** The x86 line adds an x86-64 cross toolchain; this line adds cbench's AArch64 libc
  and GCC.

Restructuring first would move every file the x86 line touches and rewrite the `crate::` paths
its 3.8k new lines depend on, turning those 9 conflicts into a port across crate boundaries.

## Migration plan

Step 0 is the precondition; each later step is one commit, behavior-preserving, with the checks
listed run before the next step. "verify full" is `nix develop -c cargo xtask verify full`.

0. **Integrate the x86 line** (separately, as a feature merge): decide the C API version and the
   flag composition above, update the x86 text to `fcc`, then verify full on x86-64 Linux plus the
   native x86-64 suites (`crates/fir/tests/x86_64.rs`, fcc's corpus with `--target x86_64`), and
   verify full on Apple silicon. Only after this does the restructure start.
1. **Workspace skeleton.** Root `Cargo.toml` members list instead of `crates/*`; shared
   `[workspace.dependencies]`. No code moves. Check: `cargo build --workspace`, verify fast.
2. **Break the two cycles inside `fir`** (still one crate): move `backend/aarch64/syntax.rs` and
   `abi.rs` under `dialect/aarch64/`, and `machine.rs` beside `interp.rs`, each with a re-export
   at its old public path; move `contract::components` and `backend/mod.rs`'s driver functions
   into a `driver` module, re-exported at `fir::backend::*`; move `vfp_expand_imm` to `float`.
   Update the paths the Rust doc comments and `docs/` give for these files. Check: verify full
   (the contracts suite and `docs/assurance/op-contracts.json` must be byte-identical).
3. **Extract `fai-ir`** to `compiler/ir`, generated files with it; `fir` re-exports it. Update the
   generator headers, `xtask generated()`, and the `generated_rust` evidence paths in the same
   commit. Check: `lake exe gen-rust`/`gen-builder` outputs identical to the checked-in files,
   verify full.
4. **Extract `fai-interp`, `fai-lowering`, `fai-transforms`** (one commit each). `Assurance`,
   `DEFAULT`, `parse_experimental`, and `CheckDce` move unchanged. Check after each: verify full;
   `fir opt --list-passes` output identical; the `dce_*` suites and the proof audit pass.
5. **Extract `fai-codegen` and the targets** (`fai-target-aarch64`, `fai-target-x86_64`).
   Check: verify full (qemu-user for AArch64 on x86-64 Linux), native AArch64 on Apple silicon,
   native x86-64 on x86-64 Linux; ABI torture counts unchanged.
6. **Extract `fai-driver`**, make `fir` a pure facade at `sdk/rust`. Check: verify full;
   `fir::` paths used by `fir-capi`, the examples, and the tests compile unchanged.
7. **Move the binary** to `tools/fir` (package `fir-cli`, binary `fir`) and **`fir-capi` to
   `sdk/c`**: CMake include path, `cbindgen.toml`, xtask's `fir.h` check, `tests/capi`. Check:
   verify full (C API under ASan), fcc's CMake build and corpus.
8. **Move the cross-component Rust suites** to `tests/` (package `fai-tests`, test binary names
   unchanged so `xtask`'s evidence names still match). Check: verify full, evidence counts equal
   to step 0's report.
9. **Move cbench** to `benchmarks/c`; update `nix/devshell.nix`, the bench READMEs, and the
   paths in `docs/performance/` without touching recorded numbers. Check: `cbench.py` dry run on
   one program under qemu-user; native timing only on an AArch64 host.
10. **Docs and README**: root `README.md`, `docs/architecture.md` with this map, CI paths.
    Check: `nix flake check`, verify full.

Compatibility kept throughout: the `fir` and `fcc` binaries and all their flags, `fir-ref`,
`fir-audit`, the `fir` Rust crate path, every C symbol and `FIR_API_VERSION`, the environment
variables `xtask` clears, test binary names. No stable Rust API or ABI is promised; the internal
`fai-*` crates are `publish = false`. `fcxx` is not created; there is room for it beside `fcc`.
