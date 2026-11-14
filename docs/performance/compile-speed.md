# How fast fai compiles

This is about the time fai takes to compile a program: what an edit, compile, and test loop
waits for. It is not about how fast the generated code runs ([c-baseline.md](c-baseline.md) and
the inference benchmark cover that), and it keeps the time to rebuild the compiler itself
separate ([below](#rebuilding-the-compiler)). Every number here was measured. The commands are
at the end, and the full generated tables are in
[compile-speed-report.md](compile-speed-report.md).

## Summary

- **Small C files compile 30% faster.** On 12 small programs, fcc `-O` to an AArch64 object
  took 35.5 ms (geometric mean) at `045d398` and takes 25.0 ms now. That is 1.48× Clang `-O0`'s
  time and 1.15× GCC `-O0`'s, down from 2.10× and 1.64×. For x86-64 objects the time went from
  51.9 to 35.9 ms. Almost all of the gain is the cached include probe: fcc no longer runs the
  target C compiler on every file to find its headers.
- **Large functions are no longer quadratic.** The register allocation validator, which runs
  on every compilation, had been 86-98% of register allocation's time and was quadratic in a
  function's size. For one 6,400-statement function, fcc `-O` now takes 0.52 s instead of
  3.75 s, and its peak memory fell from 1,746 MiB to 191 MiB (Linux). On an Apple M4 Max,
  `fir compile` takes 0.21 s instead of 2.46 s. At 1,600 statements the times are 0.12 s
  against 0.34 s.
- **Many functions now use less CPU.** The 32 hardware threads hid the validator's cost in
  wall time: 1,600 functions take 790 ms against 810 ms. CPU time fell from 1,378 to 1,012 ms,
  which matters on fewer cores, or with several agents compiling at once.
- **Every check still runs, and every output is the same.** The validator checks exactly what
  it checked before: 186,468 validations in a differential run gave identical verdicts and
  messages. Every object, assembly file, and module compiled here is byte-identical before and
  after, on both targets and both hosts. Each phase's cost, verification included, is now
  visible with `FIR_TIME=1`.
- **What is left.**
  - **Small file (matmul, 22 ms):** about 9 ms of process start and Clang setup, 5 ms of Clang,
    6 ms of the external assembler, 1 ms writing the assembly, and 1.5 ms of fai itself.
  - **Large program (1,600 functions):**
    - The external assembler is 43% of wall time on Linux (337 of 790 ms). On macOS it is 84%:
      the host assembler there is LLVM's, which is 3× slower than GNU `as` on fai's text.
    - Clang and fcc's lowering to HFIR take 21%.
    - Verifying the IR takes 9%.
    - fai's other phases run on one thread.
  - **Opt-in proved DCE checker (`--check-dce`):** multiplies a large compilation's time by 10.
- **Next:** write objects directly instead of assembly text. That is the largest remaining cost
  on every input size above a few hundred lines, and by far the largest on macOS.

## What was measured, on what

| | |
|---|---|
| Revisions | the baseline is `045d398` (`main`). After: this branch: `91ad771` (timing), `2f5c312` and `7b8b54a` (validator), `0e8c8bb` (include-probe cache), `1f3f597` (harness). The final runs are at `1f3f597`, from a clean tree |
| Linux host | AMD Ryzen 9 9950X (16 cores, 32 threads), 30 GiB, NixOS, Linux 6.18.60, x86-64. It is shared with other work, so every comparison interleaves its configurations in shuffled rounds and reports medians, quartiles, and ranges. The final run's load average was 3.7-6.3 |
| macOS host | Apple M4 Max (16 cores), macOS 26 (Darwin 25.6.0), natively. Also shared, with a load average of 4.2-4.7 |
| Toolchain | the dev shell (`nix develop`, nixpkgs as `flake.lock` pins): rustc 1.99.0; Clang/LLVM 23.1.3, which is fcc's frontend and the reference Clang; the AArch64 cross GCC 16.2.0 and binutils 2.46, which are the reference GCC and, on Linux, fcc's assembler; host GCC 15.3.0 |
| Flags | fcc and `fir compile` as shipped, with `-O` where named. The reference compilers get the flags `cbench.py` sets: `-ffp-contract=off` and no Nix hardening. Clang also gets exactly fcc's Clang setup: the target, `-nostdlibinc`, the resource directory, and the cross GCC's include directories |
| Targets | AArch64 Linux (fcc's default; ELF), x86-64 Linux (fcc `--target x86_64`, the integer subset), and AArch64 macOS (`fir compile --os darwin`, Mach-O) |
| Method | `benchmarks/compile/compilebench.py` on Linux. Each workload runs one warmup round, then 10 rounds, with the configurations in a new order each round. It records wall time, CPU time (user plus system, including the children the compiler waited for), and peak RSS, from `wait4`. Phase breakdowns come from separate `FIR_TIME=1` runs. On the Mac, the same method ran from a script, on the generated workloads only (see Limits) |

The comparison with Clang and GCC measures compile time only. The compilers don't produce code
of the same quality: fcc's code is slower than `-O0` code ([c-baseline.md](c-baseline.md)).

## Before and after (Linux)

Median wall time in ms, with quartiles in brackets, over 10 rounds. "fcc" is `fcc -O FILE -o
FILE.o`, the C frontend, fai, and the external assembler. "fir" is `fir compile -O FILE.mfir
--emit asm`, fai's own pipeline with no C frontend and no assembler. x86-64 is the integer
subset, so the three programs with floats are refused there (`-`).

| workload | fcc, AArch64, before | after | fcc, x86-64, before | after | fir, before | after |
|---|---:|---:|---:|---:|---:|---:|
| bintree | 32.7 [30.9, 34.5] | 22.3 [21.4, 23.9] | 47.3 [44.1, 49.1] | 32.2 [30.2, 34.2] | 2.8 [2.6, 3.1] | 2.7 [2.4, 2.7] |
| bytecode | 33.4 [32.2, 35.1] | 22.7 [21.8, 23.8] | 45.2 [44.0, 47.3] | 30.8 [29.8, 33.6] | 3.3 [3.2, 3.6] | 3.1 [3.0, 3.3] |
| crc32 | 34.8 [34.1, 35.9] | 25.7 [24.3, 26.6] | 51.3 [49.3, 52.9] | 36.0 [34.9, 36.7] | 3.7 [3.6, 3.9] | 3.6 [3.4, 3.7] |
| fannkuch | 31.4 [30.8, 32.4] | 21.6 [21.0, 22.2] | 42.5 [42.1, 45.6] | 28.8 [28.0, 30.8] | 3.4 [3.2, 3.6] | 2.8 [2.7, 2.8] |
| hashtab | 31.7 [31.1, 31.8] | 21.4 [21.1, 22.7] | 44.1 [43.1, 45.8] | 29.2 [27.6, 30.6] | 3.3 [3.1, 3.4] | 2.9 [2.8, 3.0] |
| mandel | 31.1 [30.3, 32.9] | 20.5 [19.5, 21.3] | - | - | 2.7 [2.6, 2.8] | 2.4 [2.3, 2.5] |
| matmul | 32.2 [31.7, 33.5] | 22.3 [21.1, 22.9] | - | - | 3.5 [3.3, 3.6] | 3.1 [3.0, 3.2] |
| nbody | 33.7 [32.4, 35.4] | 22.9 [21.2, 24.6] | - | - | 3.5 [3.4, 3.6] | 3.4 [3.3, 3.6] |
| nqueens | 32.3 [30.2, 33.5] | 22.5 [20.4, 23.5] | 43.8 [43.5, 46.4] | 30.4 [29.4, 32.8] | 2.4 [2.3, 2.5] | 2.3 [2.2, 2.4] |
| quicksort | 34.5 [33.5, 37.4] | 25.1 [22.8, 27.1] | 51.9 [45.4, 62.3] | 32.6 [29.6, 36.6] | 4.1 [3.9, 4.7] | 3.6 [3.5, 3.8] |
| sieve | 84.0 [83.2, 84.6] | 73.2 [72.5, 74.8] | 127.2 [124.9, 129.7] | 111.0 [109.0, 111.5] | 16.2 [15.8, 16.4] | 15.8 [15.6, 15.9] |
| strings | 34.1 [33.0, 35.4] | 22.4 [22.2, 23.3] | 45.7 [44.8, 47.8] | 30.3 [29.1, 32.3] | 4.6 [4.5, 4.8] | 3.8 [3.7, 4.0] |
| 100 functions × 10 statements (1,401 lines) | 83.3 [82.6, 86.2] | 70.5 [69.1, 72.7] | 93.9 [91.8, 95.1] | 78.1 [77.3, 78.9] | 27.3 [27.0, 28.0] | 24.9 [24.5, 25.6] |
| 400 × 10 (5,601) | 228.8 [222.4, 232.5] | 206.4 [204.6, 209.5] | 222.4 [217.7, 226.8] | 204.3 [201.8, 212.0] | 72.8 [72.0, 74.5] | 69.7 [68.6, 71.6] |
| 1,600 × 10 (22,401) | 810.2 [798.6, 826.3] | 789.8 [776.9, 907.3] | 746.4 [740.4, 752.8] | 739.6 [732.8, 748.6] | 292.7 [290.8, 296.2] | 274.8 [273.0, 286.5] |
| 1 function × 400 statements | 69.0 [68.2, 69.6] | 42.5 [41.7, 43.7] | 66.4 [64.5, 69.1] | 49.9 [48.8, 51.1] | 29.3 [29.1, 29.9] | 13.8 [13.7, 14.2] |
| 1 × 1,600 | 338.6 [336.8, 340.1] | 117.3 [115.6, 118.3] | 133.0 [131.7, 134.8] | 116.4 [115.5, 117.6] | 256.6 [255.7, 258.2] | 49.8 [49.5, 50.1] |
| 1 × 6,400 | 3,746 [3,735, 3,796] | 515.6 [509.2, 517.7] | 437.7 [434.0, 440.1] | 422.5 [420.0, 424.5] | 3,406 [3,398, 3,434] | 262.8 [260.1, 269.8] |

The x86-64 backend has no allocation validator, so on large functions it changed only by the
include probe. In CPU time, which includes the assembler and the include probe, the many-function
inputs gained more than their wall time shows. Over 400 functions, fcc went from 354 to 262 ms
and fir from 198 to 128 ms. Over 1,600, fcc went from 1,378 to 1,012 ms and fir from 835 to
494 ms. Peak memory fell only for single large functions:

| workload | fcc before | fcc after | fir before | fir after | Clang `-O0` | GCC `-O0` |
|---|---:|---:|---:|---:|---:|---:|
| 1 × 1,600 | 180 MiB | 78 MiB | 126 MiB | 39 MiB | 111 MiB | 74 MiB |
| 1 × 6,400 | 1,746 MiB | 191 MiB | 1,694 MiB | 139 MiB | 154 MiB | 187 MiB |

**Cold and warm.** A cold include-probe cache costs a probe and a cache write once per
environment and target. In the final run, fcc's first AArch64 compilation took 46.6 ms against
a median of 21.6, and its first x86-64 compilation 52.3 ms against 32.2. After that, every run
is warm. fai has no incremental compilation: compiling a file again does all the work again.

### Against Clang and GCC (compile time only)

Medians in ms, Linux, all producing AArch64 objects, except the x86-64 columns:

| workload | fcc `-O` | Clang `-O0` | GCC `-O0` | Clang `-O2` | GCC `-O2` | fcc `-O` x86-64 | Clang `-O0` x86-64 | GCC `-O0` x86-64 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 12 small programs (geometric mean) | 25.0 | 16.9 | 21.6 | 26.5 | 38.0 | 35.9 | 22.0 | 19.6 |
| 100 × 10 | 70 | 46 | 129 | 288 | 235 | 78 | 56 | 117 |
| 400 × 10 | 206 | 132 | 448 | 1,098 | 638 | 204 | 156 | 407 |
| 1,600 × 10 | 790 | 481 | 1,758 | 4,520 | 2,304 | 740 | 567 | 1,595 |
| 1 × 400 | 42 | 26 | 45 | 104 | 209 | 50 | 31 | 37 |
| 1 × 1,600 | 117 | 59 | 132 | 482 | 836 | 116 | 64 | 105 |
| 1 × 6,400 | 516 | 225 | 538 | 4,364 | 4,602 | 422 | 196 | 426 |

The small programs' x86-64 geometric means cover the nine integer programs for fcc and all
twelve for Clang and GCC.

fcc is now within 1.5× of Clang `-O0` on small files and faster than GCC `-O0` on generated
code. Clang `-O0` stays the fastest compiler: it assembles in process and starts no other
processes.

## Where the time goes now

Self time in ms of one fcc `-O` compilation to an AArch64 object (`FIR_TIME=1`, medians of 5
runs, Linux). Phases marked `*` ran on worker threads and are CPU time summed over them. The
last row is the median wall time less the phases' total. The phases came from separate runs,
so that row is approximate.

| phase | matmul | 1,600 × 10 | 1 × 6,400 |
|---|---:|---:|---:|
| fcc: include probe (cached) | 0.03 | 0.05 | 0.05 |
| fcc: Clang (preprocess, parse, semantic analysis) | 5.35 | 95.0 | 34.7 |
| fcc: lowering the AST to HFIR | 0.23 | 70.1 | 69.3 |
| verify (every IR verification) | 0.12 | 70.4 | 24.1 |
| lower (HFIR to MFIR) | 0.08 | 44.2 | 11.7 |
| `-O` passes | 0.06 | 26.4 | 5.2 |
| AArch64 instruction selection | 0.09 | 36.5 | 10.5 |
| AArch64 register allocation (wall, main thread) | 0.66 | 16.5 | 175.3 |
| ... assignment `*` | 0.11 | 68.0 | 90.7 |
| ... rewriting `*` | 0.02 | 33.3 | 2.7 |
| ... allocation validator `*` | 0.33 | 210.6 | 77.2 |
| AArch64 emission | 0.05 | 25.4 | 9.8 |
| fcc: writing the assembly | 1.06 | 46.9 | 21.0 |
| fcc: external assembler and linker (`cc`) | 5.86 | 337.1 | 147.3 |
| total of the main thread's phases | 13.55 | 775.5 | 508.1 |
| outside the phases (process start, Clang's setup, exit) | 8.7 | 14.3 | 7.5 |

- **Small file.** fai's own work takes about 1.5 ms of 22 ms. The rest is three processes and
  their setup:
  - Loading fcc's 300 MB of Clang and LLVM shared libraries takes 5.2 ms before `main`.
  - Clang takes 5 ms.
  - The cross GCC driver and `as` take 5.6 ms. `as` alone takes 1.1 ms on an empty file; the
    driver takes 4.7.
- **Many functions.**
  - The assembler takes 43% of the time.
  - Clang and the lowering to HFIR take 21%.
  - Verification takes 9%. The HFIR is verified twice, once by fcc and once by
    `fir_module_compile`.
  - fai's phases other than allocation run on one thread.
  - fcc writes 8 MB of assembly in 45 ms, and GNU `as` reads it at about 25 MB/s.
- **One large function.** Allocation takes 34% of the time. Assigning registers (91 ms) now
  costs more than validating the result (77 ms), which was 3.4 s at the baseline.
- **macOS (M4 Max).**
  - `fir compile -O --os darwin -o x.o` on 1,600 functions takes 1,439 ms, and assembling
    accounts for 1,215 ms of it (84%). The host's `cc` assembles with LLVM's integrated
    assembler.
  - On Linux, the same assembler (`llvm-mc`) took 962 ms on the 8 MB file that GNU `as`
    assembles in 326 ms, with identical disassembly.
  - fai's in-process pipeline (`--emit asm`) took 224 ms.

### macOS, before and after (M4 Max, natively)

Medians of 10 rounds, ms, peak RSS in MiB:

| workload | `fir compile -O --os darwin --emit asm` before | after | `... -o x.o` (with the host assembler) before | after | fcc `-O --emit asm` before | after | Clang `-O0 -c` |
|---|---:|---:|---:|---:|---:|---:|---:|
| 100 × 10 | 20.3 | 17.6 | 158.8 | 156.9 | 52.4 | 50.5 | 62.0 |
| 400 × 10 | 64.2 | 61.3 | 424.2 | 414.9 | 129.4 | 125.9 | 138.3 |
| 1,600 × 10 | 238.3 | 224.0 | 1,453 | 1,439 | 442.2 | 425.7 | 441.3 |
| 1 × 400 | 21.7 | 11.1 | 120.2 | 110.6 | 47.0 | 37.9 | 46.0 |
| 1 × 1,600 | 181.3 (150) | 39.2 (31) | 362.3 | 217.6 | 219.4 (189) | 79.3 (71) | 69.8 |
| 1 × 6,400 | 2,464 (2,016) | 214.5 (184) | 2,982 | 721.9 | 2,586 (2,070) | 332.5 (227) | 186.3 |

Outputs are byte-identical before and after on every row. fcc on macOS ran without system
headers (see Limits), so its include probe fails there each time and is not cached.

## What changed

Four changes, each measured, none changing what fai emits: every output of every workload below
is byte-identical before and after (`compilebench`'s output hashes, both targets; the M4 Max
runs check the same).

1. **`FIR_TIME=1`** (`91ad771`) prints where a compilation's time went, phase by phase:
   `fai_ir::timing` records each phase's self time (phases inside it subtracted), and marks the
   phases worker threads record as CPU time summed over them. `fir` prints the report; fcc adds
   its own steps through two new C API calls (`fir_time_record`, `fir_time_report`;
   `FIR_API_VERSION` 1.7, `tests/capi/timing.c`) and prints one report. Off, a phase costs one
   relaxed atomic load.
2. **The register allocation validator's state is cheap to copy** (`2f5c312`, `7b8b54a`). The
   validator copies its dataflow state at every block entry, join, and choice point. It was 63
   heap-allocated sets plus a `BTreeMap` of sets per slot kind, so a function with B blocks and
   S slots copied B × S sets: 86-98% of register allocation's time, quadratic in a function's
   size. Locations are now numbered densely and stored in `Rc`'d chunks of 32, copied only when
   written; small sets live in place; each chunk lists the values it may hold, kept within twice
   what it holds, so removing a value skips chunks that can't hold it. What the validator
   checks, its walk, budgets, worklist, and messages are unchanged
   (`targets/aarch64/src/regcheck/state.rs`).
3. **fcc caches its include probe** (`0e8c8bb`). Every fcc run started the target C compiler to
   list its include directories (`cc -E -Wp,-v`): 7-10 ms, 30-40% of compiling a small file.
   The answer is cached, keyed by everything that could change it (the compiler named, its real
   path, size and modification time, the target, and the environment except eight variables
   that don't affect a C compiler's search path), and used only while every directory found
   still exists and every directory the compiler skipped as nonexistent still doesn't
   (`frontends/c/README.md`, `sdk/c/tests/fcc_cache.rs`). `FCC_CACHE=0` turns it off.
4. **`compilebench`** (`1f3f597`, `benchmarks/compile/`) reproduces every table here.

### How the changes were checked

- **Validator, representation.** `regcheck/state.rs` keeps the original representation as a
  test model; random programs of state operations (clones, joins, and equality included) must
  agree with it on every observation (300 programs per release test run, 40 in development
  builds; 3,000 were run once). This test found a real disagreement in a first version: a chunk
  both sides share is not its own join when a slot in it is in the map but empty, which would
  have changed when the dataflow sees a block's state as changed.
- **Validator, end to end.** A one-time differential run of the original validator against the
  new one (not kept in the tree) on 396 modules (every `.fir` corpus, the C corpus, the
  benchmark programs, and generated functions; each without `-O`, with `-O`, and with the
  experimental promotion pipeline: 4,548 functions), with 40 random mutations of each honest
  allocation (registers changed, instructions deleted, duplicated, or swapped, offsets moved):
  186,468 validations, 46,453 accepted and 140,015 refused by both, every message identical. It
  was run on both versions.
- **Include-probe cache.** `fcc_cache.rs` checks a hit, a miss on a changed environment, a
  skipped directory that appears, a damaged entry, and that cached, uncached, and `FCC_CACHE=0`
  runs give the same HFIR. With the environment left out of the key, or without the
  skipped-directory check, it fails. The fcc corpus passes with the cache on.
- **Suites.** `cargo xtask verify fast` passes on the timing and validator commits (11 checks,
  0 failed; release tests, AddressSanitizer, and complete evidence are skipped by design in fast
  mode); the AArch64, register-check, ABI, debug-line, C API, and fcc suites pass in release on
  the final commit. `verify full` was not run.

## What verification costs

fai checks its own work on every compilation; none of it was turned off. Self time on the Linux
host (`FIR_TIME=1`, medians), after the changes:

| check | runs | matmul | 400 × 10 | 1,600 × 10 | 1 × 1,600 | 1 × 6,400 |
|---|---|---:|---:|---:|---:|---:|
| IR verifier (`verify`: fcc's HFIR, again in `fir_module_compile`, the lowering's output, the `-O` output) | always | 0.12 | 16.5 | 70.4 | 5.4 | 24.1 |
| allocation validator (`aarch64.regcheck`, CPU over threads) | always (AArch64) | 0.33 | 48.3 | 210.6 | 12.1 | 77.2 |
| ... the same at `045d398` | | 0.6 | 131 | 603 | 215 | 3,250 |
| whole fcc `-O` compilation, wall | | 22.3 | 206.4 | 789.8 | 117.3 | 515.6 |
| proved DCE checker (`--check-dce`, `fir-ref check-dce`), wall it adds | opt in | +6.4 | +970 | +4,100 | | |

The `045d398` validator figures come from the A/B runs in the commit messages, which used the
same inputs but separate runs.

- **The IR verifier** is 9% of a large compilation. One of its four passes is redundant: fcc
  verifies the HFIR, then `fir_module_compile` verifies the same module again. That is a quarter
  of the cost, about 17 ms on 1,600 functions.
- **The allocation validator** is now 11-21% of a large compilation's CPU: 211 of 1,012 ms on
  1,600 functions, 77 of 490 ms on one 6,400-statement function. At `045d398` it was up to 88%.
  It costs 1-3× the register assignment it checks.
- **The proved DCE checker** (`--check-dce`, which the C corpus's `-O` builds use in
  `verify full`) costs more than the rest of the compilation together: 6.4 ms on matmul, about
  1 s on 400 functions, about 4.1 s on 1,600. That is 10× the whole compilation, with three
  runs each agreeing within 7%. It hands the module to `fir-ref` as text and checks it in Lean.
  It is opt-in, and it belongs to the proof work, so this study only measured it.
- **Development builds** also verify after every pass (`verify_each`), which release builds
  don't.

The validator remains one of fai's largest costs on large inputs, but it is now 11-21% of a large
compilation's CPU rather than up to 88%. For comparison, CompCert's verified register allocation
validator reports 20% of register allocation's time and 6% of the whole compilation
([Rideau and Leroy, CC 2010](https://xavierleroy.org/publi/validation-regalloc.pdf)), and
Cranelift keeps its register allocation checker off by default for being "somewhat expensive"
([settings.rs](https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/codegen/meta/src/shared/settings.rs)).
fai keeps its validator on.

## Rebuilding the compiler

Not the subject of this study, but part of the loop. Linux host, the dev shell, `cargo build
--bin fir`, wall seconds (user CPU):

| | release | debug |
|---|---:|---:|
| from scratch | 5.8 (36.9) | 4.0 (10.5) |
| after editing `targets/aarch64/src/regcheck.rs` (a leaf crate) | 2.4 (6.8) | 0.6 (0.4) |
| after editing `compiler/ir/src/lib.rs` (the root crate) | 4.4 (33.7) | 0.8 (0.9) |
| after editing `tools/fir/main.rs` | 0.6 (0.7) | 0.5 (0.3) |
| fcc (CMake, Ninja) from scratch | 6.7 (10.0) | |

Release builds aren't incremental (Cargo's default), so editing the root crate recompiles
every crate after it; development builds take under a second. On the M4 Max, building `fir`
and fcc from scratch took 11-12 s.

## The agent loop

| | Linux host |
|---|---:|
| `cargo xtask verify fast` | 4 min 6 s, of which the debug-build test suites 239 s |
| `cargo test --release -p fir-capi --test fcc` (the C corpus, 3 builds per program, both targets, and the ABI torture) | 14.6 s wall, 150 s CPU |
| ... with the include-probe cache (3 alternating runs each) | 14.2 s wall (14.10-14.19), 140 s CPU (139.8-140.9), against 14.5-14.7 s and 150.7-152.4 s without |

The suites, not compilation, set the pace of `verify fast`: one fcc compilation of a small file
is 20 ms. Most of the C corpus's time goes to running the programs under qemu-user and to the
reference compilers.

## What other compilers do

From primary sources (each claim links to one; "unverified" marks what couldn't be checked):

- **Emitting objects directly.** LLVM's MC project counted the external assembler at about 20%
  of compile time for C at `-O0 -g` and built the integrated assembler to remove the
  text round trip ([LLVM blog, 2010](https://blog.llvm.org/2010/04/intro-to-llvm-mc-project.html)).
  Go needs "no assembler pass in the usual pipeline" ([go.dev/doc/asm](https://go.dev/doc/asm));
  Cranelift writes objects with `cranelift-object` ([docs.rs](https://docs.rs/cranelift-object)).
  Zig's self-hosted x86-64 backend emits machine code directly and is the default for Debug
  builds since 0.15, with debug compiles about 5x faster than through LLVM "in most cases"
  ([0.15.1 release notes](https://ziglang.org/download/0.15.1/release-notes.html)). On fai's
  output, LLVM's integrated assembler (`llvm-mc`) was 3x *slower* than GNU `as`, so the gain is
  in not printing and reparsing text, not in another text assembler.
- **Fast `-O0` code generation.** LLVM at `-O0` selects with FastISel (GlobalISel on AArch64)
  and allocates with RegAllocFast, block-locally, with no liveness analysis or interference
  graph ([RegAllocFast.cpp](https://github.com/llvm/llvm-project/blob/main/llvm/lib/CodeGen/RegAllocFast.cpp),
  [TargetPassConfig.cpp](https://github.com/llvm/llvm-project/blob/main/llvm/lib/CodeGen/TargetPassConfig.cpp)).
  TPDE does selection, allocation, and encoding in one pass and reports 8-24x faster than LLVM
  `-O0` on SPECint 2017 ([arXiv 2505.22610](https://arxiv.org/abs/2505.22610)).
- **Caching.** ccache keys on the compiler's identity (by default its modification time and
  size) and hashes `CPATH`, `C_INCLUDE_PATH`, and similar variables into its manifest key
  ([manual](https://ccache.dev/manual/latest.html),
  [ccache.cpp](https://github.com/ccache/ccache/blob/master/src/ccache/ccache.cpp)). Zig's cache
  manifests record inode, modification time, and a content hash per input, distrust a
  modification time within the current timestamp tick, and identify the compiler by hashing it
  and its libraries ([0.4.0 release notes](https://ziglang.org/download/0.4.0/release-notes.html));
  a `zig cc -c` cache hit took 0.01 s against 0.12 s cold
  ([Kelley, 2020](https://andrewkelley.me/post/zig-cc-powerful-drop-in-replacement-gcc-clang.html)).
  Zig reads Nix's `NIX_CFLAGS_COMPILE` and `C_INCLUDE_PATH` itself rather than running a
  compiler ([NativePaths.zig](https://github.com/ziglang/zig/blob/master/lib/std/zig/system/NativePaths.zig)),
  but its libc detection still runs `$CC -E -Wp,-v` uncached
  ([LibCInstallation.zig](https://github.com/ziglang/zig/blob/master/lib/std/zig/LibCInstallation.zig)).
  Clang's driver finds a Linux target's include directories in process, with no subprocess and
  no cache ([Linux.cpp](https://github.com/llvm/llvm-project/blob/main/clang/lib/Driver/ToolChains/Linux.cpp)).
- **Incremental compilation.** rustc records the queries each result read and, on a rebuild,
  reuses results whose inputs' hashes are unchanged ("red-green", with early cutoff:
  [rustc dev guide](https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation.html)).
  Zig's incremental mode patches the output binary per top-level declaration; its 2026 devlog
  reports 228-288 ms incremental rebuilds of the Zig compiler itself against 36 s from scratch
  ([devlog](https://ziglang.org/devlog/2026/)).
- **Parallelism.** rustc's parallel front end (`-Z threads=8`) cut compile times by up to 50%,
  with up to 35% more memory ([Rust blog, 2023](https://blog.rust-lang.org/2023/11/09/parallel-rustc/));
  GCC's WHOPR partitions link-time optimization into parallel jobs
  ([GCC internals](https://gcc.gnu.org/onlinedocs/gccint/LTO-Overview.html)). Zig 0.15 runs
  semantic analysis, code generation, and linking in parallel (its self-build went from 13.8 to
  10.0 s on one system, per the release notes above).
- **Process startup.** Clang's in-process cc1 (`-fintegrated-cc1`) targeted Windows, where a
  process costs 30-100 ms; on Linux its authors measured no meaningful difference (6m20s against
  6m18s for a build; [D69825](https://reviews.llvm.org/D69825)).
- **Measuring.** Clang's `-ftime-trace` ([Pranckevičius, 2019](https://aras-p.info/blog/2019/01/16/time-trace-timeline-flame-chart-profiler-for-Clang/)),
  GCC's `-ftime-report` ([developer options](https://gcc.gnu.org/onlinedocs/gcc/Developer-Options.html)),
  and rustc's `-Z self-profile` ([unstable book](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/self-profile.html))
  are what `FIR_TIME` imitates.

These are design comparisons. fai compiles FIR and C (through fcc), not Rust, C++, or Zig.

## Next steps, in order

Each step is ranked by the cost it removes, as measured above.

1. **Write object files directly instead of assembly text.** This removes the largest cost at
   every size above a few hundred lines:
   - 337 of 790 ms on 1,600 functions on Linux;
   - 1,215 of 1,439 ms on macOS, where the host assembler is LLVM's and 3× slower than GNU
     `as` on fai's output;
   - 5.9 of 22 ms, as a process, on a small file;
   - and the 21-47 ms spent printing and writing the text.

   The backends already hold every instruction as a value (`mir::Inst`). An encoder and an ELF
   and Mach-O writer would replace printing for objects, with relocations, and with debug line
   tables for `-g`. Linking would still go through `cc`. Go, Zig, and Cranelift work this way.
   Check it differentially: assemble the current text with GNU `as` and compare the result
   byte for byte with the direct object over every corpus. Keep `--emit asm`. The risk is
   encoding and relocation bugs, which that comparison is designed to catch.
2. **Use all the cores on large inputs.** Selection, emission, verification, lowering, and the
   passes run per function on one thread: about 200 ms of 790 on 1,600 functions. Register
   allocation already runs in parallel. This needs care in shared code: the codegen track owns
   `isel.rs`.
3. **Cut fcc's fixed cost: about 9 ms of a 22 ms small compilation is outside any phase.**
   About 5 ms of that is loading the Clang and LLVM shared libraries before `main`, the rest
   Clang's setup and exit.
   - Two ways: link Clang statically, or keep fcc resident as a compile server (sccache's and
     Zig's `--watch` model).
   - Measure first: Clang's in-process cc1 found little on Linux (D69825).
   - Until objects are direct, `-c` could also run `as` itself rather than the GCC driver, which
     costs 4.7 ms against `as`'s 1.1 ms on an empty file. On x86-64 the host's Nix `cc`
     wrapper takes 13.5 ms to assemble.
4. **Don't verify the HFIR twice:** about 17 ms on 1,600 functions, 2%. This needs a "verified
   and unchanged since" mark that every mutating C API call clears.
5. **The proved DCE checker's cost** (for the proof track): it multiplies a large compilation's
   time by 10. Profiling the text round trip and the checker would show where it goes.
6. **Faster rebuilds of the compiler.**
   - Release builds aren't incremental, so editing `fai-ir` costs a 4.4 s rebuild. An
     incremental release profile for development would cut that; its effect hasn't been
     measured.
   - `verify fast` spends 239 s in the debug test suites, which is more than any compilation.
7. **Register assignment on very large functions:** 91 ms on 6,400 statements, now more than
   the validator.
8. **Zero-filled globals as `.zero` or `.bss`** ([c-baseline.md](c-baseline.md), bottleneck 4).
   `sieve` takes 73 ms where the other programs take about 22, because its zeroed megabyte is
   printed byte by byte and then assembled. This changes the output's layout (data, not code),
   so it belongs with the codegen track.

The research above suggests one more idea, not ranked because nothing here measured it:
caching whole compilations by content, Zig- or ccache-style, for repeated compilations of the
same file.

## Limits of this study

- **Hosts.** One x86-64 Linux machine and one Apple M4 Max, both shared with other work: the
  tables give medians, quartiles, and ranges over shuffled rounds, and the load averages. No
  AArch64 Linux machine was measured natively, and no x86-64 Mac exists in the toolchain.
- **What runs on macOS.** fcc makes Linux binaries only; the Darwin dev shell has no Linux C
  library, so on the Mac fcc compiled only header-free inputs (the generated workloads), to
  assembly. `fir compile --os darwin` ran the whole pipeline, with the host's assembler.
- **Inputs.** Twelve small kernels and generated C. Real C (large headers, many translation
  units) would weigh Clang's share more.
- **Cold runs.** The page cache was never dropped (no root): "first run" is a cold include-probe
  cache, not a cold disk. fai has no incremental compilation, so there is no incremental case to
  measure.
- **The differential run** of the old and new validators was done once and is not in the tree;
  the model test that stays guards the representation.

## Reproducing

```sh
nix develop
cargo build --release --bin fir && cmake -S frontends/c -B build/fcc -G Ninja && cmake --build build/fcc

# One compilation, phase by phase
FIR_TIME=1 build/fcc/fcc benchmarks/c/programs/matmul.c -O -o /tmp/m.o
FIR_TIME=1 target/release/fir compile FILE.mfir -O --emit asm -o /dev/null

# The tables (target/compilebench/report.md); against a baseline built from 045d398:
git archive 045d398 | tar -x -C /tmp/base && (cd /tmp/base && cargo build --release --bin fir &&
  cmake -S frontends/c -B build/fcc -G Ninja && cmake --build build/fcc)
python3 -B benchmarks/compile/compilebench.py run \
    --fcc base=/tmp/base/build/fcc/fcc --fir base=/tmp/base/target/release/fir

# The validator's model test, with more programs, and the include-probe cache's test
REGCHECK_STATE_SEEDS=3000 cargo test --release -p fai-target-aarch64 --lib state_agrees
cargo test --release -p fir-capi --test fcc_cache
```

On macOS the same harness doesn't run, since it needs the Linux toolchain. The M4 Max figures
came from interleaved runs of `fir compile -O --os darwin` (to assembly and, with the host's
`cc`, to an object), fcc `-O --emit asm`, and the dev shell's Clang on the generated workloads,
measured with the same `wait4` method and checked for identical outputs.
