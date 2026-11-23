# fai against GCC, Clang, and arocc

This compares fai's C compiler (`fcc`) with GCC, Clang, and arocc on everything measurable: how
fast each compiles, how fast and how large the code it makes is, how much memory each uses, what
C each accepts, and whether the programs behave the same. Every number was measured at `972e7dc`
(`main`), on the machines below, by the three harnesses in `benchmarks/`; the commands are at the
end. The generated tables are in [compilers-report.md](compilers-report.md).

Earlier studies cover parts of this in more depth: [c-baseline.md](c-baseline.md) (fcc's code
on the 12 kernels, and why it is slow) and [compile-speed.md](compile-speed.md) (fcc's compile
time, phase by phase). This one adds two real projects, Lua 5.4.7 and SQLite 3.53.3, C23, and
arocc, and re-measures the rest at the current revision.

**Since this was measured**, instruction selection changed
([selection.md](selection.md)): `fcc -O` executes 1.22× GCC `-O0`'s instructions on Lua and
0.63× on SQLite's speedtest1, from 2.27× and 1.16×. The times below were not measured again.

## Summary

- **Behavior: no difference found.** Every build of every program prints the same output as
  GCC `-O2`'s build: the 12 kernels under all 7 configurations; Lua's own test suite (28 of 28
  files) and 7 Lua workloads under fcc, `fcc -O`, GCC and Clang at `-O0` and `-O2`; SQLite's
  speedtest1, whose `--verify` hash of every query result is identical for all six builds,
  under qemu and natively; and the 27 C23 programs under GCC, Clang, and fcc.
- **Program speed: fcc's code is the slowest of all.** Natively on an Apple M4 Max, `fcc -O`
  takes 3.14× GCC `-O2`'s time on the kernels, and 5.23× on Lua and SQLite. Unoptimized
  GCC and Clang are faster: 2.36× and 2.21× on the kernels, 3.63× and 3.99× on the projects. fcc's
  `-O` gains 1% on the kernels and 6% on the projects.
- **Executed instructions: 5.2× GCC `-O2`'s on the kernels, 5.8× on the projects** (GCC `-O0`:
  3.3× and 2.8×; Clang `-O0`: 3.1× and 2.6×). 84-88% of fcc's memory accesses go to the stack,
  as at `-O0`; GCC and Clang `-O2` send 29-47% there.
- **Code size: 2.5-3.6× GCC `-O2`'s**, 2.1-2.9× GCC's and Clang's `-O0`: 3.63× GCC `-O2`'s on
  the kernels' objects, 3.13× on Lua's, 2.48× on SQLite's.
- **Compile speed: as fast as an unoptimized compiler, not as fast as Clang `-O0`.** On small
  files fcc `-O` takes 22.5 ms (geometric mean), against Clang `-O0` 14.7, GCC `-O0` 20.2,
  Clang `-O2` 23.8, and GCC `-O2` 35.6. On generated code it is up to 2.2× faster than GCC
  `-O0` (as fast on one 6,400-statement function) and 1.6-2.3× slower than Clang `-O0`. A whole
  build of Lua takes 1.46 s serially (Clang `-O0` 0.79, GCC `-O0` 1.30, GCC `-O2` 3.97);
  SQLite's 269,613-line amalgamation 1.35 s (Clang `-O0` 0.74, GCC `-O0` 2.17, GCC `-O2` 15.4,
  Clang `-O2` 8.5). `-O` costs fcc 0-7%.
- **Compile memory: between GCC and Clang.** fcc loads Clang and LLVM's shared libraries: about
  70 MiB for a small file (GCC 38, Clang 99), 257 MiB for `sqlite3.c` (GCC `-O0` 317, Clang `-O0`
  187, either `-O2` 360-384).
- **arocc is the fastest and smallest frontend, but it can't make code yet.** Parsing and
  checking only, it takes 33% less time than Clang on Lua and 2.9× less on small files, in 30 MiB
  instead of 82-120 MiB. It has no code generator ("TODO implement lowering functions" for any
  function), so it is compared as a frontend only. It accepts all of Lua and SQLite and 17 of the
  27 C23 programs.
- **C23:** GCC, Clang, and fcc run all 27 C23 programs identically. fcc accepts exactly what
  Clang accepts, because Clang is its frontend: neither takes storage classes in compound
  literals or `_Float32`/`_Float64`, which GCC and arocc accept. arocc rejects 10: 9 are gaps in
  arocc, and 1 uses a C2y feature that arocc is right to refuse.
- **Where fcc loses the most, in order:** every local lives in the stack frame (the instruction
  and memory-traffic gap); instruction selection works one IR op at a time; `goto *` through a
  label table compiles to a switch at every `goto *`, which makes Lua's interpreter loop 4.7×
  slower to compile than without it; zero-filled globals go to the assembler byte by byte
  (`sieve`: 71 ms against 20); and the external assembler and linker are 20-30% of a build.

## The compilers

| | fcc (fai) | GCC | Clang | arocc |
|---|---|---|---|---|
| Version | `972e7dc` | 16.2.0 (AArch64 cross) | 23.1.3 | `2acd4ac` (2026-11-12) |
| Written in | Rust (IR, passes, backends: 70k lines), C++ (the C frontend: 5k), Lean 4 (spec and proofs: 20k) | C++ | C++ | Zig (55k lines) |
| C frontend | Clang 23.1.3's, as a library | its own | its own | its own |
| IR and optimizer | FIR (HFIR, MFIR, LFIR); `-O` runs proved passes (DCE, DSE, store forwarding, copy propagation); no register promotion by default | GIMPLE and RTL, `-O0` to `-O3` | LLVM IR, `-O0` to `-O3` | none yet |
| Code generation | own AArch64 and x86-64 (the integer subset) backends, assembly text, external `as` | own, in process | own, in process (integrated assembler) | none yet (its README: "under construction") |
| Targets measured | AArch64 Linux, x86-64 Linux | both | both | parsing for AArch64 Linux |
| How it is checked | a Lean specification and proofs for the passes; a Lean checker can check every DCE step (`--check-dce`); a validator checks every register allocation; differential tests against GCC | test suites | test suites | test suites |
| Size of the binary | `fcc` 5.7 MB, plus Clang's `libclang-cpp` (97 MB) and `libLLVM` (205 MB), shared | `cc1` 51 MB | `clang` 0.2 MB, plus the same `libclang-cpp` and `libLLVM` | 15.8 MB, static |

What fcc doesn't support, each diagnosed with its location (from
[frontends/c/README.md](../../frontends/c/README.md)): `long double`, `_Complex`, and the other
float formats; variable-length arrays; `_Atomic` objects (the atomic builtins work); thread-local
variables; inline assembly; statement expressions; packed structs and alignments over 16; wide
string literals; K&R definitions; integers over 128 bits, and 128-bit integers on x86-64; a few
by-value struct ABIs. GCC and Clang support all of these (K&R definitions only before C23).
fcc has no debug information (no `-g`) and no `-O2`-style optimization. Every function and
global is a global symbol (FIR has no linkage); `static` names get a per-file suffix.

## The machines and method

| | |
|---|---|
| Build host | AMD Ryzen 9 9950X (16 cores, 32 threads), NixOS, Linux 6.18.60. Load average 0.1-1.5 during the compile timings |
| Native AArch64 | Apple M4 Max (16 cores), macOS 26, in Docker Desktop 29.9.3's arm64 Linux VM (16 vCPUs, `alpine:3.22`): native execution, virtualized, not emulated (`CPU implementer 0x61`). The Mac was shared: load average 2-3 |
| Toolchain | the dev shell (`nix develop`, `flake.lock`'s nixpkgs): GCC 16.2.0 and binutils 2.46 for AArch64, Clang/LLVM 23.1.3, glibc 2.44 (static), qemu-user 11.1.2, rustc 1.99.0. arocc built with Zig 0.18.0-dev.1005, as its `build.zig.zon` asks |
| Flags | fcc as shipped, with `-O` where named. GCC and Clang get `-ffp-contract=off` and no Nix hardening; Clang (and arocc) get exactly fcc's Clang setup: the target, `-nostdlibinc`, the cross GCC's include directories. All link statically against the same glibc |
| Projects | Lua 5.4.7 (33 files, `-std=c23 -DLUA_COMPAT_5_3 -DLUA_USE_POSIX`); SQLite 3.53.3, the amalgamation (`sqlite3.c`, 269,613 lines) and `speedtest1.c` (`-std=gnu23 -DNDEBUG -DSQLITE_THREADSAFE=0 -DSQLITE_OMIT_LOAD_EXTENSION`). Sources pinned by SHA-256 |
| Compile time | wall and CPU time (with the children waited for: the assembler, the linker) and peak RSS from `wait4`. compilebench: medians of 10 shuffled rounds after a warmup. cbench: the minimum of 5 runs. projbench: the minimum of 5 shuffled rounds |
| Run time | medians of interleaved rounds after a warmup, through cbench's `benchrun`, which checks every run's output and refuses to time under emulation. Kernels: 7 rounds. Lua and speedtest1: 11 rounds |
| Instructions | exact counts of executed AArch64 instructions under qemu-user (cbench's TCG plugin), split into the program's own code and libc by the linker map |

## Behavior

| | fcc | `fcc -O` | GCC `-O0` | GCC `-O2` | Clang `-O0` | Clang `-O2` |
|---|---|---|---|---|---|---|
| 12 kernels: output = GCC `-O2`'s (qemu; also natively, every timed run) | 12 | 12 | 12 | 12 | 12 | 12 |
| Lua's test suite, files passing (qemu) | 28/28 | 28/28 | 28/28 | 28/28 | 28/28 | 28/28 |
| Lua workloads: output = GCC `-O2`'s (qemu, and natively every run) | 7/7 | 7/7 | 7/7 | 7/7 | 7/7 | 7/7 |
| speedtest1 `--verify` hash = GCC `-O2`'s (qemu at size 5, natively at size 60) | yes | yes | yes | yes | yes | yes |

GCC `-O1` (cbench's seventh configuration) also matches on the kernels. The C23 programs are
below. In the work that led to this revision, fcc also passed SQLite's own TCL tests: it
compiled all 102 library files of SQLite's split build into SQLite's `testfixture`, and the 102
of 104 sampled test files that pass with GCC's build passed with fcc's, with and without `-O`.
That was not rerun here.

## Program speed

### The 12 kernels (cbench)

Native wall time on the M4 Max, median of 7 rounds, as a ratio to GCC `-O2` (geometric mean
over the 12 programs), with executed instructions and code size:

| | fcc | `fcc -O` | GCC `-O0` | GCC `-O1` | GCC `-O2` | Clang `-O0` | Clang `-O2` |
|---|---:|---:|---:|---:|---:|---:|---:|
| Run time | 3.18× | 3.14× | 2.36× | 1.08× | 1.00× | 2.21× | 0.94× |
| Executed instructions, own code | 5.23× | 5.20× | 3.26× | 1.22× | 1.00× | 3.06× | 0.89× |
| Executed instructions, with libc | 4.48× | 4.47× | 2.99× | 1.16× | 1.00× | 2.80× | 0.88× |
| Code size (`.text` of the object) | 3.68× | 3.63× | 1.27× | 0.74× | 1.00× | 1.31× | 0.80× |
| Memory accesses (all 12, millions) | 310 | 307 | 309 | 67 | 52 | 311 | 52 |
| ... to the stack | 88% | 88% | 88% | 41% | 47% | 86% | 29% |

Per program, `fcc -O` against GCC `-O2` runs from 1.29× (`bintree`, mostly glibc's `malloc`)
to 13.6× (`matmul`, a tight loop over arrays). The geometric means are within 1% of the
[c-baseline](c-baseline.md) measurement, and the instruction counts are identical: fcc's code for
these kernels hasn't changed since.

### Lua and SQLite (projbench)

Native wall time on the M4 Max, median of 11 rounds, in seconds, with the ratio to GCC `-O2`.
Lua runs each script with its argument (`fib 35`, `trees 15`, `nbody 400000`, `spectral 400`,
`strings 300000`, `sort 400000`, `fannkuch 10`); speedtest1 runs at `--size 60` in memory:

| workload | fcc | `fcc -O` | GCC `-O0` | GCC `-O2` | Clang `-O0` | Clang `-O2` |
|---|---:|---:|---:|---:|---:|---:|
| lua fannkuch | 7.420 (5.94×) | 6.825 (5.46×) | 5.380 (4.30×) | 1.250 | 6.761 (5.41×) | 1.153 (0.92×) |
| lua fib | 1.487 (7.09×) | 1.451 (6.92×) | 0.937 (4.47×) | 0.210 | 1.189 (5.67×) | 0.223 (1.06×) |
| lua nbody | 2.776 (6.04×) | 2.539 (5.53×) | 1.833 (3.99×) | 0.459 | 2.176 (4.74×) | 0.411 (0.89×) |
| lua sort | 1.455 (8.05×) | 1.398 (7.74×) | 0.576 (3.19×) | 0.181 | 0.641 (3.55×) | 0.180 (1.00×) |
| lua spectral | 0.879 (8.55×) | 0.826 (8.04×) | 0.661 (6.42×) | 0.103 | 0.779 (7.57×) | 0.120 (1.17×) |
| lua strings | 0.661 (3.02×) | 0.625 (2.85×) | 0.458 (2.09×) | 0.219 | 0.454 (2.07×) | 0.222 (1.01×) |
| lua trees | 1.844 (4.01×) | 1.774 (3.86×) | 1.155 (2.51×) | 0.460 | 1.381 (3.00×) | 0.468 (1.02×) |
| speedtest1 | 3.375 (4.12×) | 3.185 (3.89×) | 3.012 (3.68×) | 0.818 | 2.148 (2.62×) | 0.821 (1.00×) |
| **geometric mean** | **5.53×** | **5.23×** | **3.63×** | **1.00×** | **3.99×** | **1.01×** |

`fcc -O` against the unoptimized compilers: 1.44× GCC `-O0`'s time and 1.31× Clang `-O0`'s
(geometric means), from 1.06× GCC `-O0` on speedtest1 to 2.43× on `lua sort`. Peak memory while
running is the same for every build, within 2.5 MiB (Lua 1-72 MiB by script, speedtest1 86-88
MiB).

Executed instructions in the project's own code (exact, under qemu at the small sizes, millions,
ratio to GCC `-O2`):

| workload | fcc | `fcc -O` | GCC `-O0` | GCC `-O2` | Clang `-O0` | Clang `-O2` |
|---|---:|---:|---:|---:|---:|---:|
| lua fannkuch | 156.0 (6.31×) | 154.0 (6.23×) | 68.1 (2.75×) | 24.7 | 66.9 (2.71×) | 25.9 (1.05×) |
| lua fib | 26.1 (6.53×) | 25.9 (6.49×) | 11.7 (2.92×) | 4.0 | 11.7 (2.94×) | 4.5 (1.14×) |
| lua nbody | 328.4 (5.70×) | 332.1 (5.76×) | 145.3 (2.52×) | 57.6 | 142.3 (2.47×) | 58.6 (1.02×) |
| lua sort | 234.8 (6.79×) | 233.3 (6.75×) | 81.6 (2.36×) | 34.6 | 83.2 (2.41×) | 35.9 (1.04×) |
| lua spectral | 207.6 (6.85×) | 204.9 (6.76×) | 89.5 (2.95×) | 30.3 | 88.5 (2.92×) | 33.0 (1.09×) |
| lua strings | 57.7 (4.38×) | 57.1 (4.34×) | 28.6 (2.17×) | 13.2 | 28.6 (2.17×) | 14.2 (1.08×) |
| lua trees | 126.4 (5.76×) | 124.9 (5.69×) | 58.9 (2.68×) | 21.9 | 57.3 (2.61×) | 22.5 (1.03×) |
| speedtest1 | 5,293 (5.07×) | 5,242 (5.02×) | 4,507 (4.32×) | 1,044 | 2,375 (2.27×) | 1,072 (1.03×) |
| **geometric mean** | **5.86×** | **5.82×** | **2.78×** | **1.00×** | **2.55×** | **1.06×** |

Instruction mix of the projects' own code, over all eight workloads:

| | executed | load | store | move | ALU | compare | branch | call | memory accesses | to the stack |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| fcc | 6,431M | 24.4% | 9.8% | 16.1% | 27.7% | 10.1% | 8.4% | 0.8% | 2,198M | 84% |
| `fcc -O` | 6,375M | 23.6% | 9.9% | 16.2% | 28.0% | 10.2% | 8.5% | 0.8% | 2,137M | 84% |
| GCC `-O0` | 4,990M | 22.6% | 8.3% | 3.9% | 10.4% | 26.0% | 27.8% | 0.9% | 1,542M | 78% |
| GCC `-O2` | 1,231M | 25.4% | 10.2% | 12.2% | 20.5% | 9.4% | 19.3% | 1.7% | 439M | 32% |
| Clang `-O0` | 2,853M | 39.9% | 16.1% | 3.7% | 19.3% | 0.6% | 17.9% | 1.6% | 1,596M | 78% |
| Clang `-O2` | 1,267M | 25.7% | 10.3% | 10.7% | 21.5% | 9.3% | 19.6% | 1.6% | 460M | 34% |

Code size:

| | fcc | `fcc -O` | GCC `-O0` | GCC `-O2` | Clang `-O0` | Clang `-O2` |
|---|---:|---:|---:|---:|---:|---:|
| Lua's 33 objects, `.text` bytes | 573,108 | 569,252 (3.13×) | 260,072 | 181,884 | 273,604 | 199,936 |
| `sqlite3.o` + `speedtest1.o`, `.text` bytes | 2,137,416 | 2,120,536 (2.48×) | 1,029,764 | 855,000 | 1,042,620 | 972,048 |
| static `lua` binary, bytes | 1,680,408 | 1,680,472 | 1,372,080 | 1,226,920 | 1,372,896 | 1,291,944 |
| static `speedtest1` binary, bytes | 3,341,704 | 3,341,704 | 2,162,720 | 1,986,360 | 2,229,544 | 2,052,584 |

**What the differences say.** fcc's code does what `-O0` code does (every value goes through
the stack: 84% of its memory accesses), and then more: 2.0-2.9× GCC `-O0`'s instructions on
Lua, because instruction selection lowers one IR op at a time with no folding: its 16% of plain
moves (GCC `-O0`: 4%) are largely that overhead. The gap is smaller in time than in
instructions (5.2× against 5.8× GCC `-O2`'s on the projects: on the M4, store-to-load
forwarding hides much of the stack traffic) and smallest where a program spends its time in
libc or on memory (`bintree` 1.29×, `lua strings` 2.85×). `-O` gains only 1-6%, because its
passes (dead code and dead store elimination, store forwarding, copy propagation) can't remove
what costs the most: the stack slots themselves. Register promotion (`mem2reg`) exists but is
experimental and off.

Notable details:

- `-O` saves fcc 0.5-1.3% of its instructions on Lua (on `nbody` it adds 1%) but 2.5-9% of the
  time (6% on average). It removes 2.8% of the memory accesses, which likely accounts for more
  time than their share of instructions suggests.
- On Lua, GCC `-O0` and Clang `-O0` execute the same number of instructions within 2%, yet Clang
  `-O0` takes 0.99-1.27× GCC `-O0`'s time: 56% of its instructions are loads and stores, against
  GCC `-O0`'s 31% (all workloads). On speedtest1 it is the other way: GCC `-O0` executes 1.9×
  Clang `-O0`'s instructions (4,507M against 2,375M) and takes 1.4× its time.
- On speedtest1, fcc is close to GCC `-O0`: 1.16× its instructions and 1.06× its time, against
  2.0-2.9× and 1.25-2.43× on Lua.
- fcc reaches a `volatile` access through a helper call (`__fcc_vload32`, FIR has no volatile
  operation): 0.4% of Lua's executed instructions under `fib`.

## Compile speed

### Small and generated files (compilebench)

Median wall time of one compilation to an object file, in ms, on the build host (10 rounds):

| | fcc `-O` | fcc `-O`, to assembly | `fir compile -O` (no C, no assembler) | Clang `-O0` | Clang `-O2` | GCC `-O0` | GCC `-O2` |
|---|---:|---:|---:|---:|---:|---:|---:|
| 12 kernels (geometric mean) | 22.5 | 15.3 | 3.3 | 14.7 | 23.8 | 20.2 | 35.6 |
| 100 functions × 10 statements (1,401 lines) | 68 | 44 | 24 | 43 | 280 | 121 | 227 |
| 400 × 10 (5,601 lines) | 197 | 117 | 66 | 129 | 1,046 | 426 | 603 |
| 1,600 × 10 (22,401 lines) | 748 | 436 | 265 | 465 | 4,215 | 1,662 | 2,201 |
| 1 function × 400 statements | 39 | 26 | 14 | 22 | 97 | 41 | 195 |
| 1 × 1,600 | 114 | 76 | 50 | 56 | 461 | 123 | 798 |
| 1 × 6,400 | 502 | 362 | 261 | 215 | 4,136 | 512 | 4,456 |

For x86-64 objects (fcc's integer subset, so 9 of the 12 kernels): fcc `-O` 33.7 ms (geometric
mean), Clang `-O0` 20.3, GCC `-O0` 18.6; on 1,600 functions 715, 539, and 1,505 ms; on one
6,400-statement function 419, 190, and 406 ms.

fcc's `-O` changes its compile time by 0-6%. To assembly, fcc takes 15.3 ms on the kernels
(geometric mean); the external assembler makes that 22.5 ms to an object, a step Clang's
integrated assembler doesn't pay for (Clang `-O0`: 14.7 ms to an object). CPU
time is higher than wall time on large inputs (1,600 functions: 976 ms CPU for 748 wall), because
fcc's backend runs on worker threads.

The outlier is `sieve`: 71 ms against 20 for GCC `-O0`. Its 1 MiB zero-filled global array is
written to the assembly file as bytes, and the assembler takes 42 ms to read them (with
`--target x86_64`, 77 ms).

### Whole projects (projbench)

Serial build, every file compiled once, minimum of 5 rounds (wall ms; CPU ms; peak RSS of any
one compilation):

| | fcc | `fcc -O` | GCC `-O0` | GCC `-O2` | Clang `-O0` | Clang `-O2` |
|---|---:|---:|---:|---:|---:|---:|
| Lua, 33 files, wall | 1,433 | 1,457 | 1,303 | 3,968 | 792 | 2,228 |
| Lua, CPU | 1,333 | 1,357 | 1,204 | 3,850 | 755 | 2,180 |
| Lua, peak RSS (MiB) | 142 | 142 | 67 | 87 | 111 | 130 |
| `sqlite3.c`, wall | 1,261 | 1,352 | 2,165 | 15,383 | 735 | 8,459 |
| `speedtest1.c`, wall | 85 | 85 | 83 | 408 | 36 | 176 |
| SQLite, CPU | 1,687 | 1,785 | 2,101 | 15,524 | 761 | 8,529 |
| SQLite, peak RSS (MiB) | 257 | 254 | 317 | 360 | 187 | 384 |

On `sqlite3.c` fcc is 1.7× faster than GCC `-O0` and 12× faster than GCC `-O2`, and 1.7×
slower than Clang `-O0`. On Lua it is 1.1× slower than GCC `-O0`, because of one file:
`lvm.c` takes fcc 446 ms (GCC `-O0` 109, Clang `-O0` 56, GCC `-O2` 520). Lua's interpreter loop
dispatches with labels as values (`goto *` through a table of `&&label`s, its default with a
GNU-compatible compiler). fcc compiles each of its roughly 80 `goto *`s to a switch over every
address-taken label, and register allocation over that control flow takes 73% of the file's
time. With `-DLUA_USE_JUMPTABLE=0` (a plain `switch`), fcc compiles `lvm.c` in 97 ms. Of the
other 32 files, fcc is slower than GCC `-O0` only on the three smallest (`lctype.c`, `linit.c`,
`lopcodes.c`: 15-18 ms against 12-16).

Where fcc's time goes on the projects (the largest phases' self time, summed over the files,
`FIR_TIME=1`, ms; phases marked `*` run on worker threads and are CPU time, not part of the
total):

| phase | Lua, `-O` | SQLite, `-O` |
|---|---:|---:|
| Clang: preprocess, parse, analyze | 309 | 244 |
| lowering Clang's AST to HFIR | 40 | 107 |
| verifying the IR (every verification) | 33 | 133 |
| HFIR to MFIR, and the `-O` passes | 28 | 142 |
| AArch64 instruction selection | 13 | 54 |
| register allocation (main thread) | 371 | 57 |
| register allocation, assignment * | 91 | 126 |
| register allocation validation * | 316 | 486 |
| writing assembly text | 143 | 221 |
| the external assembler and linker driver | 276 | 411 |
| **total, main thread** | **1,225** | **1,410** |

### Parse and check only, with arocc

`-fsyntax-only`, minimum of 5 rounds, wall ms summed over the files (each a separate process);
fcc's own Clang phase and its lowering are in-process times from `FIR_TIME=1`, without process
start:

| inputs | GCC | Clang | arocc | fcc: Clang phase | fcc: AST to HFIR |
|---|---:|---:|---:|---:|---:|
| 12 kernels | 175 | 135 | 46 | 60 | 2.6 |
| Lua, 33 files | 593 | 503 | 337 | 293 | 39 |
| `sqlite3.c` + `speedtest1.c` | 218 | 243 | 206 | 243 | 108 |
| generated: 1,600 functions, and one of 6,400 statements | 111 | 135 | 82 | 128 | 140 |

Peak memory: arocc 30 MiB on every Lua file and 76 MiB on `sqlite3.c`; GCC 30-42 and 100;
Clang 80-88 and 120. arocc checks a 64-line file (`lctype.c`) in 2.6 ms, against 11-12 ms for
GCC and Clang: its lead on small files is mostly start-up. It is slower than both on one
file: Lua's `lvm.c`, 64 ms against GCC's 34 and Clang's 32. It accepted every file of both projects.

## C23

The 27 C23 programs of fcc's corpus (`frontends/c/tests/c23_*.c`), compiled with `-std=c23`,
linked, and run under qemu with GCC, Clang, and fcc; arocc checks each (`-fsyntax-only`); plus
the two C23 features fcc's corpus records as errors because Clang lacks them:

| program | GCC | Clang | fcc | arocc |
|---|---|---|---|---|
| 17 programs: attributes, `auto`, `_BitInt`, wide `_BitInt`, `true`/`false`/`bool`, `<stdckdint.h>`, `constexpr` aggregates, `#embed`, `= {}`, labels, the C23 library, literals, prototypes, `static_assert`, unnamed parameters, `unreachable`, `va_start` without a name | runs | same output | same output | accepts |
| `c23_bitint_builtins`, `c23_stdbit` | runs | same | same | rejects: no `__builtin_stdc_leading_ones` and the other `__builtin_stdc_*` that glibc's `<stdbit.h>` uses with GCC 14 or later |
| `c23_constexpr` | runs | same | same | rejects: a `constexpr` struct's member as a `case` value |
| `c23_enum_fixed` | runs | same | same | rejects: an enum with a fixed underlying type named in `_Generic` |
| `c23_generic_qualifiers` | runs | same | same | rejects: `int` and `const int` as two `_Generic` associations (they are not compatible types, so C23 allows both) |
| `c23_keywords` | runs | same | same | rejects: `ULLONG_WIDTH` (arocc's own `<limits.h>` defines it as `__LLONG_WIDTH__`, which arocc doesn't predefine) |
| `c23_nullptr` | runs | same | same | rejects: `bool b = nullptr;` (C23 allows it) |
| `c23_preprocessor` | runs | same | same | rejects: `__VA_ARGS__` inside `__VA_OPT__(...)` (`#define SUM(first, ...) (first __VA_OPT__(+ sum_rest(__VA_ARGS__)))`) |
| `c23_tag_compat` | runs | same | same | rejects: redefining an identical struct tag (C23's tag compatibility) |
| `c23_typeof` | runs | same | same | rejects: a type name as `_Generic`'s controlling operand. That is C2y, not C23: arocc is right, and GCC and Clang accept it as an extension |
| storage classes in compound literals (`(static int){0}`) | accepts | rejects | rejects | accepts |
| `_Float32`, `_Float64` | accepts | rejects | rejects | accepts |

fcc's C is Clang's C: whatever Clang 23 doesn't parse, fcc can't compile. The `c23_typeof` test
uses a C2y feature, so fcc's corpus should name it so, or move that one line.

## Every difference, in one list

Measured here, fcc against GCC and Clang at the same level of effort (`-O0`):

1. **Run time:** 1.33× GCC `-O0`'s and 1.42× Clang `-O0`'s on the kernels; 1.44× and 1.31× on the
   projects. Against `-O2`: 3.1× on the kernels, 5.2× on the projects.
2. **Executed instructions:** 1.2-2.9× `-O0`'s (1.6-1.7× on the kernels, 2.0-2.9× on Lua,
   1.2× GCC's and 2.2× Clang's on speedtest1), 5-6× `-O2`'s.
3. **Memory traffic:** like `-O0` (84-88% to the stack), 4-6× `-O2`'s accesses.
4. **Code size:** 2.1-2.9× `-O0`'s, 2.5-3.6× `-O2`'s; static binaries 1.2-1.5× `-O0`'s.
5. **Compile time:** 1.1× GCC `-O0` on small files and 0.45-1.0× on large ones (0.58× on
   `sqlite3.c`); 1.5× Clang `-O0` on small files and 1.6-2.3× on large ones; 0.95× Clang
   `-O2` on small files, and 0.08-0.65× either `-O2` on larger inputs. One pathology: `goto *`
   through label tables (Lua's `lvm.c`, 8× Clang `-O0`). One slow path: large zero-filled
   globals (`sieve`, 3.5× GCC `-O0`).
6. **Compile memory:** 70 MiB minimum (Clang's libraries), Clang `-O0`'s 99; up to 257 MiB on
   `sqlite3.c`, below GCC (317-360) and Clang `-O2` (384).
7. **`-O`:** gains 1% (kernels) to 6% (projects) in run time and at most 1.3% in
   instructions (on `lua nbody` it executes 1% more), and costs 0-7% in compile time. GCC's and
   Clang's `-O2` gain 2.4-4.0× in run time over their `-O0`.
8. **Behavior:** none found.
9. **Language:** fcc's C is Clang's, minus the list in "The compilers": no VLAs, `long double`,
   `_Complex`, inline assembly, statement expressions, TLS, `_Atomic` objects, and others.
10. **Tooling:** fcc writes assembly text and runs an external assembler and linker (20-30% of
    its time on the projects; Clang assembles in process); it has no debug information (no
    `-g`); its passes are proved and its register allocation is checked on every compilation,
    which no other compiler here does.

And arocc: the fastest, smallest frontend here (2.9× faster than Clang on small files, a third
of the memory), accepts both projects, misses 9 C23 features or builtins the others have, and makes
no code.

## What to do next, by what it would buy

1. **Promote locals to registers by default** (prove and enable `mem2reg`): the stack traffic
   is the largest part of every gap above (84% of fcc's memory accesses).
2. **Select instructions over more than one IR op** (addressing modes, compare and branch,
   constants): most of the 2.0-2.9× instruction ratio to GCC `-O0` on Lua is this overhead.
3. **Dispatch `goto *` once:** jump through the label's address (an indirect branch), or merge
   the per-site switches into one dispatch block, instead of a switch at every `goto *`. That
   would make `lvm.c` compile up to 4.7× faster (the plain-`switch` build's time), and should
   help Lua's run time too.
4. **Emit zero-filled globals as `.zero N`, or into `.bss`:** on `sieve` that would save most
   of the 42 ms the assembler spends reading the bytes and the 11 ms fcc spends writing them.
5. **Write objects directly** instead of assembly text for an external assembler: 20-30% of a
   project build ([compile-speed.md](compile-speed.md) has the details).

## Limits

- One machine of each kind, both shared. Run times are from the M4 Max in a Linux VM. A smaller
  AArch64 core would likely show fcc's extra instructions more, since an M4 hides much of the
  stack traffic. Spread across rounds: under 6% for most cells, and a median of 4.8%, but up to
  49% for a few short or fcc-built Lua runs (`spectral`, `fib`, `fannkuch`), most likely the VM's
  vCPUs moving to efficiency cores; the medians absorb it, and the per-cell spreads are in the
  generated report.
- The projects are two. Lua's workloads are small scripts written for this harness; speedtest1
  is SQLite's own benchmark, run in memory (`--memdb`) without its R-Tree test (not compiled in).
- x86-64 is measured for compile time only (fcc's x86-64 backend lacks floats, so neither
  project builds there).
- arocc is compared as a frontend only, at one commit of a fast-moving project.
- GCC and Clang are compared at `-O0` and `-O2` only.

## Reproducing

```sh
nix develop
uv run benchmarks/c/cbench.py all --ssh MAC --docker alpine:3.22 \
    --docker-bin '/usr/local/bin/docker --context desktop-linux'   # the kernels
uv run benchmarks/compile/compilebench.py run                     # compile latency
uv run benchmarks/projects/projbench.py prepare                   # Lua, SQLite, Lua's tests
export AROCC=/path/to/arocc/zig-out/bin/arocc                     # built with its Zig
for step in build frontend check count c23; do
  uv run benchmarks/projects/projbench.py $step --reps 5
done
uv run benchmarks/projects/projbench.py time --rounds 11 --ssh MAC --docker alpine:3.22 \
    --docker-bin '/usr/local/bin/docker --context desktop-linux'
uv run benchmarks/projects/projbench.py report                    # target/projbench/report.md
FIR_TIME=1 build/fcc/fcc -O FILE.c -o FILE.o                       # one compilation's phases
```
