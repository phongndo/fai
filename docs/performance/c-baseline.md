# fcc: the end-to-end C baseline

This is where fcc stands as a C compiler at the revision named below: whether its programs
behave like GCC's and Clang's, how its code compares with theirs, how fast it compiles, and what
costs the most. It is a baseline to measure later work against, not a target. Every number comes
from `benchmarks/c/cbench.py` (measured when it was `frontends/c/bench/cbench.py`; the move
changed no code). The commands to reproduce them are below.

fcc as of `main` at `55c1751`, renamed from `fai-cc` (which changes no code it generates). The
behavior checks, instruction counts, and run times were measured on binaries built from
`1ac29a2` with the same compiler changes. The 84 binaries built at this revision are
bit-identical to them (equal SHA-256s, which `cbench.py report` checks), because `main`'s
changes since then (the experimental promotion passes, the proved DCE checker) are opt-in. They
hold here unchanged. Compile times and code size were measured at this revision. The full
generated tables are in [c-baseline-report.md](c-baseline-report.md).

## Summary

- **Behavior: no differences found.** The 67-program differential corpus matches GCC with and
  without `-O`, and 57 programs also match at every IR layer in the interpreter. The 13 error tests
  and the ABI torture (240 signatures × 6 caller/callee pairings) pass. The 12 benchmark programs
  print exactly what GCC -O2's builds print under all 7 configurations: at the small size under
  qemu, and at the large size natively in every timed run of three independent runs. Instruction
  counts and outputs were identical across the runs.
- **Run time (native, Apple M4 Max): `fcc -O` takes 3.13× GCC -O2's time** (geometric mean over 12
  programs; 1.3× on `bintree`, which mostly runs glibc's allocator, to 13.5× on `matmul`). That is
  1.32× GCC -O0's and 1.41× Clang -O0's: fcc's code is slower
  than the other compilers' unoptimized code. `-O` gains about 1%.
- **Executed instructions: 5.2× GCC -O2's**, 1.6× GCC -O0's, 1.7× Clang -O0's. **Code size:
  3.6× GCC -O2's**, 2.8× Clang -O0's.
- **Compile time:** about 30 ms per small file, between Clang -O0 (12-15 ms) and GCC -O2 (23-40 ms,
  and 171 ms for `bintree`, whose recursion GCC inlines into itself).
  It is linear in the number of functions, but **quadratic in a function's size**: the register
  allocation validator takes 90% of the backend on a large function.
- **The bottlenecks, in order:** (1) every local lives in memory: `-O` promotes nothing to
  registers (an experimental, opt-in promotion pipeline now exists; see bottleneck 1);
  (2) instruction selection works one op at a time and folds nothing: 40% of fcc's executed
  instructions are overhead that Clang -O0, with the same memory traffic, doesn't have; (3) the quadratic
  allocation validator; (4) zero-initialized globals written out byte by byte into `.data`;
  (5) about 25 ms of fixed cost per file. Details and evidence are under
  [Bottlenecks](#bottlenecks).

## Environment

| | |
|---|---|
| Revision | `main` at `55c1751` plus the rename and this harness; run times and counts from bit-identical binaries built at `1ac29a2` with the same changes |
| Toolchain | the dev shell (`nix develop`), nixpkgs `4fe25e12` as pinned by `flake.lock`: rustc 1.99.0, the cross `aarch64-unknown-linux-gnu-gcc` 16.2.0, Clang/LLVM 23.1.3 (also fcc's frontend), binutils 2.46, glibc 2.44 (static), qemu-user 11.1.2 |
| Build host: compiling, counting, compile time | AMD Ryzen 9 9950X (16 cores, 32 threads), NixOS, Linux 6.18.60, x86-64. Shared with other work, so compile times are the minimum of 5 runs (load average about 1 during the published compile-time runs, 3-8 during earlier ones) |
| Native host: wall time | Apple M4 Max (16 cores, 64 GB), macOS 26 (Darwin 25.6.0). Runs in Docker Desktop 29.9.3's arm64 Linux VM (Apple's hypervisor, kernel 7.0.14-linuxkit, 16 vCPUs, 7.7 GiB): native execution, virtualized, not emulated (`CPU implementer 0x61`, Apple). Image `alpine:3.22@sha256:49340b34…` (only `/bin/sh`: the binaries are static) |
| Behavior and counts | qemu-user 11.1.2 on the build host (CPU model `max`) |

## Results

### Run time on the M4 Max (median of 7 interleaved rounds after a warmup, seconds)

| program | fcc | fcc-O | gcc-O0 | gcc-O1 | gcc-O2 | clang-O0 | clang-O2 |
|---|---:|---:|---:|---:|---:|---:|---:|
| bintree | 0.371 | 0.363 | 0.337 | 0.313 | 0.285 | 0.344 | 0.294 |
| bytecode | 0.783 | 0.765 | 0.785 | 0.299 | 0.297 | 0.813 | 0.288 |
| crc32 | 0.598 | 0.605 | 0.272 | 0.223 | 0.224 | 0.241 | 0.226 |
| fannkuch | 0.376 | 0.376 | 0.287 | 0.137 | 0.153 | 0.229 | 0.148 |
| hashtab | 0.628 | 0.579 | 0.570 | 0.308 | 0.305 | 0.539 | 0.310 |
| mandel | 1.025 | 1.032 | 0.916 | 0.365 | 0.363 | 1.034 | 0.333 |
| matmul | 3.500 | 3.478 | 3.381 | 0.486 | 0.257 | 2.026 | 0.262 |
| nbody | 0.962 | 0.960 | 0.836 | 0.289 | 0.272 | 0.827 | 0.267 |
| nqueens | 0.294 | 0.294 | 0.212 | 0.132 | 0.131 | 0.246 | 0.126 |
| quicksort | 0.759 | 0.758 | 0.552 | 0.311 | 0.292 | 0.532 | 0.295 |
| sieve | 1.241 | 1.238 | 0.421 | 0.238 | 0.185 | 0.379 | 0.148 |
| strings | 1.739 | 1.682 | 1.407 | 0.381 | 0.411 | 1.359 | 0.302 |
| **geomean vs gcc-O2** | **3.17×** | **3.13×** | **2.38×** | **1.08×** | **1.00×** | **2.23×** | **0.95×** |

Within a run, runs of a cell spread by a median of 5% (max − min over median). Seven cells had one
or two slow runs (up to 2.2× the others), which the median absorbs. They are listed in the
generated report, and are most likely macOS moving the VM's vCPU to an efficiency core. This is
the third of three independent runs, and the only one with the harness as reviewed. Against the
second (identical binaries, the earlier `benchrun`), its medians moved by 1.8% (median over the 84
cells) and at most 4.9%; the first two agreed within 3.0%. Read differences under about 5% as
noise.

`bintree` spends most of its time in glibc's `malloc` and `free`, the same for every
configuration, so its ratios are small. `bytecode`'s `switch` costs fcc no more than the -O0
compilers. `matmul` (13.5×) and `sieve` (6.7×) are tight loops over arrays, where per-iteration
overhead dominates.

### Executed instructions (program code only, small size, exact; millions)

| program | fcc | fcc-O | gcc-O0 | gcc-O1 | gcc-O2 | clang-O0 | clang-O2 |
|---|---:|---:|---:|---:|---:|---:|---:|
| bintree | 16.8 | 16.4 | 8.5 | 6.5 | 4.6 | 9.2 | 6.3 |
| bytecode | 237.4 | 236.0 | 288.4 | 86.6 | 86.6 | 158.2 | 86.6 |
| crc32 | 53.6 | 53.6 | 31.6 | 9.5 | 9.5 | 29.0 | 10.9 |
| fannkuch | 50.9 | 50.9 | 24.4 | 8.9 | 7.2 | 22.2 | 6.3 |
| hashtab | 48.1 | 47.5 | 26.4 | 7.8 | 7.9 | 26.5 | 7.2 |
| mandel | 17.4 | 17.4 | 11.5 | 5.1 | 5.2 | 15.9 | 4.8 |
| matmul | 176.1 | 176.1 | 166.3 | 33.4 | 17.0 | 113.2 | 11.9 |
| nbody | 45.3 | 45.3 | 35.6 | 11.4 | 9.9 | 31.1 | 9.2 |
| nqueens | 0.2 | 0.2 | 0.1 | 0.1 | 0.1 | 0.1 | 0.1 |
| quicksort | 82.8 | 82.8 | 46.5 | 20.5 | 16.8 | 42.2 | 17.3 |
| sieve | 214.0 | 214.0 | 110.1 | 32.5 | 19.0 | 121.2 | 8.9 |
| strings | 78.0 | 77.5 | 35.9 | 14.9 | 11.4 | 40.7 | 8.4 |
| **geomean vs gcc-O2** | **5.23×** | **5.20×** | **3.26×** | **1.22×** | **1.00×** | **3.06×** | **0.89×** |

| config | executed | memory accesses | to the stack |
|---|---:|---:|---:|
| fcc-O | 1,018M | 307M | 88% |
| gcc-O0 | 785M | 309M | 88% |
| clang-O0 | 609M | 311M | 86% |
| gcc-O1 | 237M | 67M | 41% |
| gcc-O2 | 195M | 52M | 47% |
| clang-O2 | 178M | 52M | 29% |

**Instructions are not time.** fcc's code executes 5.2× GCC -O2's instructions but takes 3.1×
its time on the M4. The extra instructions are mostly cheap there: stack loads and stores that the
core forwards from its store buffer, constant moves, extensions, and branches that a wide
out-of-order core overlaps. The time ratio on narrower AArch64 cores (smaller Cortex-A and
Neoverse cores) is likely to be different, probably larger. Only a measurement there would show it.

### Code size, compile time

`.text` of each program's object, geomean against GCC -O2: fcc 3.68×, fcc -O 3.63×, GCC -O0 1.27×,
Clang -O0 1.31×. (GCC -O2's `bintree` is 9 KB because it inlines the recursion into itself.)

Compile time to an object file, minimum of 5 runs: fcc -O takes 27-32 ms per benchmark program
(79 ms for `sieve`, see bottleneck 4). GCC -O2 takes 23-40 ms (171 ms for `bintree`), Clang -O0
12-15 ms. The geomean against GCC -O2 is 0.93× for fcc -O and 0.39× for Clang -O0. Over the 67
corpus programs: fcc 2.02 s, fcc -O 2.02 s, GCC -O0 1.23 s, GCC -O2 3.23 s, Clang -O0 0.92 s,
Clang -O2 1.94 s.

For a small file, fcc's ~30 ms divides as follows. Startup takes 17 ms (an empty file to HFIR),
7 ms of it the system include probe. Clang's parse and the lowering to HFIR take about 5 ms, FIR's
lowering, `-O`, and backend 1-2 ms, and the external assembler 6-10 ms. In the `fir` CLI on the
same modules, `fir lower` takes about 1 ms, `fir opt -O` about 1 ms, and `fir compile` 1.3-2.8 ms
(13 ms for `sieve`).

Compile-time scaling on generated C (loops, branches, `switch`es, arrays, calls), minimum of 5:

| input | C lines | fcc →HFIR | fcc -O →asm | fcc -O →.o | gcc -O0 | gcc -O2 | clang -O0 |
|---|---:|---:|---:|---:|---:|---:|---:|
| 100 functions × 10 statements | 1,401 | 0.029 | 0.042 | 0.075 | 0.120 | 0.222 | 0.041 |
| 400 × 10 | 5,601 | 0.067 | 0.112 | 0.203 | 0.424 | 0.600 | 0.125 |
| 1,600 × 10 | 22,401 | 0.221 | 0.400 | 0.743 | 1.664 | 2.206 | 0.463 |
| 1 function × 100 statements | 105 | 0.018 | 0.024 | 0.031 | 0.020 | 0.063 | 0.014 |
| 1 × 400 | 405 | 0.021 | 0.045 | 0.064 | 0.039 | 0.196 | 0.021 |
| 1 × 1,600 | 1,605 | 0.036 | 0.274 | 0.321 | 0.122 | 0.792 | 0.054 |

Many functions scale linearly. fcc is faster than GCC at either level and 1.6× Clang -O0, and
about 45% of its time is the external assembler on its 8 MB of assembly. One growing function
scales quadratically in the backend: `fir compile` takes 24 ms at 400 statements, 240 ms at
1,600, and about 3.7 s at 6,400 (bottleneck 3).

## Bottlenecks

Ranked by what each costs in the measurements above. Each is a finding, not a fix; none was
changed for this baseline.

### 1. Every local lives in memory (generated code)

fcc gives every local and parameter a stack slot at function entry and loads and stores it at
every use (`frontends/c/README.md`, "How C maps to FIR"). Its memory traffic is the -O0 compilers':
307M accesses, 88% of them to the stack, against Clang -O0's 311M (86%) and GCC -O0's 309M (88%).
In total it executes as many loads as Clang -O0 (231.0M each; per program the ratio ranges from
0.77× on `bytecode` to 1.76× on `fannkuch`). GCC -O1 makes 67M memory accesses.
That puts fcc in the -O0 class at best (GCC -O0 2.38×, Clang -O0 2.23× of GCC -O2's time), and
the step from -O0 to -O1 is the largest available: 2.2× for GCC.

`-O` cannot recover it. Its passes (`fwd`, `copyprop`, `dse`, `dce`) match only adjacent ops: a
load right after a store to the same pointer. On these programs `-O` changes executed instructions
by at most 2.3% and time by about 1%. Promoting non-escaping slots to SSA values (mem2reg, with
scalar replacement of structs) is the missing piece, and the decided headline proof of FIR-1
(decision "FIR-1 scope"). The layer audit's slice found the same
(`docs/assurance/layer-audit.md` §2).

A prototype now exists: the experimental `mem2reg` and `stackdce` passes, opt-in with
`fcc --passes mem2reg,stackdce,fwd,copyprop,dse,dce --experimental`, unproved, and never part
of `-O` ([05-optimizing-c.md](../design/05-optimizing-c.md)). On the corpus it removes 95% of
the loads and 32% of the executed instructions against `fcc -O`. This baseline measures the
default pipelines only. Adding that pipeline as a configuration of `cbench.py` would show what
it buys natively, and what of bottleneck 2 is left once memory traffic is gone. 05's own
measurement puts the remaining gap in instruction selection, as bottleneck 2 does.

### 2. Instruction selection one op at a time (generated code)

With the same total of 231.0M loads as Clang -O0, fcc -O executes 1,018M instructions against 609M, and
takes 1.41× Clang -O0's time. The difference is selection, measured per instruction form over all
12 programs (dynamic counts, program code):

| form | fcc -O | clang -O0 | where it comes from |
|---|---:|---:|---|
| constants put in a register, then used | 124.5M | 6.9M | `konst` then a register op, where an immediate encodes (`movz x9, #1; add x3, x3, x9`) |
| extensions (`sxtw`, `ubfx`, …) | 102.3M | 15.6M | integer compares extend both operands every time (`isel.rs:1921-1928`), even values a 32-bit load just extended |
| no-op `asr xN, xN, #0` (`sbfx #0, #64`) | 47.1M | 0 | `int.sext` to `i128` emitted unconditionally (`isel.rs:1936-1946`). The HFIR lowering computes `ptr.index` exactly at twice the address width (decision "HFIR lowering") |
| `mul` | 57.2M | 10.1M | the same index arithmetic multiplies by the element size: no shifts, no scaled addressing (`ldr d0, [x9, x10, lsl #3]`) |
| `cset` and `tst #1` | 53.3M | 1.4M | every comparison materializes an `i1` and `branch_bit` tests its bit 0 (`isel.rs:989`): no compare-and-branch |
| unconditional `b` | 55.4M | 55.1M | structured regions become blocks joined by jumps, including jumps to jumps. GCC -O2 executes 2.9% of its instructions as `b`, fcc 5.4% |

matmul's inner statement `c[i * n + j] += aik * b[k * n + j]` is 42 instructions per iteration
in fcc -O, with 16 memory accesses, 13 of them to stack slots. GCC -O2 vectorizes it. These are local rules, mostly listed
under decision 7's "next" items (folding offsets and shifted operands, `madd`, `ldp`/`stp`). With
them, fcc would at least reach the -O0 compilers. With bottleneck 1 fixed too, the gap that
remains is GCC -O1's.

### 3. The register allocation validator is quadratic (compile time)

`regcheck::validate` runs on every compile, by design: it is the safety net that makes an
unproved allocator trustworthy. On one function of 1,600 statements, callgrind attributes 90.3% of
`fir compile`'s instructions to it. The allocation itself (`assign`) takes 3.4%, and instruction
selection and emission a few percent. Its state is a sorted list of values per location, every
register and every spill and save slot (`regcheck.rs:92`). Every write `kill`s the value across
all locations (`regcheck.rs:151`), and each block's state is cloned and joined over all of them.
Slots grow with the function, so the cost grows with instructions × slots: 24 ms at 400
statements, 240 ms at 1,600, about 3.7 s at 6,400. An index from value to locations, or sparse
per-block states, would make it close to linear without changing what it checks. Machine-generated
C (big `switch` interpreters, unrolled tables) will hit this first.

### 4. Globals are written byte by byte, and zeros go to `.data` (compile time, binary size)

The backend writes every global's image as `.byte` lists, and a writable global always goes to
`.data` (`targets/aarch64/src/emit.rs:743-781`). There is no `.bss` and no `.zero`.
`sieve`'s `static unsigned char flags[1 << 20]` becomes 65,536 lines of `.byte 0, …` (3.5 MB of
assembly) and 1 MiB of `.data` in the object and the binary, where GCC puts it in `.bss`. It costs
13 ms in `fir compile` (against 1.3-2.8 ms for every other program) and 79 ms per compile
(against about 30 ms). Zero runs as `.zero N`, and all-zero writable globals in `.bss`, would fix
it.

### 5. About 25 ms of fixed cost per file (compile time)

Each fcc process runs the cross compiler's include probe (`cc -E -Wp,-v`, 7 ms,
`frontends/c/src/main.cpp:148`) and starts Clang (17 ms to HFIR for an empty file, against
Clang -O0's 12-15 ms for a whole small program). It then writes assembly text and runs the cross
GCC driver to assemble it (6-10 ms on small files, about 340 ms of the 743 ms for 1,600
functions). Over the corpus, fcc takes 2.02 s and Clang -O0 0.92 s. Finding the include directories when fcc is
built (as it already does for Clang's resource directory), and writing objects directly, would
remove most of it.

### Not bottlenecks

FIR's lowering and `-O` take about 1 ms each on these programs. Instruction selection,
allocation, and emission are a few percent of the backend, outside bottleneck 3. Behavior showed
no difference anywhere.

## Limits of this baseline

- **One native machine.** The run times come from one Apple M4 Max in a Linux VM, so they hold
  for that core. Under Apple's hypervisor, macOS schedules the vCPUs, and runs may land on
  efficiency cores (the isolated outliers). Other AArch64 cores will give other ratios,
  especially for fcc's stack-heavy code (see "Instructions are not time").
- **Small programs.** Twelve kernels of 20-65 lines, plus generated inputs for compile time.
  They cover the common shapes of C (loops over arrays, recursion, pointer chasing, `switch`
  dispatch, floating point, the allocator) but are not a standard suite such as SPEC.
- **What fcc can compile.** The programs avoid what fcc rejects (`volatile`, `long double`,
  external variables such as `stdout`, VLAs; see "Not supported yet"), so the comparison is over
  the subset both compile.
- **Reference flags.** The references run with `-ffp-contract=off` and without Nix's hardening, to
  compare like with like. Their defaults would be somewhat faster (FMA) and somewhat slower
  (stack protector, register zeroing).

## How it is measured

### What runs

- **Behavior.** The differential corpus `cargo test --release -p fir-capi --test fcc`
  (`frontends/c/README.md#tests`) is unchanged. On top of it, the twelve programs in
  `benchmarks/c/programs/` are small kernels written for this baseline, deterministic and free
  of undefined behavior, each printing a checksum. Every build of every program must print exactly
  what GCC -O2's build prints and exit the same way. That is checked twice: at the small size under
  qemu-user (`count`, which fails on any difference, or if the reference itself fails) and at the
  large size natively (`time`, where `benchrun` compares every timed run's output through EOF,
  extra bytes included).
- **Configurations.** `fcc`, `fcc-O` (`fcc -O`, FIR's proved passes), GCC 16.2 at
  `-O0`, `-O1`, `-O2`, and Clang 23 at `-O0`, `-O2`, all for `aarch64-unknown-linux-gnu`. The
  reference compilers get `-ffp-contract=off`, since fcc never fuses `a * b + c`. Nix's
  compiler wrapper would add hardening flags to GCC's code only (`-fstack-protector-strong`,
  `-fzero-call-used-regs=used-gpr`, ...), so the harness clears them (`NIX_HARDENING_ENABLE=`).
  Clang runs unwrapped with exactly fcc's Clang setup (target, `-nostdlibinc`, resource
  directory, and the cross GCC's system include directories), so it parses the same headers.
- **The reference GCC** is `FCC_BENCH_GCC` from the dev shell: the cross GCC off AArch64, and
  GCC itself (also 16.2) on AArch64 Linux, where the shell's `cc` is Clang. The harness refuses a
  "GCC" whose `--version` isn't GCC's.
- **Linking.** Every object is linked by the same command: that GCC driver, `-static`, against
  the target's static glibc 2.44 (`FCC_BENCH_LIBC_STATIC`, from the dev shell). The same binary
  then runs under qemu-user and on any AArch64 Linux machine, with the same libc.
- **Provenance.** Each step records the SHA-256 of every binary it measured, and `report` refuses
  a `count` or `time` result whose binaries aren't the current build's, so a stale step is never
  mixed into a report. `time` saves nothing unless every program ran under every configuration in
  every round.

### Metrics, and where each is valid

| Metric | Where | Valid as |
|---|---|---|
| Wall time of a run | native AArch64 only (`benchrun` refuses otherwise) | performance on that machine |
| Executed instructions, their mix, memory accesses by address | qemu-user with `insn_count.so` | exact architectural counts; **not** a time |
| Code size | `.text*` sections of the program's object | exact |
| Compile time | the x86-64 host, natively | performance of the compilers on that host |

**No timing is taken under emulation.** Under qemu-user an instruction's cost depends on how QEMU
translates it, not on any AArch64 core, so qemu wall times say nothing about AArch64
performance. The `time` step refuses to start on a non-AArch64 host unless given `--ssh`, and
`benchrun`, the native driver, reads `/proc/cpuinfo` and refuses qemu-user, the emulator the
dev shell provides: its CPU reports implementer `0x00`, which Arm reserves for software. That check
has a limit. A full-system emulator modelling a named CPU (`qemu-system-aarch64 -cpu cortex-a72`
under TCG) reports that CPU's implementer and would pass, and no check from inside the guest can
rule it out. So the machine is the operator's word, backed by what the results record: here
the SSH host's own CPU (`Apple M4 Max`, from `sysctl`), Docker's server architecture
(`linux/arm64`), and the VM's `CPU implementer 0x61` (Apple).

Instruction counts are exact but are not time. One executed instruction in fcc's code is
usually cheaper than one in GCC -O2's: most are stack loads and stores that hit the store buffer
and L1, plus moves and branches a wide out-of-order core overlaps. The time table and the count
table disagree for that reason (see below).

The QEMU plugin (`benchmarks/c/insn_count.c`) counts the executions of every translated block
and, for every memory access, whether its address is in the stack. qemu-user puts a program's
first `mmap`ed memory directly below the stack mapping, so the window has to stay inside that
mapping. QEMU runs with a fixed 8 MiB stack (`-s 8M`) and an empty environment, which keeps the
initial `sp` within a few KiB of the stack's top. The window is [`sp` − 7 MiB, `sp` + 64 KiB). The
harness checks under `-strace` that no mapping meets it, and that nothing touches the 512 KiB of
stack below it. (A first version used 64 MiB, which counted `hashtab`'s 2 MiB heap as stack; a
review caught it.) The harness takes the program's own code ranges from the linker map, so libc is
counted separately, disassembles them with `objdump`, and classifies each executed instruction.
Counting stack traffic by address matters: fcc addresses its slots through registers computed
once at function entry (`add x2, sp, #0` … `ldr x4, [x2]`), so classifying by `[sp`/`[x29`
operands would miss nearly all of it.

Native timing interleaves configurations. After one warmup round, each of the N rounds runs
every program under every configuration once, so drift (thermal state, other load) spreads
over all configurations instead of biasing one. The tables give the median wall time.

### Reproducing

```sh
nix develop                                   # Linux, x86-64 or AArch64
python3 benchmarks/c/cbench.py build          # fcc (CMake), every config: objects, binaries,
                                              # compile times, fcc's phases, sizes
python3 benchmarks/c/cbench.py count          # behavior + instruction counts (qemu-user off AArch64)
python3 benchmarks/c/cbench.py scaling        # compile time on generated inputs
python3 benchmarks/c/cbench.py time           # natively, on an AArch64 Linux host
python3 benchmarks/c/cbench.py time --ssh HOST                       # on an AArch64 Linux host
python3 benchmarks/c/cbench.py time --ssh MAC --docker alpine:3.22 \
    --docker-bin '/usr/local/bin/docker --context desktop-linux'      # in an arm64 Linux VM
python3 benchmarks/c/cbench.py report         # target/cbench/report.md
python3 benchmarks/c/cbench.py all [time options]
```

`--only NAME...` restricts the programs, `--reps N` the compile-time repetitions (5), `--rounds N`
the native rounds (7), and `--out DIR` the output directory (`target/cbench`). Each step writes its
JSON there. The program sizes are `SIZES` in `cbench.py`: a small count size, run under qemu, and a
large time size, run natively.

The backend profile behind bottleneck 3 is outside the harness. To reproduce it (perf is not
available on the build host, so callgrind):

```sh
python3 -c 'import sys; sys.path.insert(0, "benchmarks/c"); import cbench
for n in (400, 1600, 6400): open(f"one{n}.c", "w").write(cbench.synth(1, n))'
for n in 400 1600 6400; do
  build/fcc/fcc one$n.c --emit hfir -o one$n.hfir && target/release/fir lower one$n.hfir > one$n.mfir
  time target/release/fir compile one$n.mfir --emit asm -o /dev/null          # 24 ms, 240 ms, ~3.7 s
done
valgrind --tool=callgrind --callgrind-out-file=cg.out \
  target/release/fir compile one1600.mfir --emit asm -o /dev/null
callgrind_annotate --inclusive=yes cg.out | grep fir::     # regcheck::validate: 90.3% inclusive
```
