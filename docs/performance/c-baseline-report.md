# fcc C baseline: the generated report

Written by `frontends/c/bench/cbench.py report` from the measurements behind
[c-baseline.md](c-baseline.md) (`target/cbench/*.json`), unedited but for this note. Regenerate it
after a new run to compare. Its build ran at `753b752` with the next commit's harness not yet
committed; the counts and times come from bit-identical binaries built earlier (c-baseline.md
says how that is checked).

Revision `753b7528c031` (with uncommitted changes); host Linux 6.18.60 x86_64, AMD Ryzen 9 9950X 16-Core Processor (32 CPUs). aarch64-unknown-linux-gnu-gcc (GCC) 16.2.0; clang version 23.1.3; qemu-aarch64 version 11.1.2.

## Behavior (small size, qemu-user): output and exit code equal to gcc-O2's

| program | fcc | fcc-O | gcc-O0 | gcc-O1 | gcc-O2 | clang-O0 | clang-O2 |
|---|---:|---:|---:|---:|---:|---:|---:|
| bintree | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| bytecode | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| crc32 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| fannkuch | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| hashtab | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| mandel | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| matmul | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| nbody | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| nqueens | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| quicksort | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| sieve | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| strings | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

## Native wall time (median of 7 interleaved rounds, seconds)

Where: ssh y, docker; CPU implementer 0x61, part 0x0; Docker server 29.9.3 linux/arm64, image `alpine@sha256:49340b346798875b5592e5d420241f2f9cfba5f47e62ebb1446a1b34734e898f`.

The SSH host: Darwin y 25.6.0 Darwin Kernel Version 25.6.0: Fri Jul 31 19:17:26 PDT 2026; root:xnu-12377.161.14~5/RELEASE_ARM64_T6041 arm64; Apple M4 Max; 16; 68719476736.

The machine as Linux saw it:

```
uname: Linux 6b3151483900 7.0.14-linuxkit #1 SMP PREEMPT Fri Oct 30 13:45:20 UTC 2026 aarch64 Linux
nproc: 16
MemTotal:        8123676 kB
     16 CPU implementer	: 0x61
     16 CPU part	: 0x000
     16 CPU revision	: 0
     16 CPU variant	: 0x0
     16 Features	: fp asimd evtstrm aes pmull sha1 sha2 crc32 atomics fphp asimdhp cpuid asimdrdm jscvt fcma lrcpc dcpop sha3 asimddp sha512 asimdfhm dit uscat ilrcpc flagm sb paca pacg dcpodp flagm2 frint i8mm bf16 bti afp
```

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

Spread (max − min) / median across rounds: median 5.0%, worst 119.8%.

Cells whose runs spread by more than 15% (all runs, seconds): bytecode gcc-O2 (0.297, 0.291, 0.290, 0.301, 0.297, 0.372, 0.299); crc32 fcc (0.604, 0.595, 0.595, 0.598, 0.607, 0.698, 0.588); crc32 fcc-O (0.611, 0.597, 0.605, 0.603, 0.610, 0.685, 0.586); hashtab clang-O2 (0.310, 0.309, 0.310, 0.310, 0.325, 0.275, 0.311); matmul fcc (3.493, 3.499, 4.433, 3.549, 3.500, 3.462, 3.500); matmul gcc-O0 (3.375, 3.396, 4.687, 3.434, 3.381, 3.307, 3.344); matmul clang-O0 (2.021, 2.027, 4.319, 4.439, 2.026, 2.013, 2.014).

## Executed instructions in the program's own code (small size, millions; exact, counted under qemu)

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

## Executed instructions including libc (millions)

| program | fcc | fcc-O | gcc-O0 | gcc-O1 | gcc-O2 | clang-O0 | clang-O2 |
|---|---:|---:|---:|---:|---:|---:|---:|
| bintree | 63.2 | 62.8 | 54.9 | 52.9 | 51.1 | 55.6 | 52.8 |
| bytecode | 237.5 | 236.1 | 288.5 | 86.7 | 86.7 | 158.3 | 86.7 |
| crc32 | 53.7 | 53.7 | 31.7 | 9.6 | 9.6 | 29.1 | 11.0 |
| fannkuch | 51.0 | 51.0 | 24.5 | 9.0 | 8.4 | 22.3 | 7.5 |
| hashtab | 48.2 | 47.6 | 26.5 | 7.9 | 8.0 | 26.6 | 7.3 |
| mandel | 17.5 | 17.5 | 11.6 | 5.2 | 5.3 | 16.0 | 4.9 |
| matmul | 176.2 | 176.2 | 166.4 | 33.5 | 17.1 | 113.3 | 12.0 |
| nbody | 45.4 | 45.4 | 37.9 | 11.5 | 10.0 | 33.4 | 9.3 |
| nqueens | 0.3 | 0.3 | 0.2 | 0.2 | 0.2 | 0.2 | 0.2 |
| quicksort | 82.9 | 82.9 | 46.6 | 20.6 | 16.9 | 42.3 | 17.3 |
| sieve | 214.1 | 214.1 | 110.2 | 32.6 | 19.1 | 121.3 | 9.0 |
| strings | 78.1 | 77.6 | 36.0 | 15.0 | 12.9 | 40.8 | 9.9 |
| **geomean vs gcc-O2** | **4.48×** | **4.47×** | **2.99×** | **1.16×** | **1.00×** | **2.80×** | **0.88×** |

## Instruction mix in the program's own code (all programs, share of executed instructions)

| config | executed | load | store | move | alu | compare | branch | call | muldiv | fp | memory accesses | to the stack |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| fcc | 1021M | 22.9% | 7.4% | 12.9% | 29.1% | 9.4% | 10.6% | 0.2% | 5.7% | 1.8% | 310M | 88% |
| fcc-O | 1018M | 22.7% | 7.4% | 13.0% | 29.2% | 9.4% | 10.6% | 0.2% | 5.7% | 1.8% | 307M | 88% |
| gcc-O0 | 785M | 30.1% | 9.2% | 3.3% | 24.3% | 13.4% | 15.1% | 0.3% | 1.9% | 2.3% | 309M | 88% |
| gcc-O1 | 237M | 18.7% | 9.0% | 5.7% | 28.0% | 12.2% | 17.7% | 0.4% | 0.8% | 7.4% | 67M | 41% |
| gcc-O2 | 195M | 18.5% | 8.1% | 6.1% | 31.8% | 11.1% | 17.0% | 0.3% | 1.0% | 6.1% | 52M | 47% |
| clang-O0 | 609M | 37.9% | 13.2% | 4.7% | 23.4% | 0.3% | 15.3% | 0.4% | 1.9% | 3.0% | 311M | 86% |
| clang-O2 | 178M | 19.0% | 8.4% | 5.3% | 34.3% | 8.4% | 16.4% | 0.4% | 1.2% | 6.6% | 52M | 29% |

Memory accesses are counted by address (an `ldp` may be two); an access is to the stack if its address is in [sp - 7 MiB, sp + 64 KiB) of the initial stack pointer sp, inside QEMU's 8 MiB stack; `count` checks that no mapping meets that window.

## Code size (.text bytes of the program's object)

| program | fcc | fcc-O | gcc-O0 | gcc-O1 | gcc-O2 | clang-O0 | clang-O2 |
|---|---:|---:|---:|---:|---:|---:|---:|
| bintree | 1712 | 1676 | 544 | 416 | 9052 | 608 | 432 |
| bytecode | 3968 | 3924 | 1184 | 564 | 568 | 780 | 432 |
| crc32 | 1804 | 1780 | 564 | 264 | 292 | 632 | 288 |
| fannkuch | 2408 | 2384 | 784 | 432 | 484 | 808 | 624 |
| hashtab | 2268 | 2224 | 844 | 468 | 452 | 904 | 416 |
| mandel | 1476 | 1452 | 396 | 276 | 308 | 504 | 248 |
| matmul | 2264 | 2240 | 972 | 588 | 608 | 968 | 548 |
| nbody | 2920 | 2896 | 1572 | 644 | 676 | 1428 | 960 |
| nqueens | 1368 | 1344 | 368 | 288 | 260 | 412 | 272 |
| quicksort | 3280 | 3256 | 1504 | 988 | 892 | 1448 | 904 |
| sieve | 1648 | 1624 | 468 | 248 | 316 | 524 | 572 |
| strings | 3244 | 3208 | 1152 | 744 | 836 | 1404 | 672 |
| **geomean vs gcc-O2** | **3.68×** | **3.63×** | **1.27×** | **0.74×** | **1.00×** | **1.31×** | **0.80×** |

## Compile time to an object file (host, minimum of 5 runs, ms)

| program | fcc | fcc-O | gcc-O0 | gcc-O1 | gcc-O2 | clang-O0 | clang-O2 |
|---|---:|---:|---:|---:|---:|---:|---:|
| bintree | 27 | 28 | 18 | 23 | 171 | 12 | 20 |
| bytecode | 29 | 28 | 19 | 22 | 27 | 13 | 21 |
| crc32 | 32 | 31 | 18 | 22 | 24 | 13 | 20 |
| fannkuch | 28 | 29 | 17 | 24 | 28 | 14 | 23 |
| hashtab | 27 | 29 | 18 | 24 | 29 | 14 | 21 |
| mandel | 27 | 27 | 16 | 21 | 23 | 14 | 17 |
| matmul | 28 | 29 | 20 | 24 | 31 | 12 | 25 |
| nbody | 29 | 29 | 20 | 27 | 37 | 15 | 31 |
| nqueens | 28 | 27 | 17 | 19 | 23 | 13 | 17 |
| quicksort | 29 | 29 | 19 | 32 | 38 | 12 | 29 |
| sieve | 79 | 79 | 17 | 23 | 25 | 13 | 24 |
| strings | 30 | 32 | 20 | 28 | 40 | 14 | 25 |
| **geomean vs gcc-O2** | **0.92×** | **0.93×** | **0.54×** | **0.71×** | **1.00×** | **0.39×** | **0.66×** |

The 67 programs of `frontends/c/tests`, one compile each, total seconds: fcc 2.02, fcc-O 2.02, gcc-O0 1.23, gcc-O1 2.17, gcc-O2 3.23, clang-O0 0.92, clang-O2 1.94.

### Where fcc's time goes (ms, minimum of the runs; each stage includes the ones before)

Startup (an empty file to HFIR): 17 ms, of which the system include probe (`cc -E -Wp,-v`) is 7 ms.

| program | →HFIR | →MFIR -O | →asm -O | →.o -O | fir lower | fir opt -O | fir compile | HFIR lines |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| bintree | 20 | 20 | 21 | 29 | 1.0 | 1.0 | 1.4 | 319 |
| bytecode | 21 | 22 | 22 | 27 | 1.2 | 1.2 | 1.9 | 663 |
| crc32 | 21 | 21 | 22 | 32 | 1.0 | 1.1 | 2.4 | 350 |
| fannkuch | 21 | 22 | 21 | 27 | 1.1 | 1.0 | 1.9 | 430 |
| hashtab | 21 | 20 | 21 | 27 | 1.1 | 1.1 | 1.8 | 424 |
| mandel | 22 | 20 | 20 | 27 | 1.0 | 1.0 | 1.6 | 290 |
| matmul | 20 | 21 | 21 | 29 | 1.0 | 1.1 | 1.8 | 453 |
| nbody | 22 | 20 | 23 | 28 | 1.2 | 1.2 | 1.8 | 571 |
| nqueens | 20 | 20 | 20 | 27 | 1.0 | 0.9 | 1.3 | 251 |
| quicksort | 20 | 21 | 22 | 29 | 1.3 | 1.1 | 2.3 | 623 |
| sieve | 21 | 20 | 33 | 79 | 0.9 | 1.0 | 12.7 | 321 |
| strings | 20 | 20 | 24 | 30 | 1.2 | 1.1 | 2.8 | 600 |

The `fir` columns are the same module through the `fir` CLI, each step a separate process.

## Compile-time scaling (seconds, minimum of the runs)

**many functions**

| funcs | stmts each | C lines | HFIR lines | fcc →HFIR | fcc →asm | fcc -O →asm | fcc -O →.o | gcc -O0 | gcc -O2 | clang -O0 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 25 | 10 | 351 | 5387 | 0.020 | 0.026 | 0.028 | 0.040 | 0.040 | 0.124 | 0.018 |
| 100 | 10 | 1401 | 21592 | 0.029 | 0.040 | 0.042 | 0.075 | 0.120 | 0.222 | 0.041 |
| 400 | 10 | 5601 | 86292 | 0.067 | 0.103 | 0.112 | 0.203 | 0.424 | 0.600 | 0.125 |
| 1600 | 10 | 22401 | 345092 | 0.221 | 0.364 | 0.400 | 0.743 | 1.664 | 2.206 | 0.463 |

**one function**

| funcs | stmts each | C lines | HFIR lines | fcc →HFIR | fcc →asm | fcc -O →asm | fcc -O →.o | gcc -O0 | gcc -O2 | clang -O0 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 25 | 30 | 517 | 0.017 | 0.018 | 0.019 | 0.025 | 0.014 | 0.027 | 0.010 |
| 1 | 100 | 105 | 1906 | 0.018 | 0.023 | 0.024 | 0.031 | 0.020 | 0.063 | 0.014 |
| 1 | 400 | 405 | 7556 | 0.021 | 0.044 | 0.045 | 0.064 | 0.039 | 0.196 | 0.021 |
| 1 | 1600 | 1605 | 30156 | 0.036 | 0.272 | 0.274 | 0.321 | 0.122 | 0.792 | 0.054 |
