# fai against GCC, Clang, and arocc: the generated tables

The three harnesses' reports as generated at `972e7dc` (with this change's harness edits), for
[compilers.md](compilers.md). "dirty" in their headers is those edits: no compiler source changed.
compilebench's per-workload tables (quartiles, ranges, first runs, phases) are left out; its
full report has the same form as [compile-speed-report.md](compile-speed-report.md).

## projbench: Lua, SQLite, frontends, C23

fai `972e7dc676` (dirty); aarch64-unknown-linux-gnu-gcc (GCC) 16.2.0; clang version 23.1.3; host AMD Ryzen 9 9950X 16-Core Processor, load ['1.20', '0.94', '0.58'] to ['1.18', '0.94', '0.58']

### Build: Lua 5.4.7, 33 files (serial, minimum of 5)

| config | wall ms | CPU ms | peak RSS MiB | .text bytes |
|---|---:|---:|---:|---:|
| fcc | 1,433 | 1,333 | 142 | 573,108 |
| fcc-O | 1,457 | 1,357 | 142 | 569,252 |
| gcc-O0 | 1,303 | 1,204 | 67 | 260,072 |
| gcc-O2 | 3,968 | 3,850 | 87 | 181,884 |
| clang-O0 | 792 | 755 | 111 | 273,604 |
| clang-O2 | 2,228 | 2,180 | 130 | 199,936 |

### Build: SQLite: sqlite3.c + speedtest1.c (serial, minimum of 5)

| config | wall ms | CPU ms | peak RSS MiB | .text bytes |
|---|---:|---:|---:|---:|
| fcc | 1,346 | 1,687 | 257 | 2,137,416 |
| fcc-O | 1,438 | 1,785 | 254 | 2,120,536 |
| gcc-O0 | 2,248 | 2,101 | 317 | 1,029,764 |
| gcc-O2 | 15,791 | 15,524 | 360 | 855,000 |
| clang-O0 | 772 | 761 | 187 | 1,042,620 |
| clang-O2 | 8,635 | 8,529 | 384 | 972,048 |

| config | sqlite3 | speedtest1 |
|---|---:|---:|
| fcc | 1,261 | 85.1 |
| fcc-O | 1,352 | 85.2 |
| gcc-O0 | 2,165 | 83.4 |
| gcc-O2 | 15,383 | 408 |
| clang-O0 | 735 | 36.3 |
| clang-O2 | 8,459 | 176 |

### fcc phases (self ms, summed over files; * = summed over threads)

| build | largest phases |
|---|---:|
| lua/fcc | total (main thread) 1,218, aarch64.regalloc 383, aarch64.regcheck * 325, fcc: clang (preprocess, parse, sema) 306, fcc: assemble, link (cc) 277, fcc: write assembly 143, aarch64.regalloc.assign * 94, fcc: lower AST to HFIR 41 |
| lua/fcc-O | total (main thread) 1,225, aarch64.regalloc 371, aarch64.regcheck * 316, fcc: clang (preprocess, parse, sema) 309, fcc: assemble, link (cc) 276, fcc: write assembly 143, aarch64.regalloc.assign * 91, fcc: lower AST to HFIR 40 |
| sqlite/fcc | total (main thread) 1,331, aarch64.regcheck * 525, fcc: assemble, link (cc) 422, fcc: clang (preprocess, parse, sema) 247, fcc: write assembly 235, aarch64.regalloc.assign * 132, verify 107, fcc: lower AST to HFIR 107 |
| sqlite/fcc-O | total (main thread) 1,410, aarch64.regcheck * 486, fcc: assemble, link (cc) 411, fcc: clang (preprocess, parse, sema) 244, fcc: write assembly 221, verify 133, aarch64.regalloc.assign * 126, fcc: lower AST to HFIR 107 |

### Binaries (static)

| binary | bytes | .text |
|---|---:|---:|
| lua.clang-O0 | 1,372,896 | 832,712 |
| lua.clang-O2 | 1,291,944 | 758,920 |
| lua.fcc | 1,680,408 | 1,131,912 |
| lua.fcc-O | 1,680,472 | 1,128,072 |
| lua.gcc-O0 | 1,372,080 | 819,848 |
| lua.gcc-O2 | 1,226,920 | 741,320 |
| speedtest1.clang-O0 | 2,229,544 | 1,534,184 |
| speedtest1.clang-O2 | 2,052,584 | 1,465,448 |
| speedtest1.fcc | 3,341,704 | 2,629,032 |
| speedtest1.fcc-O | 3,341,704 | 2,612,136 |
| speedtest1.gcc-O0 | 2,162,720 | 1,522,600 |
| speedtest1.gcc-O2 | 1,986,360 | 1,347,816 |

### Frontends: parse and check only (wall ms, minimum, summed over files)

| inputs | files | gcc -fsyntax-only | clang -fsyntax-only | arocc -fsyntax-only | fcc: Clang phase | fcc: AST to HFIR |
|---|---:|---:|---:|---:|---:|---:|
| generated | 2 | 111 | 135 | 82.3 | 128 | 140 |
| lua | 33 | 593 | 503 | 337 | 293 | 39.4 |
| programs | 12 | 175 | 135 | 45.8 | 60.4 | 2.6 |
| sqlite | 2 | 218 | 243 | 206 | 243 | 108 |

Per file: wall ms / peak RSS MiB

| file | lines | gcc | clang | arocc |
|---|---:|---:|---:|---:|
| generated/gen-1600x10 | 22,401 | 77.3 / 60 | 95.4 / 92 | 61.7 / 32 |
| generated/gen-1x6400 | 6,405 | 33.9 / 40 | 39.2 / 83 | 20.6 / 31 |
| lua/lapi | 1,463 | 20.0 / 33 | 17.0 / 84 | 18.0 / 31 |
| lua/lauxlib | 1,126 | 19.1 / 31 | 14.8 / 84 | 7.5 / 31 |
| lua/lbaselib | 549 | 15.7 / 31 | 13.9 / 83 | 5.8 / 31 |
| lua/lcode | 1,874 | 23.3 / 36 | 22.6 / 86 | 22.6 / 31 |
| lua/lcorolib | 210 | 15.3 / 31 | 12.6 / 83 | 4.7 / 31 |
| lua/lctype | 64 | 12.3 / 31 | 9.5 / 80 | 2.6 / 31 |
| lua/ldblib | 483 | 15.9 / 31 | 13.0 / 83 | 5.4 / 31 |
| lua/ldebug | 962 | 18.3 / 32 | 15.2 / 84 | 10.7 / 31 |
| lua/ldo | 1,028 | 19.3 / 32 | 16.9 / 84 | 11.4 / 31 |
| lua/ldump | 230 | 15.7 / 31 | 12.0 / 82 | 4.4 / 31 |
| lua/lfunc | 294 | 16.2 / 31 | 13.4 / 82 | 5.8 / 31 |
| lua/lgc | 1,743 | 20.2 / 33 | 16.5 / 84 | 13.6 / 31 |
| lua/linit | 65 | 15.1 / 31 | 13.1 / 82 | 3.2 / 31 |
| lua/liolib | 841 | 17.0 / 31 | 14.9 / 83 | 6.4 / 31 |
| lua/llex | 581 | 17.3 / 31 | 13.5 / 83 | 6.7 / 31 |
| lua/lmathlib | 781 | 20.5 / 34 | 16.2 / 84 | 15.5 / 31 |
| lua/lmem | 215 | 15.1 / 31 | 14.2 / 82 | 4.4 / 31 |
| lua/loadlib | 758 | 16.9 / 31 | 14.7 / 83 | 5.5 / 31 |
| lua/lobject | 602 | 23.4 / 35 | 19.4 / 86 | 18.0 / 31 |
| lua/lopcodes | 104 | 12.8 / 31 | 10.8 / 80 | 3.2 / 31 |
| lua/loslib | 430 | 17.1 / 31 | 14.0 / 83 | 6.7 / 31 |
| lua/lparser | 1,967 | 18.2 / 32 | 16.7 / 84 | 8.9 / 31 |
| lua/lstate | 445 | 17.1 / 31 | 14.1 / 83 | 6.4 / 31 |
| lua/lstring | 274 | 15.7 / 31 | 13.1 / 83 | 5.3 / 31 |
| lua/lstrlib | 1,874 | 23.7 / 35 | 21.3 / 85 | 17.1 / 31 |
| lua/ltable | 995 | 21.2 / 35 | 18.4 / 85 | 18.5 / 31 |
| lua/ltablib | 430 | 14.8 / 31 | 12.4 / 83 | 4.7 / 31 |
| lua/ltm | 271 | 16.1 / 31 | 14.3 / 83 | 7.2 / 31 |
| lua/lua | 688 | 18.4 / 31 | 14.9 / 84 | 7.3 / 31 |
| lua/lundump | 335 | 15.9 / 31 | 13.2 / 83 | 5.9 / 31 |
| lua/lutf8lib | 291 | 16.1 / 31 | 14.0 / 82 | 5.6 / 31 |
| lua/lvm | 1,899 | 34.6 / 42 | 31.4 / 88 | 63.7 / 31 |
| lua/lzio | 68 | 15.2 / 31 | 11.7 / 82 | 4.3 / 31 |
| programs/bintree | 47 | 14.5 / 31 | 11.1 / 82 | 3.8 / 31 |
| programs/bytecode | 49 | 14.5 / 31 | 11.6 / 82 | 3.7 / 31 |
| programs/crc32 | 37 | 14.4 / 31 | 10.8 / 82 | 3.8 / 31 |
| programs/fannkuch | 47 | 14.3 / 31 | 10.4 / 82 | 3.7 / 31 |
| programs/hashtab | 58 | 14.9 / 31 | 10.7 / 82 | 3.9 / 31 |
| programs/mandel | 25 | 14.2 / 31 | 11.5 / 82 | 3.8 / 31 |
| programs/matmul | 44 | 14.3 / 31 | 11.7 / 82 | 3.9 / 31 |
| programs/nbody | 62 | 14.9 / 31 | 11.3 / 82 | 3.9 / 31 |
| programs/nqueens | 22 | 14.0 / 31 | 11.1 / 82 | 3.9 / 31 |
| programs/quicksort | 69 | 15.3 / 31 | 12.3 / 82 | 3.8 / 31 |
| programs/sieve | 29 | 14.9 / 31 | 10.8 / 82 | 3.8 / 31 |
| programs/strings | 67 | 14.8 / 31 | 12.1 / 82 | 3.8 / 31 |
| sqlite/speedtest1 | 3,487 | 21.8 / 34 | 21.1 / 85 | 11.4 / 31 |
| sqlite/sqlite3 | 269,613 | 196 / 100 | 222 / 121 | 195 / 76 |

### Behavior (qemu)

| config | Lua suite | Lua scripts = GCC -O2 | speedtest1 hash = GCC -O2 |
|---|---:|---:|---:|
| fcc | 28 of 28 | 7 | True |
| fcc-O | 28 of 28 | 7 | True |
| gcc-O0 | 28 of 28 | 7 | True |
| gcc-O2 | 28 of 28 | 7 | True |
| clang-O0 | 28 of 28 | 7 | True |
| clang-O2 | 28 of 28 | 7 | True |

### C23 programs

| program | GCC | Clang | fcc | arocc |
|---|---:|---:|---:|---:|
| c23_attributes | runs | same | same | accepts |
| c23_auto | runs | same | same | accepts |
| c23_bitint | runs | same | same | accepts |
| c23_bitint_builtins | runs | same | same | rejects: c23_bitint_builtins.c:21:24: error: passing 'void' to parameter of incompatible type 'long' |
| c23_bitint_wide | runs | same | same | accepts |
| c23_bool_keywords | runs | same | same | accepts |
| c23_ckdint | runs | same | same | accepts |
| c23_constexpr | runs | same | same | rejects: c23_constexpr.c:24:8: error: case value must be an integer constant expression |
| c23_constexpr_aggregates | runs | same | same | accepts |
| c23_embed | runs | same | same | accepts |
| c23_empty_init | runs | same | same | accepts |
| c23_enum_fixed | runs | same | same | rejects: c23_enum_fixed.c:21:45: error: expected a type |
| c23_generic_qualifiers | runs | same | same | rejects: c23_generic_qualifiers.c:22:45: error: type 'const int' in generic association compatible with previously specified type |
| c23_keywords | runs | same | same | rejects: c23_keywords.c:23:24: error: use of undeclared identifier '__LLONG_WIDTH__' |
| c23_labels | runs | same | same | accepts |
| c23_libc | runs | same | same | accepts |
| c23_literals | runs | same | same | accepts |
| c23_nullptr | runs | same | same | rejects: c23_nullptr.c:21:12: error: initializing 'bool' from incompatible type 'nullptr_t' |
| c23_preprocessor | runs | same | same | rejects: c23_preprocessor.c:34:44: error: expected expression |
| c23_prototypes | runs | same | same | accepts |
| c23_static_assert | runs | same | same | accepts |
| c23_stdbit | runs | same | same | rejects: c23_stdbit.c:12:28: error: passing 'void' to parameter of incompatible type 'long' |
| c23_tag_compat | runs | same | same | rejects: c23_tag_compat.c:8:8: error: redefinition of 'point' |
| c23_typeof | runs | same | same | rejects: c23_typeof.c:29:34: error: expected expression |
| c23_unnamed_params | runs | same | same | accepts |
| c23_unreachable | runs | same | same | accepts |
| c23_variadic_noname | runs | same | same | accepts |
| errors/c23_compound_storage | accepts | rejected | rejected | accepts |
| errors/c23_float_types | accepts | rejected | rejected | accepts |

### Native run time, seconds (median of 11; ssh y, docker)

| program | fcc | fcc-O | gcc-O0 | gcc-O2 | clang-O0 | clang-O2 |
|---|---:|---:|---:|---:|---:|---:|
| lua-fannkuch | 7.420 (5.94×) | 6.825 (5.46×) | 5.380 (4.30×) | 1.250 (1.00×) | 6.761 (5.41×) | 1.153 (0.92×) |
| lua-fib | 1.487 (7.09×) | 1.451 (6.92×) | 0.937 (4.47×) | 0.210 (1.00×) | 1.189 (5.67×) | 0.223 (1.06×) |
| lua-nbody | 2.776 (6.04×) | 2.539 (5.53×) | 1.833 (3.99×) | 0.459 (1.00×) | 2.176 (4.74×) | 0.411 (0.89×) |
| lua-sort | 1.455 (8.05×) | 1.398 (7.74×) | 0.576 (3.19×) | 0.181 (1.00×) | 0.641 (3.55×) | 0.180 (1.00×) |
| lua-spectral | 0.879 (8.55×) | 0.826 (8.04×) | 0.661 (6.42×) | 0.103 (1.00×) | 0.779 (7.57×) | 0.120 (1.17×) |
| lua-strings | 0.661 (3.02×) | 0.625 (2.85×) | 0.458 (2.09×) | 0.219 (1.00×) | 0.454 (2.07×) | 0.222 (1.01×) |
| lua-trees | 1.844 (4.01×) | 1.774 (3.86×) | 1.155 (2.51×) | 0.460 (1.00×) | 1.381 (3.00×) | 0.468 (1.02×) |
| speedtest1 | 3.375 (4.12×) | 3.185 (3.89×) | 3.012 (3.68×) | 0.818 (1.00×) | 2.148 (2.62×) | 0.821 (1.00×) |
| **geomean vs gcc-O2** | **5.53×** | **5.23×** | **3.63×** | **1.00×** | **3.99×** | **1.01×** |

### Executed instructions in the project's own code (qemu, exact, millions)

| workload | fcc | fcc-O | gcc-O0 | gcc-O2 | clang-O0 | clang-O2 |
|---|---:|---:|---:|---:|---:|---:|
| lua-fannkuch | 156.0 (6.31×) | 154.0 (6.23×) | 68.1 (2.75×) | 24.7 (1.00×) | 66.9 (2.71×) | 25.9 (1.05×) |
| lua-fib | 26.1 (6.53×) | 25.9 (6.49×) | 11.7 (2.92×) | 4.0 (1.00×) | 11.7 (2.94×) | 4.5 (1.14×) |
| lua-nbody | 328.4 (5.70×) | 332.1 (5.76×) | 145.3 (2.52×) | 57.6 (1.00×) | 142.3 (2.47×) | 58.6 (1.02×) |
| lua-sort | 234.8 (6.79×) | 233.3 (6.75×) | 81.6 (2.36×) | 34.6 (1.00×) | 83.2 (2.41×) | 35.9 (1.04×) |
| lua-spectral | 207.6 (6.85×) | 204.9 (6.76×) | 89.5 (2.95×) | 30.3 (1.00×) | 88.5 (2.92×) | 33.0 (1.09×) |
| lua-strings | 57.7 (4.38×) | 57.1 (4.34×) | 28.6 (2.17×) | 13.2 (1.00×) | 28.6 (2.17×) | 14.2 (1.08×) |
| lua-trees | 126.4 (5.76×) | 124.9 (5.69×) | 58.9 (2.68×) | 21.9 (1.00×) | 57.3 (2.61×) | 22.5 (1.03×) |
| speedtest1 | 5,293.5 (5.07×) | 5,242.4 (5.02×) | 4,506.7 (4.32×) | 1,044.2 (1.00×) | 2,374.9 (2.27×) | 1,072.0 (1.03×) |
| **geomean vs gcc-O2** | **5.86×** | **5.82×** | **2.78×** | **1.00×** | **2.55×** | **1.06×** |

Executed in libc (millions):

| workload | fcc | fcc-O | gcc-O0 | gcc-O2 | clang-O0 | clang-O2 |
|---|---:|---:|---:|---:|---:|---:|
| lua-fannkuch | 0.3 | 0.3 | 0.4 | 0.3 | 0.4 | 0.3 |
| lua-fib | 0.3 | 0.3 | 0.3 | 0.3 | 0.3 | 0.3 |
| lua-nbody | 0.6 | 0.6 | 0.7 | 0.4 | 0.7 | 0.4 |
| lua-sort | 0.3 | 0.3 | 0.4 | 0.3 | 0.4 | 0.3 |
| lua-spectral | 0.3 | 0.3 | 0.4 | 0.3 | 0.4 | 0.3 |
| lua-strings | 10.0 | 10.0 | 10.1 | 9.5 | 10.1 | 9.4 |
| lua-trees | 15.8 | 15.8 | 15.9 | 15.9 | 15.9 | 15.9 |
| speedtest1 | 100.7 | 100.7 | 94.6 | 89.4 | 91.7 | 90.0 |

Instruction mix in the own code, all workloads:

| config | executed | load | store | move | alu | compare | branch | call | muldiv | fp | memory accesses | to the stack |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| fcc | 6,431M | 24.4% | 9.8% | 16.1% | 27.7% | 10.1% | 8.4% | 0.8% | 2.7% | 0.0% | 2,198M | 84% |
| fcc-O | 6,375M | 23.6% | 9.9% | 16.2% | 28.0% | 10.2% | 8.5% | 0.8% | 2.7% | 0.0% | 2,137M | 84% |
| gcc-O0 | 4,990M | 22.6% | 8.3% | 3.9% | 10.4% | 26.0% | 27.8% | 0.9% | 0.1% | 0.0% | 1,542M | 78% |
| gcc-O2 | 1,231M | 25.4% | 10.2% | 12.2% | 20.5% | 9.4% | 19.3% | 1.7% | 1.0% | 0.1% | 439M | 32% |
| clang-O0 | 2,853M | 39.9% | 16.1% | 3.7% | 19.3% | 0.6% | 17.9% | 1.6% | 0.9% | 0.1% | 1,596M | 78% |
| clang-O2 | 1,267M | 25.7% | 10.3% | 10.7% | 21.5% | 9.3% | 19.6% | 1.6% | 1.2% | 0.1% | 460M | 34% |

Peak RSS while running, MiB:

| program | fcc | fcc-O | gcc-O0 | gcc-O2 | clang-O0 | clang-O2 |
|---|---:|---:|---:|---:|---:|---:|
| lua-fannkuch | 1.3 | 1.3 | 1.0 | 0.9 | 1.0 | 1.0 |
| lua-fib | 2.3 | 1.3 | 3.1 | 2.9 | 3.0 | 1.0 |
| lua-nbody | 3.4 | 1.3 | 1.0 | 3.0 | 1.1 | 1.0 |
| lua-sort | 12.5 | 11.9 | 12.2 | 11.5 | 11.5 | 12.0 |
| lua-spectral | 1.3 | 1.3 | 1.0 | 0.9 | 1.1 | 1.0 |
| lua-strings | 71.5 | 71.3 | 71.3 | 71.2 | 71.2 | 71.3 |
| lua-trees | 8.7 | 8.9 | 7.9 | 7.9 | 8.1 | 7.6 |
| speedtest1 | 87.8 | 87.6 | 86.2 | 86.2 | 86.8 | 86.7 |

Spread of the runs, (max − min) / median:

| program | fcc | fcc-O | gcc-O0 | gcc-O2 | clang-O0 | clang-O2 |
|---|---:|---:|---:|---:|---:|---:|
| lua-fannkuch | 27.7% | 20.2% | 2.8% | 2.7% | 1.8% | 4.6% |
| lua-fib | 16.8% | 16.4% | 3.1% | 38.8% | 1.1% | 2.2% |
| lua-nbody | 6.6% | 6.1% | 4.0% | 6.8% | 4.6% | 13.0% |
| lua-sort | 3.3% | 10.1% | 6.3% | 6.9% | 1.8% | 5.1% |
| lua-spectral | 19.5% | 23.8% | 7.9% | 38.2% | 2.2% | 48.7% |
| lua-strings | 3.4% | 3.8% | 5.7% | 8.0% | 4.2% | 6.3% |
| lua-trees | 4.9% | 1.4% | 1.7% | 4.7% | 2.4% | 22.0% |
| speedtest1 | 1.8% | 0.8% | 1.1% | 7.7% | 1.7% | 1.4% |

## cbench: the 12 kernels

Revision `972e7dc676e3` (with uncommitted changes); host Linux 6.18.60 x86_64, AMD Ryzen 9 9950X 16-Core Processor (32 CPUs). aarch64-unknown-linux-gnu-gcc (GCC) 16.2.0; clang version 23.1.3; qemu-aarch64 version 11.1.2.

### Behavior (small size, qemu-user): output and exit code equal to gcc-O2's

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

### Native wall time (median of 7 interleaved rounds, seconds)

Where: ssh y, docker; CPU implementer 0x61, part 0x0; Docker server 29.9.3 linux/arm64, image `alpine@sha256:49340b346798875b5592e5d420241f2f9cfba5f47e62ebb1446a1b34734e898f`.

The SSH host: Darwin y 25.6.0 Darwin Kernel Version 25.6.0: Fri Jul 31 19:17:26 PDT 2026; root:xnu-12377.161.14~5/RELEASE_ARM64_T6041 arm64; Apple M4 Max; 16; 68719476736.

The machine as Linux saw it:

```
uname: Linux 5393f0c0b126 7.0.14-linuxkit #1 SMP PREEMPT Fri Oct 30 13:45:20 UTC 2026 aarch64 Linux
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
| bintree | 0.360 | 0.360 | 0.319 | 0.298 | 0.280 | 0.330 | 0.283 |
| bytecode | 0.751 | 0.729 | 0.751 | 0.285 | 0.281 | 0.766 | 0.276 |
| crc32 | 0.579 | 0.582 | 0.254 | 0.222 | 0.221 | 0.230 | 0.221 |
| fannkuch | 0.366 | 0.365 | 0.271 | 0.132 | 0.144 | 0.217 | 0.137 |
| hashtab | 0.606 | 0.562 | 0.537 | 0.289 | 0.291 | 0.509 | 0.292 |
| mandel | 0.977 | 0.981 | 0.905 | 0.358 | 0.359 | 0.993 | 0.326 |
| matmul | 3.381 | 3.380 | 3.238 | 0.470 | 0.249 | 1.971 | 0.255 |
| nbody | 0.925 | 0.918 | 0.806 | 0.277 | 0.261 | 0.796 | 0.253 |
| nqueens | 0.279 | 0.279 | 0.199 | 0.123 | 0.124 | 0.234 | 0.119 |
| quicksort | 0.727 | 0.725 | 0.524 | 0.301 | 0.276 | 0.500 | 0.281 |
| sieve | 1.181 | 1.175 | 0.405 | 0.230 | 0.182 | 0.365 | 0.144 |
| strings | 1.685 | 1.627 | 1.348 | 0.352 | 0.382 | 1.310 | 0.281 |
| **geomean vs gcc-O2** | **3.18×** | **3.14×** | **2.36×** | **1.08×** | **1.00×** | **2.21×** | **0.94×** |

Spread (max − min) / median across rounds: median 3.6%, worst 28.9%.

Cells whose runs spread by more than 15% (all runs, seconds): matmul fcc-O (3.287, 3.345, 3.380, 3.393, 4.263, 3.378, 3.416); strings gcc-O1 (0.338, 0.366, 0.351, 0.365, 0.349, 0.397, 0.352).

### Executed instructions in the program's own code (small size, millions; exact, counted under qemu)

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

### Executed instructions including libc (millions)

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

### Instruction mix in the program's own code (all programs, share of executed instructions)

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

### Code size (.text bytes of the program's object)

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

### Compile time to an object file (host, minimum of 5 runs, ms)

| program | fcc | fcc-O | gcc-O0 | gcc-O1 | gcc-O2 | clang-O0 | clang-O2 |
|---|---:|---:|---:|---:|---:|---:|---:|
| bintree | 19 | 18 | 18 | 23 | 171 | 13 | 19 |
| bytecode | 19 | 19 | 18 | 23 | 26 | 13 | 20 |
| crc32 | 21 | 21 | 17 | 23 | 25 | 13 | 21 |
| fannkuch | 18 | 18 | 19 | 24 | 27 | 13 | 24 |
| hashtab | 18 | 19 | 20 | 25 | 27 | 13 | 23 |
| mandel | 17 | 18 | 17 | 21 | 23 | 13 | 17 |
| matmul | 18 | 19 | 18 | 27 | 33 | 15 | 22 |
| nbody | 18 | 20 | 20 | 26 | 36 | 15 | 28 |
| nqueens | 18 | 18 | 16 | 21 | 21 | 12 | 19 |
| quicksort | 19 | 19 | 20 | 31 | 38 | 13 | 29 |
| sieve | 69 | 71 | 18 | 20 | 26 | 15 | 24 |
| strings | 19 | 19 | 20 | 29 | 38 | 13 | 28 |
| **geomean vs gcc-O2** | **0.63×** | **0.64×** | **0.55×** | **0.73×** | **1.00×** | **0.41×** | **0.68×** |

The 103 programs of `frontends/c/tests`, one compile each, total seconds: fcc 1.92, fcc-O 1.95, gcc-O0 1.78, gcc-O1 2.77, gcc-O2 3.97, clang-O0 1.24, clang-O2 2.56.

#### Where fcc's time goes (ms, minimum of the runs; each stage includes the ones before)

Startup (an empty file to HFIR): 6 ms, of which the system include probe (`cc -E -Wp,-v`) is 7 ms.

| program | →HFIR | →MFIR -O | →asm -O | →.o -O | fir lower | fir opt -O | fir compile | HFIR lines |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| bintree | 12 | 11 | 11 | 18 | 1.1 | 1.0 | 1.4 | 319 |
| bytecode | 11 | 11 | 11 | 18 | 1.3 | 1.3 | 1.7 | 663 |
| crc32 | 10 | 11 | 12 | 22 | 1.0 | 1.0 | 2.2 | 350 |
| fannkuch | 11 | 11 | 11 | 19 | 1.0 | 1.1 | 1.4 | 430 |
| hashtab | 10 | 10 | 11 | 18 | 1.1 | 1.1 | 1.5 | 424 |
| mandel | 11 | 10 | 11 | 18 | 1.0 | 0.9 | 1.3 | 290 |
| matmul | 10 | 10 | 11 | 18 | 1.1 | 1.1 | 1.5 | 453 |
| nbody | 11 | 11 | 12 | 21 | 1.3 | 1.3 | 1.7 | 571 |
| nqueens | 10 | 10 | 11 | 18 | 0.9 | 0.9 | 1.2 | 251 |
| quicksort | 10 | 11 | 12 | 18 | 1.1 | 1.0 | 1.8 | 623 |
| sieve | 11 | 11 | 25 | 70 | 1.0 | 0.9 | 12.8 | 321 |
| strings | 10 | 10 | 12 | 19 | 1.1 | 1.2 | 2.0 | 600 |

The `fir` columns are the same module through the `fir` CLI, each step a separate process.

### Compile-time scaling (seconds, minimum of the runs)

**many functions**

| funcs | stmts each | C lines | HFIR lines | fcc →HFIR | fcc →asm | fcc -O →asm | fcc -O →.o | gcc -O0 | gcc -O2 | clang -O0 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 25 | 10 | 351 | 5387 | 0.010 | 0.015 | 0.017 | 0.029 | 0.039 | 0.121 | 0.018 |
| 100 | 10 | 1401 | 21592 | 0.021 | 0.031 | 0.033 | 0.065 | 0.119 | 0.221 | 0.040 |
| 400 | 10 | 5601 | 86292 | 0.061 | 0.093 | 0.102 | 0.195 | 0.422 | 0.599 | 0.127 |
| 1600 | 10 | 22401 | 345092 | 0.222 | 0.353 | 0.394 | 0.738 | 1.652 | 2.198 | 0.464 |

**one function**

| funcs | stmts each | C lines | HFIR lines | fcc →HFIR | fcc →asm | fcc -O →asm | fcc -O →.o | gcc -O0 | gcc -O2 | clang -O0 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 25 | 30 | 517 | 0.007 | 0.008 | 0.009 | 0.016 | 0.015 | 0.028 | 0.010 |
| 1 | 100 | 105 | 1906 | 0.009 | 0.011 | 0.011 | 0.019 | 0.019 | 0.063 | 0.012 |
| 1 | 400 | 405 | 7556 | 0.012 | 0.020 | 0.020 | 0.038 | 0.039 | 0.193 | 0.020 |
| 1 | 1600 | 1605 | 30156 | 0.028 | 0.060 | 0.066 | 0.113 | 0.121 | 0.790 | 0.055 |

## compilebench: compile latency (overview)

- revision `972e7dc676e3` (dirty); builds: `fcc` = /home/dp/.t3/worktrees/fai/t3-a2d8785d-3be030b8d3c44bdd/build/fcc/fcc (sha256 05e27148dfdc), `fir` = /home/dp/.t3/worktrees/fai/t3-a2d8785d-3be030b8d3c44bdd/target/release/fir (sha256 b936ffa78e51)
- host: Linux 6.18.60 x86_64, AMD Ryzen 9 9950X 16-Core Processor, 32 CPUs; load average 0.07 0.35 0.48 at the start, 1.49 1.04 0.76 at the end
- aarch64-unknown-linux-gnu-gcc (GCC) 16.2.0; clang version 23.1.3; rustc 1.99.0 (b940084d7 2026-09-28) (built from a source tarball)
- 10 rounds after a warmup, configurations shuffled per round. Wall and CPU in ms: median [quartiles] (min-max); peak RSS in MiB (max). "first run" is the warmup: fcc's include-probe cache is empty then (a cold cache), and warm after.

### Overview: Median wall time, ms

| workload | fcc-O.o | fcc-O.s | fcc-O0.o | fcc-x86-O.o | fir-O.s | clang-O0.o | clang-O2.o | clang-x86-O0.o | gcc-O0.o | gcc-O2.o | gcc-x86-O0.o |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| bintree | 19.9 | 13.7 | 20.2 | 28.2 | 2.4 | 14.3 | 22.2 | 20.1 | 19.5 | 170.9 | 18.2 |
| bytecode | 20.9 | 15.0 | 20.4 | 29.1 | 3.0 | 15.5 | 21.4 | 21.1 | 20.9 | 28.1 | 18.9 |
| crc32 | 21.3 | 14.0 | 21.9 | 33.6 | 3.3 | 13.6 | 20.5 | 19.5 | 20.0 | 27.0 | 18.0 |
| fannkuch | 19.7 | 13.6 | 20.1 | 28.5 | 2.7 | 15.1 | 26.3 | 19.5 | 19.1 | 29.5 | 17.4 |
| hashtab | 21.0 | 14.9 | 20.0 | 28.0 | 2.8 | 14.5 | 23.8 | 20.6 | 20.7 | 30.1 | 19.1 |
| mandel | 19.3 | 13.9 | 19.2 | - | 2.3 | 14.6 | 19.8 | 20.2 | 18.1 | 24.6 | 17.1 |
| matmul | 20.7 | 15.2 | 20.4 | - | 2.9 | 15.3 | 24.3 | 21.6 | 21.0 | 33.8 | 19.8 |
| nbody | 19.8 | 14.4 | 21.2 | - | 3.0 | 13.6 | 29.4 | 20.8 | 21.1 | 38.3 | 20.0 |
| nqueens | 18.1 | 12.6 | 17.5 | 27.0 | 2.1 | 13.4 | 18.0 | 18.6 | 18.5 | 23.8 | 17.2 |
| quicksort | 20.8 | 15.5 | 20.9 | 29.6 | 3.4 | 14.7 | 27.6 | 20.0 | 22.0 | 41.0 | 20.4 |
| sieve | 70.7 | 29.1 | 70.7 | 104.9 | 15.7 | 15.8 | 28.2 | 21.3 | 19.8 | 27.9 | 17.8 |
| strings | 21.8 | 15.8 | 21.4 | 30.2 | 3.7 | 16.3 | 28.0 | 20.4 | 21.7 | 41.5 | 20.0 |
| gen-100x10 | 68.0 | 43.8 | 64.8 | 75.4 | 24.2 | 42.8 | 280.3 | 53.3 | 121.3 | 226.8 | 110.4 |
| gen-400x10 | 196.9 | 117.3 | 190.8 | 202.6 | 66.2 | 128.9 | 1045.6 | 152.7 | 425.5 | 603.3 | 389.8 |
| gen-1600x10 | 747.7 | 436.0 | 708.2 | 714.9 | 265.0 | 464.7 | 4215.4 | 539.0 | 1661.7 | 2200.6 | 1504.7 |
| gen-1x400 | 39.3 | 25.8 | 38.2 | 47.6 | 13.8 | 22.1 | 97.3 | 28.6 | 40.8 | 194.6 | 34.3 |
| gen-1x1600 | 113.9 | 76.1 | 110.9 | 115.0 | 49.9 | 56.0 | 461.2 | 60.3 | 123.2 | 798.0 | 101.2 |
| gen-1x6400 | 501.6 | 362.0 | 484.5 | 419.3 | 261.2 | 214.5 | 4136.3 | 189.7 | 511.7 | 4455.6 | 406.3 |

### Overview: Median CPU time (user + system, with waited-for children), ms

| workload | fcc-O.o | fcc-O.s | fcc-O0.o | fcc-x86-O.o | fir-O.s | clang-O0.o | clang-O2.o | clang-x86-O0.o | gcc-O0.o | gcc-O2.o | gcc-x86-O0.o |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| bintree | 19.0 | 12.9 | 19.3 | 26.9 | 1.7 | 14.1 | 22.0 | 19.6 | 19.1 | 167.3 | 18.0 |
| bytecode | 19.9 | 14.0 | 19.4 | 27.3 | 2.1 | 15.3 | 21.1 | 20.5 | 20.1 | 27.3 | 18.3 |
| crc32 | 20.3 | 13.0 | 20.9 | 31.8 | 2.4 | 13.4 | 20.2 | 19.0 | 19.7 | 26.6 | 17.8 |
| fannkuch | 18.6 | 12.5 | 19.0 | 27.0 | 1.8 | 14.9 | 26.0 | 19.0 | 18.7 | 29.1 | 17.2 |
| hashtab | 20.0 | 13.8 | 18.9 | 26.6 | 1.9 | 14.3 | 23.5 | 20.1 | 19.9 | 29.7 | 18.5 |
| mandel | 18.5 | 13.2 | 18.5 | - | 1.6 | 14.4 | 19.6 | 19.6 | 17.7 | 24.3 | 16.9 |
| matmul | 19.5 | 14.1 | 19.3 | - | 1.9 | 15.1 | 24.1 | 21.1 | 20.2 | 32.9 | 19.2 |
| nbody | 18.6 | 13.3 | 20.0 | - | 2.0 | 13.4 | 29.1 | 20.3 | 20.1 | 37.2 | 19.1 |
| nqueens | 17.4 | 11.9 | 16.7 | 25.9 | 1.5 | 13.2 | 17.8 | 18.1 | 18.2 | 23.5 | 17.0 |
| quicksort | 19.5 | 14.2 | 19.6 | 27.3 | 2.1 | 14.5 | 27.3 | 19.5 | 21.0 | 39.8 | 19.5 |
| sieve | 68.9 | 27.7 | 69.0 | 102.1 | 14.3 | 15.6 | 27.9 | 20.7 | 19.5 | 27.5 | 17.6 |
| strings | 20.3 | 14.4 | 19.9 | 27.7 | 2.4 | 16.1 | 27.7 | 19.8 | 20.8 | 40.5 | 19.2 |
| gen-100x10 | 69.5 | 45.7 | 66.8 | 70.9 | 27.1 | 40.8 | 276.2 | 51.0 | 113.5 | 222.1 | 102.8 |
| gen-400x10 | 253.5 | 171.2 | 243.3 | 225.3 | 118.6 | 122.8 | 1032.6 | 145.7 | 408.1 | 593.7 | 371.2 |
| gen-1600x10 | 975.7 | 684.5 | 939.3 | 858.9 | 498.4 | 444.4 | 4170.3 | 517.0 | 1613.7 | 2172.3 | 1455.3 |
| gen-1x400 | 34.9 | 21.4 | 33.8 | 41.2 | 9.5 | 20.3 | 95.1 | 26.6 | 37.8 | 191.0 | 31.5 |
| gen-1x1600 | 103.4 | 66.0 | 100.2 | 99.1 | 39.7 | 50.0 | 454.0 | 54.9 | 113.0 | 787.0 | 91.4 |
| gen-1x6400 | 478.1 | 339.7 | 461.0 | 383.3 | 239.1 | 192.1 | 4098.8 | 169.6 | 492.2 | 4416.2 | 387.3 |

### Overview: Peak resident memory, MiB

| workload | fcc-O.o | fcc-O.s | fcc-O0.o | fcc-x86-O.o | fir-O.s | clang-O0.o | clang-O2.o | clang-x86-O0.o | gcc-O0.o | gcc-O2.o | gcc-x86-O0.o |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| bintree | 70.6 | 70.3 | 70.1 | 68.7 | 31.4 | 98.7 | 114.9 | 96.7 | 38.3 | 51.7 | 35.4 |
| bytecode | 70.6 | 70.6 | 70.6 | 69.3 | 31.4 | 99.7 | 115.7 | 101.0 | 38.8 | 42.6 | 35.8 |
| crc32 | 70.0 | 70.0 | 69.8 | 68.7 | 31.4 | 98.7 | 116.0 | 96.7 | 38.3 | 42.7 | 35.8 |
| fannkuch | 70.0 | 70.0 | 69.5 | 68.8 | 31.4 | 98.2 | 116.0 | 96.5 | 38.1 | 43.0 | 34.9 |
| hashtab | 70.3 | 70.3 | 69.8 | 69.0 | 31.4 | 98.9 | 115.2 | 96.7 | 38.8 | 43.2 | 36.1 |
| mandel | 69.8 | 70.0 | 69.8 | - | 31.4 | 98.4 | 114.2 | 96.5 | 38.4 | 42.4 | 35.1 |
| matmul | 69.8 | 69.8 | 69.7 | - | 31.4 | 98.7 | 116.0 | 100.5 | 39.6 | 44.2 | 36.8 |
| nbody | 70.3 | 70.3 | 70.1 | - | 31.4 | 98.9 | 115.9 | 97.0 | 38.9 | 44.2 | 35.4 |
| nqueens | 70.1 | 70.0 | 69.7 | 68.8 | 31.4 | 98.9 | 113.8 | 96.7 | 38.1 | 41.9 | 35.3 |
| quicksort | 70.1 | 69.8 | 69.8 | 68.5 | 31.4 | 98.4 | 116.2 | 96.2 | 38.6 | 43.9 | 35.6 |
| sieve | 73.4 | 73.4 | 73.1 | 117.0 | 31.5 | 98.7 | 117.0 | 96.5 | 38.1 | 42.7 | 35.1 |
| strings | 70.4 | 70.3 | 70.1 | 69.0 | 31.5 | 99.2 | 117.0 | 99.2 | 39.6 | 45.2 | 36.6 |
| gen-100x10 | 72.8 | 72.7 | 72.9 | 72.9 | 31.5 | 99.4 | 119.7 | 101.7 | 50.1 | 54.2 | 47.6 |
| gen-400x10 | 92.9 | 92.0 | 91.3 | 90.8 | 37.5 | 108.5 | 140.8 | 110.6 | 87.0 | 85.4 | 84.9 |
| gen-1600x10 | 185.5 | 184.9 | 182.4 | 179.2 | 134.3 | 145.8 | 235.1 | 148.2 | 235.1 | 213.2 | 234.2 |
| gen-1x400 | 69.4 | 69.4 | 68.4 | 67.2 | 37.9 | 99.9 | 115.8 | 100.5 | 46.2 | 54.6 | 41.9 |
| gen-1x1600 | 79.2 | 79.1 | 78.3 | 75.5 | 37.9 | 109.0 | 127.6 | 109.2 | 73.9 | 109.3 | 64.5 |
| gen-1x6400 | 192.7 | 192.8 | 190.5 | 140.0 | 139.1 | 154.2 | 185.7 | 147.6 | 187.2 | 413.1 | 158.7 |
