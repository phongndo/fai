# Promotion on Lua and SQLite: the baseline

[05-optimizing-c.md](../design/05-optimizing-c.md) measured the experimental promotion passes
(`mem2reg`, `stackdce`) on the 67-program corpus: 32% fewer instructions executed than `fcc -O`.
This measures the same pipelines on the two real projects of [compilers.md](compilers.md), Lua
5.4.7 and SQLite 3.53.3, before any work of the promotion round
([06-plan.md](../design/06-plan.md)) starts. It is a baseline to measure that round against.
Every number comes from `benchmarks/projects/projbench.py`; the commands are at the end.

## Summary

- **Behavior: no difference found.** With promotion, Lua's own test suite passes (28 of 28
  files), the 7 Lua workloads print what GCC `-O2`'s build prints, and speedtest1's `--verify`
  hash of every query result is the one every other build gives.
- **Promotion does not pay on these programs yet.** In executed instructions of the project's own
  code, against `fcc -O`:
  - Lua, without its interpreter loop (below): 0.4% to 11% fewer per workload, 5% in the
    geometric mean.
  - SQLite outside `sqlite3VdbeExec`: 2.5% fewer.
  - `sqlite3VdbeExec`, SQLite's bytecode interpreter: **5.6× more** (1,389M to 7,790M), which
    makes speedtest1 as a whole 2.2× slower than with `-O`.
- **Lua's interpreter loop does not compile with promotion.** `fcc` on `lvm.c` takes 0.45 s and
  142 MiB with `-O`. With `fcc-m2r` it was stopped after 4.5 minutes at 7.5 GiB and growing,
  and with `fcc-promo` at 120 s and 2.9 GiB. `mem2reg` itself takes 0.03 s; a stack sample
  40 s into the compile is in the allocation validator, joining block states. The Lua numbers
  here are therefore with `lvm.c` compiled by `fcc -O` in every configuration.
- **SQLite compiles 14× slower with promotion**: `sqlite3.c` takes 20.5 s and 1.6 GiB against
  1.4 s and 253 MiB. The allocation validator (`aarch64.regcheck`) is 36 s of CPU time there.
- **Where `-O` stands:** `fcc -O` executes 2.27× GCC `-O0`'s instructions on Lua and 1.16× on
  SQLite (2.21× Clang `-O0`'s there: GCC `-O0` compiles SQLite's `switch` to a compare chain).
- **Why: promoted values are spilled.** speedtest1's accesses to the stack go *up* with
  promotion: loads from 1,033M to 1,527M, stores from 462M to 1,358M. The allocator
  (`targets/aarch64/src/regalloc.rs`) gives each virtual register one interval with no holes
  and takes hints only from moves to or from physical registers. So in a large function a
  value that is live across the body gets a stack slot, and each block parameter that
  promotion adds is a move on every edge into its block, between two slots when both are
  spilled. The corpus's functions are small enough for registers, which is the likely reason
  the corpus gains 32% and these programs don't; that was not measured function by function.

So the pass works and is not yet worth enabling: proving it now would prove a pass that makes
SQLite slower. The round's first track is the allocator
([06-plan.md](../design/06-plan.md#track-b-make-promotion-pay)).

## What was measured, on what

| | |
|---|---|
| Revision | `f82cc88` (`main`) with this change's harness options (`--configs`, `--plain`) and Lean file; no compiler source changed |
| Host | AMD Ryzen 9 9950X, NixOS, Linux 6.18.60, x86-64, shared with other work (load average 1.4 to 7) |
| Toolchain | the dev shell: Clang/LLVM 23.1.3 (fcc's frontend and the reference Clang), the AArch64 cross GCC 16.2.0, qemu-user 11.1.2 |
| Configurations | `fcc-O`: `fcc -O`. `fcc-m2r`: `fcc --passes mem2reg,fwd,copyprop,dse,dce --experimental`. `fcc-promo`: the same with `stackdce` after `mem2reg` (`fir::passes::EXPERIMENTAL_O`). GCC and Clang at `-O0`, GCC `-O2` as the behavior reference |
| `lvm.c` | compiled by `fcc -O` in `fcc-m2r` and `fcc-promo` (`--plain lvm`): it does not compile with either in practical time |
| Counts | executed instructions under `qemu-aarch64` with cbench's plugin, in the project's own code (libc excluded by the linker map). Exact and the same on every run |
| Compile time | one round (`--reps 1`), wall time and peak RSS from `wait4`, on a loaded host: read the ratios, not the digits |

## Executed instructions (millions, the project's own code)

| workload | fcc-O | fcc-m2r | fcc-promo | gcc-O0 | clang-O0 | gcc-O2 |
|---|---:|---:|---:|---:|---:|---:|
| lua-fannkuch | 154.0 | 152.2 | 151.3 | 68.1 | 66.9 | 24.7 |
| lua-fib | 25.9 | 25.9 | 25.5 | 11.7 | 11.7 | 4.0 |
| lua-nbody | 332.1 | 327.7 | 320.3 | 146.1 | 142.3 | 57.6 |
| lua-sort | 233.3 | 216.9 | 207.8 | 81.6 | 83.2 | 34.6 |
| lua-spectral | 204.9 | 205.0 | 204.0 | 89.5 | 88.5 | 30.3 |
| lua-strings | 57.1 | 54.0 | 51.2 | 28.6 | 28.6 | 13.2 |
| lua-trees | 127.6 | 120.4 | 116.0 | 60.4 | 58.4 | 22.5 |
| speedtest1 | 5,242.4 | 11,972.5 | 11,547.5 | 4,506.7 | 2,374.9 | 1,044.2 |
| **Lua, geometric mean vs gcc-O0** | **2.27×** | **2.21×** | **2.15×** | 1 | 0.99× | 0.38× |
| **speedtest1 vs gcc-O0** | **1.16×** | **2.66×** | **2.56×** | 1 | 0.53× | 0.23× |

speedtest1 by function:

| | fcc-O | fcc-m2r | fcc-promo | gcc-O0 | clang-O0 |
|---|---:|---:|---:|---:|---:|
| `sqlite3VdbeExec` | 1,389 | 8,039 | 7,790 | 2,637 | 618 |
| everything else | 3,854 | 3,933 | 3,758 | 1,870 | 1,757 |

speedtest1's memory accesses to the stack (millions):

| | fcc-O | fcc-promo | gcc-O0 |
|---|---:|---:|---:|
| loads | 1,033 | 1,527 | 728 |
| stores | 462 | 1,358 | 290 |

With promotion, speedtest1's most executed instructions are `mov` (3,398M, from 841M), `add`
(2,054M, from 610M), `ldr` (1,551M, from 1,041M), `str` (1,294M, from 385M), and `movk` (890M,
from none in the first ten): moves between spill slots, and the addresses of slots too far from
`sp` for an immediate.

## Compile time and size

| `sqlite3.c` | wall | peak RSS | `.text` bytes |
|---|---:|---:|---:|
| fcc-O | 1.40 s | 253 MiB | 2,071,360 |
| fcc-m2r | 24.27 s | 1,641 MiB | 3,069,064 |
| fcc-promo | 20.53 s | 1,617 MiB | 2,997,564 |
| gcc-O0 | 2.59 s | 316 MiB | 999,928 |
| clang-O0 | 0.89 s | 185 MiB | 1,013,860 |

`FIR_TIME=1` on `sqlite3.c` with `fcc-promo`: `opt.mem2reg` 175 ms, every other pass under 35 ms,
instruction selection 55 ms, `aarch64.regalloc` 18.5 s of the 20.0 s total, in which the
validator (`aarch64.regcheck`) takes 36.3 s of CPU time over its worker threads and assignment
0.13 s.

`lvm.c` (Lua's `luaV_execute`: computed `goto` through a label table, which fcc compiles to a
`switch` at every `goto *`): `fir opt --passes mem2reg` takes 0.03 s and turns 968 KB of MFIR
into 3.9 MB, because every branch of every `switch` now carries the promoted values as block
arguments. Instruction selection takes 0.06 s and gives 324,066 lines of LFIR against 54,597
without promotion (54,724 `mov`s against 6,328). `fir compile` of that module was stopped at
120 s and 3 GiB (0.33 s and 87 MiB for the module without promotion). One stack sample of it
under gdb, 40 s in: the main thread waits for the allocation workers, and the one worker
still running is in `regcheck::validate`, in `State::join`, copying a state's chunks.

Lua's objects are 9% smaller with promotion (518,748 bytes of `.text` against 569,252, with
`lvm.c`'s `-O` object in both); SQLite's are 44% larger.

## What this says to do

1. **The allocator before the proof.** The values promotion makes need registers, or at least
   one home each. Two changes are named by the measurements: give a block parameter and its
   arguments the same home when they don't interfere (so an edge moves nothing), and split
   intervals (or allocate per region) so a value live across a large function isn't spilled
   everywhere. Both are in the unproved allocator, whose every output the validator checks.
2. **The validator must scale on promoted code.** It takes 36 s of CPU time in SQLite's 20 s
   compile, and `lvm.c` does not finish: its one sample is in the validator's join. [c-baseline.md](c-baseline.md#3-the-register-allocation-validator-is-quadratic-compile-time)
   named its cost before promotion made it bite: its state is a set of values per location,
   per block. A likely cause of the growth here, which one sample doesn't establish: a `mov`
   the output left out makes the destination live wherever the source does, so the sets grow
   with every block-parameter move, and every join copies them.
3. **Compare against `-O` per function, not per corpus.** A gate for moving promotion into `-O`
   needs these two programs: the corpus alone said 32% better.

## Commands

```sh
nix develop
P="uv run benchmarks/projects/projbench.py --out target/projbench-promo --plain lvm"
C=fcc-O,fcc-m2r,fcc-promo,gcc-O0,gcc-O2,clang-O0
$P prepare                        # sources, SHA-256 pinned
$P build --reps 1 --configs $C    # objects, binaries, compile times, sizes: build.json
$P check --configs $C             # Lua's suite, the Lua workloads, speedtest1 --verify: check.json
$P count --configs $C             # executed instructions under qemu: count.json

# lvm.c with promotion (stop it by hand): the same commands without --plain, or
build/fcc/fcc target/projbench-promo/src/lua-5.4.7/src/lvm.c -std=c23 -DLUA_COMPAT_5_3 \
  -DLUA_USE_POSIX --emit mfir -o lvm.mfir
target/release/fir opt lvm.mfir --passes mem2reg,fwd,copyprop,dse,dce --experimental > lvm.promoted.mfir
FIR_TIME=1 target/release/fir compile lvm.promoted.mfir --emit asm > /dev/null
# where it is, 40 s in (gdb as the parent: ptrace_scope is 1 here)
timeout -s INT 40 gdb -q -batch -ex "set args compile lvm.promoted.mfir --emit asm > /dev/null" \
  -ex run -ex 'thread apply all bt 9' target/release/fir
```

`--configs` replaces projbench's configurations for `build`, `check`, and `count` (`report` and
`time` keep the published set); `--plain` names files the experimental fcc configurations
compile with `fcc -O`.
