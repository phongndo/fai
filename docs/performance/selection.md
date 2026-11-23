# What instruction selection cost on Lua and SQLite, and what changing it bought

[promotion-baseline.md](promotion-baseline.md) found `fcc -O` executing 2.27× GCC `-O0`'s
instructions on Lua. This is the round's steps 1 to 6
([06-plan.md](../design/06-plan.md#next-steps-in-order)): where those instructions went, by the
form of each one, what changing instruction selection did about it, the change to the C
frontend that was tried and taken out, and the baseline measured again. Every number comes
from `benchmarks/projects/projbench.py`; the commands are at the end.

## Summary

- **`fcc -O` executes 1.20× GCC `-O0`'s instructions on Lua, down from 2.27×**, and 1.19× Clang
  `-O0`'s on SQLite's speedtest1, down from 2.21× (0.63× GCC `-O0`'s, down from 1.16×: GCC
  `-O0` compiles SQLite's `switch` to a chain of compares). Lua's 7 workloads together go from
  1,135M to 587M, speedtest1 from 5,242M to 2,834M.
- **Behavior is unchanged.** Lua's suite passes (28 of 28 files), the Lua workloads print what
  GCC `-O2`'s build prints, speedtest1's `--verify` hash is the same, and `fai verify full`
  and `fai gate` pass.
- **No proved pass did this.** The changes are in instruction selection, which is tested, not
  proved, and they apply with and without `-O`. They close most of the speed gap to the
  unoptimized compilers and none of the gap between what is proved and what is fast.
- **Run time on hardware was not measured.** These are executed instructions under qemu.
  `projbench.py time` needs the AArch64 host.
- **Code is smaller and compiles faster:** Lua's objects are 377 KB of `.text`, from 569 KB
  (GCC `-O0`: 260 KB), and SQLite's 1.22 MB, from 2.12 MB (GCC `-O0`: 1.03 MB). `sqlite3.c`
  compiles in 1.0 s, from 1.4 s, and `lvm.c` in 0.19 s, from 0.45 s.
- **One change was tried and taken out.** Giving `goto *` one dispatch block (step 4) failed
  the three tests the plan set for it, so it was reverted. [`fai gate`](#the-gate) now makes
  that verdict for any change: it fails this one.
- **Promotion still does not pay.** `fcc-promo` executes 3.4× `-O`'s instructions on
  speedtest1, does not compile `lvm.c` in practical time, and on the rest of Lua executes
  1.8% fewer. That is the allocator's and its validator's work: steps 7 and 8.

## Where the instructions went (steps 1 and 2)

`projbench.py forms` names every executed instruction by form (mnemonic and operands, as
objdump prints them, and for loads and stores whether the access is to the stack). Lua's 7
workloads summed, the project's own code, in millions; "before" is `f82cc88`:

| form | fcc -O before | fcc -O now | gcc -O0 | clang -O0 |
|---|---:|---:|---:|---:|
| constant into a register | 168.8 | 20.3 | 7.8 | 9.3 |
| extension | 123.6 | 5.8 | 4.2 | 0.2 |
| stack load | 112.9 | 111.9 | 120.0 | 152.1 |
| add or subtract registers | 84.7 | 28.1 | 16.0 | 18.5 |
| conditional branch | 68.9 | 68.7 | 29.1 | 25.9 |
| compare | 56.8 | 56.6 | 36.9 | 0.0 |
| spill reload | 56.0 | 0.0 | 1.9 | 0.0 |
| stack store | 55.8 | 54.7 | 53.7 | 65.9 |
| frame address | 54.6 | 4.9 | 5.0 | 3.4 |
| other load | 46.5 | 46.4 | 46.5 | 46.3 |
| flags into a register | 32.8 | 12.1 | 7.8 | 7.0 |
| spill store | 27.0 | 0.0 | 1.9 | 0.0 |
| test of a register | 26.5 | 5.7 | 0.0 | 0.0 |
| multiply | 26.0 | 1.3 | 0.2 | 1.2 |
| shift by zero | 25.6 | 0.0 | 0.0 | 0.0 |
| register save and restore | 49.3 | 23.7 | 9.6 | 6.3 |
| logic | 23.5 | 23.5 | 36.4 | 18.4 |
| jump | 19.3 | 19.2 | 13.2 | 31.7 |
| stack pointer adjustment | 18.7 | 18.6 | 0.1 | 9.3 |
| shift | 16.1 | 36.2 | 26.0 | 16.2 |
| add or subtract an immediate | 4.3 | 14.8 | 17.4 | 31.7 |
| everything else | 37.3 | 34.8 | 52.2 | 34.7 |
| **all** | **1,135.0** | **587.3** | **486.0** | **478.2** |

(The "before" column was measured when Lua still seeded its string hashes from the time and
from addresses, which moved each workload's count by 0.005% to 0.3% between runs, and
`lua-nbody`'s by up to 5%. The harness now fixes the seed, and the other columns repeat to
within a few dozen instructions.)

What the "before" column said:

- **Step 1: the forms account for the excess.** fcc's excess over GCC `-O0` was 649M. The forms
  where fcc executed more add up to 709M (the rest is forms where it executed fewer), led by
  constants (161M more), extensions (119M), register adds (69M), spill reloads (54M), frame
  addresses (50M), register saves and restores (40M), conditional branches (40M), and
  `cset`, `tst`, `mul`, and `asr #0` at about 25M each.
- **What followed each constant:** an `add` 52.6M times, a `mul` 25.8M, an `and` 19.1M, a
  `cmp` 7.7M: operands an immediate, a shift, or an addressing offset replaces.
- **Step 2: the extra stack traffic was the allocator's, all of it.** fcc made 301M accesses to
  the stack and GCC `-O0` 187M. fcc's loads and stores of its own slots were GCC's (169M
  against 174M). The extra was 56M spill reloads, 27M spill stores, and 49M register saves and
  restores against 10M. **Every one of the 56M reloads reloaded an address** (the next
  instruction used the register as the base of a load or store): fcc kept each local's
  address in a virtual register from the function's entry, large functions spilled them, and
  each access to a local first reloaded where the local was.

speedtest1 had the same shape: 704M constants (GCC `-O0` 37M), 514M extensions, 289M spill
reloads, 225M frame addresses, 320M register saves and restores, 144M multiplies, 132M shifts by
zero.

## What changed (step 5)

Instruction selection (`targets/aarch64/src/isel.rs`; decision "Instruction selection"). Four
kinds of value no longer get a register where they are defined. A use that can take them some
other way does, and a use that can't builds the register there:

1. **An integer constant** is the immediate of an `add`, a `sub`, a bitwise op, a shift, or a
   comparison when it encodes as one, and a multiplication by a power of two is a shift.
2. **A frame slot's address** is `sp` plus an offset in the load or store that uses it, when
   the access stays inside the slot. Outside it (UB in the source) the address is computed
   into a register as before, because the allocation validator refuses code that names the
   frame's spill and save areas.
3. **A pointer plus a constant** is the base and offset of the load or store that uses it.
4. **A comparison** sets the flags right before the `cf.if` or `cf.cond_br` it decides, which
   branches on them: no `cset`, no `tst`. A 32-bit comparison compares the registers' low
   halves, with no extension.

And a register known to be extended already (a narrow load's result, an extension's, a small
constant's, an `and` with a mask) isn't extended again; an extension that would change nothing
(to `i128`, for the lowering's exact index arithmetic) reuses its operand's register.

No LFIR op was added: every instruction is one the dialect, its Lean semantics, and both
interpreters already had. Two tests' fixtures relied on a constant having its own instruction
(`tests/rust/debug_lines.rs`, `tests/rust/regcheck.rs`) and now use one that still does. The
rules were measured together, not one by one.

## Step 4: tried, failed its tests, taken out

`goto *p` is a `switch` over every label whose address the function takes, at each `goto *`,
which gives `luaV_execute` an edge from every case to every case. Step 4 made it a jump, with
the label's number, to one dispatch block that switches. The plan set three tests, and with
the change in:

| Test | Result |
|---|---|
| `lvm.c` with `fcc-promo` compiles within twice `-O`'s time and memory | **No.** It compiled, which it does not without the change: 5.3 s and 359 MiB, against `-O`'s 0.09 s and 79 MiB |
| Lua's suite passes with promotion | **No.** 24 of 28: `calls`, `coroutine`, `cstack`, and `errors` ended in a segmentation fault under qemu's 8 MiB stack. They recurse deeply, and the promoted `luaV_execute` had a 128,832-byte frame (3,312 with `-O`, 3,296 from GCC `-O0`): every spilled value has a slot of its own. It was stack exhaustion: all four passed with `qemu-aarch64 -s 64M` and with `-s 256M`. (With `-s 1G` the promoted binary faulted at once, even on `print(1)`, and `-O`'s did not; that was not looked into) |
| `-O`'s instructions on Lua don't go up | **No.** Every Lua workload executes more: 0.3% to 1.9% (a jump and a move at each dispatch) |

It also compiled `lvm.c` with `-O` in 0.09 s instead of 0.19 s, into 50 KB of `.text` instead of
120 KB, which none of its tests asked for. It was kept for one revision on that argument and
then reverted: a change that fails its test is not accepted
([06-plan.md](../design/06-plan.md#what-this-is-for-and-the-rule)). What it found stays true
and is steps 7 and 8's to fix: promotion's code does not fit in registers, and every spilled
value takes its own slot.

## The gate

`fai gate` ([benchmarks/projects/README.md](../../benchmarks/projects/README.md#the-gate)) is
that rule as a command: it builds Lua and SQLite, checks their behavior, counts every
workload's instructions, and compares with the tracked baseline
`benchmarks/projects/gate.json`. Its first version failed the unchanged tree: Lua's counts
moved between runs, because Lua seeded its string hashes from the time and from addresses.
The harness now fixes the seed, and the counts repeat to within a few dozen instructions. Run
on what this round has (the rejections by hand: nothing plants them automatically yet):

| Tree | Verdict |
|---|---|
| As it is, five times, once while `fai verify full` was running | **PASS**, "the same as the baseline" each time |
| With step 4's change | **FAIL**: all 7 Lua workloads execute more (`lua-spectral` +1.91%, `lua-fannkuch` +1.88%, down to `lua-strings` +0.34%); Lua's `.text` is 18.5% smaller, which doesn't buy a pass |
| `--configs fcc-promo --timeout 60` | **FAIL**: stopped, `lvm.c` did not compile in 60 s |
| `--plain lvm` (`fcc -O`, one file left out of the judgment) | **PARTIAL, not a pass** (exit 1); with `--update`, **NOT RUN** (exit 2) |
| `--configs fcc-promo --plain lvm` | **FAIL**: speedtest1 executes 244% more than `-O`, `lua-fib` 5.2%, `lua-strings` 3.7%, and `lua-spectral` 2.0% more; SQLite's `.text` is 96% larger; it compiles in 21 s against 1.1 s and peaks at 1,669 MiB against 226 MiB. (`lua-sort` executes 6.2% fewer, `lua-nbody` 3.3%, `lua-trees` 1.9%, `lua-fannkuch` 1.5%) |

## The validator on promoted code (step 3)

`perf` on `fir compile` of the promoted `sqlite3.c` (before the selection changes): 31% in
`Locs::join`'s loop over chunks, 11% in `Set::intersect`, 12% in `memmove`, and 31% in `malloc`,
`realloc`, and `free` under them; `Locs::alias` 5.5%. So about 85% is joining block states.

Counting, in the validator's walk of the largest function of each (with a temporary counter,
not committed; `luaV_execute` stopped after 18,000 visits):

| | blocks | instructions | locations per state | values per location | largest set | visits per block reached |
|---|---:|---:|---:|---:|---:|---:|
| `luaV_execute`, promoted | 19,320 | 298,512 | 1,240 | 42 | 68 | about 10 |
| `sqlite3VdbeExec`, promoted | 3,790 | 52,453 | 210 | 3.7 | 25 | about 7 |

A state is a set of values for each register and spill slot. On the promoted `luaV_execute`
each location holds 42 values on average, because a `mov` the output left out makes its
destination a second name for whatever its source was in, and nothing drops a name when the
value it names is dead. A set over 5 values is on the heap, a join intersects every pair of
sets, and each block is visited about 10 times before its state settles. The memory is the
states kept at each block's start: 1,240 locations of 42 values, for thousands of blocks.

What that says for step 7: drop from a block's starting state the values that are dead there
(a liveness pass over the input code). A dropped fact can only make the validator refuse
more, never accept more, so the pruning needs no trust: a wrong liveness makes a compile
fail, not a miscompile pass.

## The baseline again (step 6)

After the changes. `lvm.c` is compiled with `fcc -O` in the promotion configurations
(`--plain lvm`), as in the first baseline: it does not compile with them. Executed
instructions, millions, the project's own code:

| workload | fcc-O | fcc-m2r | fcc-promo | gcc-O0 | clang-O0 | gcc-O2 |
|---|---:|---:|---:|---:|---:|---:|
| lua-fannkuch | 82.8 | 81.6 | 81.5 | 68.1 | 66.9 | 24.7 |
| lua-fib | 13.9 | 14.6 | 14.6 | 11.7 | 11.7 | 4.0 |
| lua-nbody | 176.9 | 171.7 | 171.1 | 146.1 | 140.9 | 57.6 |
| lua-sort | 101.0 | 95.5 | 94.8 | 81.6 | 83.2 | 34.6 |
| lua-spectral | 108.5 | 110.7 | 110.7 | 89.5 | 88.5 | 30.3 |
| lua-strings | 32.7 | 34.0 | 33.9 | 28.6 | 28.6 | 13.2 |
| lua-trees | 71.5 | 70.4 | 70.1 | 60.4 | 58.4 | 22.5 |
| speedtest1 | 2,834.4 | 9,954.7 | 9,739.9 | 4,506.7 | 2,374.9 | 1,044.2 |
| **Lua, geometric mean vs gcc-O0** | **1.20×** | 1.20× | 1.19× | 1 | 0.99× | 0.38× |
| **speedtest1 vs gcc-O0** | **0.63×** | 2.21× | 2.16× | 1 | 0.53× | 0.23× |

The interpreter loops: `luaV_execute` is 384M with `-O` (GCC `-O0` 313M, Clang `-O0` 309M);
`sqlite3VdbeExec` is 734M with `-O` (Clang `-O0` 618M, GCC `-O0` 2,637M) and 7,291M with
`fcc-promo`.

Compile time and size:

| | `lvm.c` | | | `sqlite3.c` | | |
|---|---:|---:|---:|---:|---:|---:|
| | wall | peak RSS | `.text` | wall | peak RSS | `.text` |
| fcc-O | 0.19 s | 98 MiB | 120,080 | 1.01 s | 226 MiB | 1,181,080 |
| fcc-promo | does not compile (60 s) | | | 19.91 s | 1,586 MiB | 2,346,636 |
| gcc-O0 | 0.10 s | 67 MiB | 41,968 | 2.07 s | 317 MiB | 999,928 |
| clang-O0 | 0.05 s | 110 MiB | 44,836 | 0.73 s | 186 MiB | 1,013,860 |

Against checkpoint 1 (promotion at least 10% better than `-O` on both projects, no worse in the
interpreter loops, and within twice `-O`'s compile time and memory): on speedtest1 promotion
executes 3.4× `-O`'s instructions, 9.9× in `sqlite3VdbeExec`, and compiles `sqlite3.c` 20×
slower; `lvm.c` does not compile with it; and on the rest of Lua it executes 1.8% fewer. `-O`
got faster and promoted code mostly did not, since what it lacks is registers.

## What is left of `-O`'s excess on Lua

101M of 587M, against GCC `-O0`:

- **Dispatch: about 59M.** Conditional branches (40M more) and compares (20M more): Lua's
  `goto *` and every `switch` are trees of compares, where GCC and Clang jump through a table
  (`br`: 4.1M). A jump table needs an indirect branch in LFIR, with Lean semantics (step 10).
- **The prologue and epilogue: about 33M.** Four adjustments of `sp` per call where GCC makes
  one or two (18.5M more), and more callee-saved registers saved and restored (14M more).
  Frame lowering is in `regalloc.rs`, and the validator checks its shape.
- **The rest:** constants that are not immediates (12M more), register adds (12M), shifts
  (10M), jumps (6M).

## Commands

```sh
nix develop
fai gate                           # PASS or FAIL against benchmarks/projects/gate.json

P="uv run benchmarks/projects/projbench.py --out target/projbench-promo --plain lvm"
C=fcc-O,fcc-m2r,fcc-promo,gcc-O0,gcc-O2,clang-O0
$P prepare
$P build --reps 1 --configs $C     # build.json: compile time, memory, sizes
$P check --configs $C              # check.json: Lua's suite, the workloads, speedtest1 --verify
$P count --configs $C              # count.json: executed instructions
$P forms --configs $C              # forms.json, forms.md: executed instructions by form

# the validator's profile (step 3)
build/fcc/fcc …/sqlite3.c -std=gnu23 -DNDEBUG -DSQLITE_THREADSAFE=0 \
  -DSQLITE_OMIT_LOAD_EXTENSION -I … --emit mfir -o sqlite3.mfir
target/release/fir opt sqlite3.mfir --passes mem2reg,stackdce,fwd,copyprop,dse,dce \
  --experimental > sqlite3.promoted.mfir
perf record target/release/fir compile sqlite3.promoted.mfir --emit asm > /dev/null
perf report --stdio --sort symbol
```

`forms` and `gate` are new with this work. `forms` takes `--configs` as `count` does, or runs
fcc `-O` and GCC and Clang at `-O0`.
