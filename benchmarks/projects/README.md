# fcc against GCC, Clang, and arocc on whole projects

`projbench.py` measures what `benchmarks/c/cbench.py` (12 small kernels) and
`benchmarks/compile/compilebench.py` (compile latency) don't: two real C projects end to end, and
which C23 programs each compiler accepts. The results and what they mean are in
[docs/performance/compilers.md](../../docs/performance/compilers.md).

```sh
nix develop
uv run benchmarks/projects/projbench.py prepare            # sources, SHA-256 pinned, in target/projbench/src
uv run benchmarks/projects/projbench.py build              # compile times, sizes, binaries
AROCC=/path/to/arocc uv run benchmarks/projects/projbench.py frontend
uv run benchmarks/projects/projbench.py check              # behavior under qemu-aarch64
uv run benchmarks/projects/projbench.py count              # executed instructions under qemu
uv run benchmarks/projects/projbench.py forms              # the same, each instruction named by form
AROCC=/path/to/arocc uv run benchmarks/projects/projbench.py c23
uv run benchmarks/projects/projbench.py time --ssh MAC --docker alpine:3.22 \
    --docker-bin '/usr/local/bin/docker --context desktop-linux'   # native AArch64, as cbench
uv run benchmarks/projects/projbench.py report             # target/projbench/report.md

fai gate                                                   # one verdict for a change: PASS or FAIL
```

## The gate

`fai gate` (`projbench.py gate`) answers one question about a change to the compiler: are Lua
and SQLite still right, and no worse than what was accepted? It fetches the sources if it must,
builds both projects with `fcc -O` and with GCC `-O2`, runs Lua's suite, the Lua workloads, and
speedtest1 `--verify`, counts the instructions every workload executes, and compares with
`gate.json`, the accepted baseline, which is tracked. It prints what is worse and what is
better, and always ends with one of three lines:

| Last line | Exit | Means |
|---|---:|---|
| `gate: PASS` | 0 | right, and nothing worse than the baseline |
| `gate: FAIL` (or `gate: PARTIAL, not a pass`) | 1 | the change is not accepted; the lines above say why |
| `gate: NOT RUN: …` | 2 | the gate could not judge the tree: no baseline yet, or the wrong host |

The same verdict and reasons are in `gate-report.json` under `--out`. It takes about five
minutes, and runs where `count` does: on x86-64 Linux in the dev shell, under `qemu-aarch64`.
On an AArch64 host the instruction-counting plugin doesn't run, and the gate says `NOT RUN`.

It fails if:

- a file doesn't compile, or takes more than `--timeout` seconds (300 unless given);
- a build's behavior differs from GCC `-O2`'s (a workload's output, a file of Lua's suite,
  speedtest1's hash);
- a workload executes more instructions than the baseline's (by more than one part in
  100,000: the counts repeat to within a few dozen instructions);
- a project's `.text` is larger than the baseline's, at all;
- a project compiles in more than twice the baseline's CPU time plus a second, or peaks at
  more than twice its memory plus 64 MiB (these two are measured once on a shared host, so
  they get slack; nothing else does. CPU time, not wall time, so a busy host doesn't fail a
  change).

**A change that fails is not accepted**, whatever else it improves. `fai gate --update` writes
`gate.json`, and only when the gate passes, and then only lowers a number, so the baseline
moves one way: an improvement is kept by committing the new `gate.json` with the change that
made it. To accept a trade (more
instructions for something the gate doesn't measure), edit `gate.json` by hand, where the
diff says what was given up.

`--configs fcc-promo` (or any fcc configuration) gates that configuration instead. One with no
baseline of its own is held to `fcc -O`'s: a pipeline proposed for `-O` must be right and no
worse than `-O` on these programs. `--out` works as for `build`. With `--plain FILE,…` the
named files are compiled with `fcc -O` and so not judged: the best verdict is then
`PARTIAL, not a pass`, and `--update` is refused.

What the gate does not cover: run time on hardware (it counts instructions under qemu), x86-64
output, the 12 kernels of `benchmarks/c`, and anything but these two projects. It is not part
of `fai verify full` or of CI yet, and `fai mutate` doesn't plant defects against it: that it
fails what it should was checked by hand
([selection.md](../../docs/performance/selection.md#the-gate)).

- **Projects:** Lua 5.4.7 (33 files, `-std=c23 -DLUA_COMPAT_5_3 -DLUA_USE_POSIX`, and
  `-Dluai_makeseed(L)=0u`: Lua seeds its string hashes from the time and from addresses, which
  made every workload's instruction count differ from run to run, by 0.005% to 0.3% and
  `lua-nbody`'s by 5%; with the seed fixed they repeat to within a few dozen instructions) and
  SQLite
  3.53.3 (the 269,613-line amalgamation `sqlite3.c`, which `prepare` generates with SQLite's own
  build, and `test/speedtest1.c`; `-std=gnu23 -DNDEBUG -DSQLITE_THREADSAFE=0
  -DSQLITE_OMIT_LOAD_EXTENSION`). Lua's test suite comes from lua.org.
- **Configurations:** fcc and `fcc -O`, GCC and Clang at `-O0` and `-O2`, all to AArch64 Linux
  objects with cbench's setup (`cbench.Tools`: the same headers, `-ffp-contract=off`, no Nix
  hardening), linked statically by the cross GCC. `frontend` runs `-fsyntax-only` on GCC, Clang,
  and arocc, and reads fcc's own Clang and lowering phases from `FIR_TIME=1`.
- **Other configurations:** `--configs A,B,…` replaces the list for `build`, `check`, and
  `count` (it must keep `gcc-O2`, the reference), and may name fcc with an experimental
  pipeline: `fcc-m2r` (`mem2reg,fwd,copyprop,dse,dce`) or `fcc-promo` (the same with
  `stackdce`), both `--experimental`. `--plain FILE,…` makes those two compile the named files
  with `fcc -O`: `lvm.c` does not compile with promotion in practical time
  ([promotion-baseline.md](../../docs/performance/promotion-baseline.md)). `report` and `time`
  keep the published list.
- **Behavior:** `check` runs Lua's own test suite (28 files that run alone, portable and soft
  mode) and the Lua scripts in `lua/` with every build, and speedtest1 with `--verify` (a hash
  of every query result), against GCC `-O2`'s build. `c23` compiles, links, and runs each
  `frontends/c/tests/c23_*.c` program with GCC, Clang, and fcc, compares the outputs, and asks
  arocc to check it.
- **Timing:** compile times are the minimum of `--reps` interleaved, shuffled rounds (3 by
  default; the report used 5), with wall time, CPU time (with waited-for children: the
  assembler), and peak RSS from `wait4`. Run times are medians of `--rounds` rounds after a
  warmup (5 by default; the report used 11), natively through cbench's `benchrun`, which refuses
  to time under emulation.
- **Instructions:** `count` runs every workload under qemu with cbench's plugin
  (`insn_count.c`) and splits executed instructions into the project's own code and libc by
  the linker map, as `cbench.py count` does for the kernels.
- **Forms:** `forms` runs every workload as `count` does (for `--configs`, or fcc `-O` and GCC
  and Clang at `-O0`) and names each executed instruction of the project's own code by form,
  from its mnemonic and operands as objdump prints them: a constant into a register, an
  extension, a compare, a frame address, a spill reload (a load into one of fai's scratch
  registers from the frame), a stack load, and so on. It also reports what follows each
  constant, what each spill reload is for (an address or a value), the stack's accesses by
  form, and the same for the interpreter loops alone (`luaV_execute`, `sqlite3VdbeExec`). It
  writes `forms.json` and `forms.md`;
  [docs/performance/selection.md](../../docs/performance/selection.md) reads them.
- **arocc** has no code generator yet (any function definition fails with "TODO implement
  lowering functions"), so it is compared as a parser and type checker only. Build it from
  https://github.com/Vexu/arocc with the Zig its `build.zig.zon` names
  (`zig build -Doptimize=ReleaseFast`); without `AROCC`, its rows are skipped.
- `lua/` holds the Lua workloads, written for this harness: `fib` (calls), `trees`
  (allocation and GC), `nbody` (floats in tables), `spectral` (numeric loops), `strings` (the
  string library), `sort` (`table.sort` with a Lua comparator), and `fannkuch` (small integer
  arrays).
