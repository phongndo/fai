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
AROCC=/path/to/arocc uv run benchmarks/projects/projbench.py c23
uv run benchmarks/projects/projbench.py time --ssh MAC --docker alpine:3.22 \
    --docker-bin '/usr/local/bin/docker --context desktop-linux'   # native AArch64, as cbench
uv run benchmarks/projects/projbench.py report             # target/projbench/report.md
```

- **Projects:** Lua 5.4.7 (33 files, `-std=c23 -DLUA_COMPAT_5_3 -DLUA_USE_POSIX`) and SQLite
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
  `stackdce`), both `--experimental`. `--plain lvm` makes those two compile the named files
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
- **arocc** has no code generator yet (any function definition fails with "TODO implement
  lowering functions"), so it is compared as a parser and type checker only. Build it from
  https://github.com/Vexu/arocc with the Zig its `build.zig.zon` names
  (`zig build -Doptimize=ReleaseFast`); without `AROCC`, its rows are skipped.
- `lua/` holds the Lua workloads, written for this harness: `fib` (calls), `trees`
  (allocation and GC), `nbody` (floats in tables), `spectral` (numeric loops), `strings` (the
  string library), `sort` (`table.sort` with a Lua comparator), and `fannkuch` (small integer
  arrays).
