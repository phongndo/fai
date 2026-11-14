# Measuring fcc's code

Two sets of tools; nothing here is built by Cargo or CMake, and no test depends on it. The
scripts are standard-library Python run by uv (`pyproject.toml` at the root), and `fai
verify` checks them with `ruff format --check`, `ruff check`, and `ty check`, which uv installs
(`uv run ruff format` applies the formatting).

- `bench.py` and its plugins measure what `fcc`'s pipelines do to the C corpus (`frontends/c/tests/*.c`),
  for [docs/design/05-optimizing-c.md](../../docs/design/05-optimizing-c.md). Below.
- `cbench.py` is the end-to-end baseline against GCC and Clang on the kernels in `programs/`:
  behavior, executed instructions, code size, compile time, and wall time on native AArch64 only,
  for [docs/performance/c-baseline.md](../../docs/performance/c-baseline.md). See the end.

On an x86-64 host the binaries run under `qemu-aarch64`, whose wall time says little about
AArch64 hardware, so the measure is what the program *executes*: two QEMU TCG plugins count the
instructions run at guest addresses in a range (`count.c`: instructions, loads, and stores;
`hist.c`: per instruction, mapped to mnemonics with `objdump`). The range is the program's own
object's `.text` in a non-PIE link, so libc (`printf`), the output helpers
(`frontends/c/tests/runtime/fai_runtime.c`), and the GCC-compiled C helpers (`frontends/c/tests/extern/`) don't
count, and the same program compiled by GCC `-O1` is the yardstick.

```sh
nix develop                                     # qemu-aarch64, the AArch64 cross compiler
cmake --build build/fcc                      # the fcc to measure (or set BENCH_FCC)
benchmarks/c/build-plugins.sh /tmp/bench        # libcount.so and libhist.so
BENCH_HIST=1 uv run python -I benchmarks/c/bench.py "$PWD" /tmp/bench
uv run benchmarks/c/summarize.py /tmp/bench/results.json
```

Each program is built four ways (GCC `-O1`, `fcc`, `fcc -O`, and `fcc --passes
$BENCH_PASSES --experimental`, by default the experimental promotion pipeline
`mem2reg,stackdce,fwd,copyprop,dse,dce`; `BENCH_MORE="p,q;r,s"` adds a build per pipeline),
run, and checked against GCC's output and exit code: `summarize.py` lists any mismatch first. A
third argument to `bench.py` keeps only the programs whose names contain it. The results also
count the `mem.load`s, `mem.store`s, and stack slots left in each pipeline's MFIR (`--emit mfir`).

## The end-to-end baseline: `cbench.py`

```sh
nix develop
uv run benchmarks/c/cbench.py all --ssh HOST [--docker IMAGE --docker-bin '…']
```

builds the 12 programs in `programs/` with `fcc`, `fcc -O`, GCC `-O0`/`-O1`/`-O2`, and Clang
`-O0`/`-O2` (static, against the target's glibc), checks every build's output against GCC
`-O2`'s, counts executed instructions and stack traffic under `qemu-aarch64` (`insn_count.c`),
times compilation and scaling on the host, and times the programs natively on `HOST`
(`benchrun.c`, which refuses to run under qemu-user), then writes `target/cbench/report.md`. Its
steps (`build`, `count`, `scaling`, `time`, `report`), options, and method are in the script's
docstring and in [docs/performance/c-baseline.md](../../docs/performance/c-baseline.md).
