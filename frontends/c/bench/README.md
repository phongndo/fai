# Measuring fai-cc's code

Tools to measure what `fai-cc`'s pipelines do to the C corpus (`../tests/*.c`), used for
[docs/design/05-optimizing-c.md](../../../docs/design/05-optimizing-c.md). Nothing here is
built by Cargo or CMake, and no test depends on it.

On an x86-64 host the binaries run under `qemu-aarch64`, whose wall time says little about
AArch64 hardware, so the measure is what the program *executes*: two QEMU TCG plugins count the
instructions run at guest addresses in a range (`count.c`: instructions, loads, and stores;
`hist.c`: per instruction, mapped to mnemonics with `objdump`). The range is the program's own
object's `.text` in a non-PIE link, so libc (`printf`), the output helpers
(`../tests/runtime/fai_runtime.c`), and the GCC-compiled C helpers (`../tests/extern/`) don't
count, and the same program compiled by GCC `-O1` is the yardstick.

```sh
nix develop                                     # qemu-aarch64, the AArch64 cross compiler
cmake --build build/fai-cc                      # the fai-cc to measure (or set BENCH_FAI)
frontends/c/bench/build-plugins.sh /tmp/bench   # libcount.so and libhist.so
BENCH_HIST=1 python3 -I frontends/c/bench/bench.py "$PWD" /tmp/bench
python3 frontends/c/bench/summarize.py /tmp/bench/results.json
```

Each program is built four ways (GCC `-O1`, `fai-cc`, `fai-cc -O`, and `fai-cc --passes
$BENCH_PASSES --experimental`, by default the experimental promotion pipeline
`mem2reg,stackdce,fwd,copyprop,dse,dce`; `BENCH_MORE="p,q;r,s"` adds a build per pipeline),
run, and checked against GCC's output and exit code: `summarize.py` lists any mismatch first. A
third argument to `bench.py` keeps only the programs whose names contain it. The results also
count the `mem.load`s, `mem.store`s, and stack slots left in each pipeline's MFIR (`--emit mfir`).
