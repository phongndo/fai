# Measuring how fast fai compiles

`compilebench.py` measures the compiler's latency on one input: what an edit, compile, and test
loop waits for. It is not about the speed of the generated code (`benchmarks/c/cbench.py`), and
not about rebuilding the compiler. The results and what they mean are in
[docs/performance/compile-speed.md](../../docs/performance/compile-speed.md).

```sh
nix develop
cargo build --release --bin fir && cmake --build build/fcc      # the builds to measure
uv run benchmarks/compile/compilebench.py run                 # target/compilebench/report.md
uv run benchmarks/compile/compilebench.py run --only small --rounds 20
uv run benchmarks/compile/compilebench.py run \
    --fcc base=/path/to/old/build/fcc/fcc --fir base=/path/to/old/target/release/fir
```

- **Workloads:** `small` is the 12 programs of `benchmarks/c/programs`; `medium` and `large`
  are generated C (`cbench.synth`): 100, 400, or 1,600 functions of 10 statements, or one
  function of 400, 1,600, or 6,400 statements. `--only` takes workload names or sizes.
- **Configurations:** fcc to an AArch64 object at `-O0` and `-O`, to assembly (no assembler),
  and to an x86-64 object; `fir compile -O` from MFIR (fai alone, no C frontend); Clang and GCC
  at `-O0` and `-O2` for AArch64 with `cbench.py`'s flags (Clang with exactly fcc's Clang
  setup); and the host's Clang and GCC at `-O0` for x86-64. `--fcc NAME=PATH` and
  `--fir NAME=PATH` add other builds (a baseline), and the report says whether each build's
  outputs are byte-identical to the default build's.
- **Method:** one warmup round (its times are reported as "first run": fcc's include-probe
  cache is empty then), then `--rounds` rounds (10) with the configurations shuffled each round.
  Every run records wall time, CPU time with the children it waited for (the assembler, the
  include probe), and peak RSS (`wait4`). Phase breakdowns come from separate runs with
  `FIR_TIME=1`, so timing never perturbs the measured runs.
- **Limits:** Linux only (the reference compilers and the AArch64 glibc are the dev shell's).
  The host is whatever machine it runs on: the report records the CPU and the load average at
  the start and the end. The configurations don't produce code of the same quality, so the
  numbers compare compile time, not compilers.

Finer detail on any one compilation: `FIR_TIME=1 build/fcc/fcc FILE.c -O -o out.o` (or
`fir compile`) prints the phase report on stderr.
