# Plan: the C round

The previous round ([03-plan.md](03-plan.md)) built HFIR, MFIR, and LFIR down to AArch64 behind a
builder API. This round builds the first compiler on top of them, a C compiler. It also adds the
IR features C needs that are still missing: floats, varargs, and aggregates passed by value in the
C ABI. Decisions are in [decisions.md](decisions.md) (rows Next round, C frontend, Floats, Float
ops, Float semantics, NaN determinism).

```
 file.c ──clang (parse, type-check)──▶ AST ──fai-cc──C API──▶ HFIR ──fir lower/opt/compile──▶ AArch64 binary
```

## Done when

`fai-cc` compiles a corpus of C programs (integers, pointers, structs, unions, arrays, globals,
string literals, every statement form including `goto` and `switch`, function pointers,
`float`/`double`, variadic functions defined and called, structs passed and returned by value,
and calls to libc including `printf`) to AArch64 binaries whose output matches the same programs
compiled by clang, run under `qemu-aarch64` on Linux (natively on AArch64). Each program's HFIR also
runs in `fir run` with the same output where its run is defined.

## Tracks

| Track | What | Depends on |
|---|---|---|
| M: Floats in the IR | `f32`/`f64` types and `float.*` ops through Lean (bit-precise IEEE 754 semantics), the op table, both interpreters, verifiers, builder and C API, lowering, passes, fixtures, the fuzzer | — |
| F: C frontend | `frontends/c`: `fai-cc`, a Clang LibTooling tool that lowers Clang's AST to HFIR through the C API; the integer, pointer, aggregate-in-memory, and control-flow subset first; a differential test corpus against clang | — |
| N: Floats on AArch64 | FP/SIMD registers (`s`/`d`), float LFIR ops with Lean semantics, isel, a second register class in the allocator and its checker, AAPCS64 float arguments and results | M |
| V: Varargs | Variadic signatures, calls, `va.*` ops in Lean and Rust, their lowering, and AAPCS64's `va_list` on AArch64 (Linux), so FIR calls `printf` and defines variadic functions C can call | N |
| A: Aggregates by value | AAPCS64 composite rules for FIR functions and external functions: HFAs in float registers, composites up to 16 bytes in `x` registers, larger ones by reference, results through `x8` | N |
| F2: C frontend, complete | `float`/`double`, varargs, by-value structs, libc's `printf`; the full corpus | F, V, A |

M and F run in parallel; then N; then V and A one after the other (both change the calling convention); F2 last.

## Floats (track M)

- **Types:** `f32` and `f64` (IEEE 754 binary32 and binary64); `f16` and `bf16` stay decided but
  unbuilt. In memory they are their bits, little-endian; they align like the integer of the same
  width. `poison` and `freeze` work at float types.
- **Ops (dialect `float`, HFIR and MFIR):** `float.add`, `float.sub`, `float.mul`, `float.div`,
  `float.rem` (IEEE remainder is not C's `fmod`; leave it out unless trivial), `float.neg`,
  `float.abs`, `float.sqrt`, `float.fma`, `float.copysign`; `float.cmp.P` for the 14 ordered and
  unordered predicates (`oeq one olt ole ogt oge ord ueq une ult ule ugt uge uno`) giving `i1`;
  `float.ext` (f32 → f64, exact), `float.trunc` (f64 → f32, rounded); `float.to_int.s`/`.u` with a
  mandatory edge-case modifier for NaN and out-of-range inputs (`.ub` for C, `.sat` for Rust and
  AArch64's `fcvtz`, `.trap` with a new trap reason `convert`); `int.to_float.s`/`.u` (rounded);
  `float.from_bits`/`float.to_bits` (same width, exact); `float.const` with an exact value.
- **Semantics:** strict IEEE 754, round to nearest, ties to even, no fast-math modifiers yet, no
  exceptions flags or rounding-mode state. Specified in Lean bit for bit, generically over the
  format (exponent and significand widths), from the exact rational result and one rounding
  function, so proofs and the reference interpreter use the same definition. NaN results follow
  the NaN determinism decision: any NaN result is an oracle choice between the canonical quiet NaN
  and a quieted payload of an input NaN (Wasm's rule); the oracle that always answers 0 picks
  canonical. Copying ops (`neg`, `abs`, `copysign`, `from_bits`, loads, stores) keep payloads.
- **Text:** constants print as the shortest decimal that reads back exactly (`1.5`, `-0.0`,
  `1e300`), `inf`, `-inf`, and NaNs as `nan` (canonical) or `nan(0x…)` with their payload bits.
- **Testing:** fixtures in `tests/float/` with `// run:` lines; the fuzzer generates float
  programs; Rust's interpreter uses host IEEE arithmetic and must print what `fir-ref run` prints.
  Difficult cases (subnormals, ties, signed zeros, NaN payloads, conversions at the limits) get
  their own fixtures.

## C frontend (tracks F and F2)

- `frontends/c/`: `fai-cc` in C++ against Clang's LibTooling, built with CMake from the dev shell
  (which adds the LLVM/Clang libraries), linking `crates/fir-capi`'s static library. It builds
  modules only through `fir.h`; if the C API is missing something, the track adds it to the API.
- `fai-cc FILE.c [-O] [-o OUT] [--emit hfir|mfir|asm] [clang flags…]`: parse and type-check with
  Clang (preprocessor and headers included), lower the AST to HFIR, verify, then compile through
  `fir_module_compile` and link as `fir compile` does.
- **Mapping:** each C rule becomes an explicit modifier: signed `+ - *` are `.nsw` (overflow is UB
  in C; `poison` refines it); `/` and `%` are `int.div.s.ub`/`int.rem.s.ub`; shifts are `.ub`;
  unsigned arithmetic is `.wrap`; float-to-int conversion is `.ub`. Locals are `mem.stack` slots
  (mem2reg comes later); `char` accesses and `memcpy` are `b8` where bytes may hold pointers
  (decision: Pointer bytes as integers); `goto` and `switch` use `cf.blocks`; C unions are
  memory (a struct of the largest member's size and alignment), accessed through pointers.
- **Tests:** a corpus of C programs under `frontends/c/tests/`, each compiled by `fai-cc` and by
  clang, run, and compared; until varargs land, output goes through a small extern print helper
  instead of `printf`.

## Varargs and aggregates by value (tracks V and A)

Designed when their tracks start, against AAPCS64 (Linux first; macOS's variant, where variadic
arguments all go on the stack, stays open). Constraints: a variadic call names its fixed and
variadic argument types; `va.start`, `va.arg T`, `va.copy`, `va.end` work on a `va_list` the
target lays out (AAPCS64's five-field structure on Linux), so FIR can pass one to `vprintf`; by-value
aggregates in signatures follow AAPCS64's classification and lower to scalars, registers, and
memory exactly as clang does, so FIR and clang-compiled C call each other.

## Not in this round

- Proofs beyond the float semantics and the purity of the new pure ops: scalarizing, lowering
  `cf.try`, composing rewrites, and the trust round's checkers stay open.
- `f16`/`bf16`, vectors, fast-math modifiers, rounding modes, `long double` beyond `double`
  (AAPCS64's `long double` is 128-bit; `fai-cc` rejects it), `_Complex`, atomics, threads,
  `volatile`, `setjmp`/`longjmp`, VLAs, inline assembly, and macOS binaries.
