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
  (decision: Pointer bytes as integers; as built, `char` is `i8`: see Progress); `goto` and `switch` use `cf.blocks`; C unions are
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

## Progress

### Track F: C frontend (done)

`fai-cc` is in `frontends/c/` (about 2,600 lines of C++; build and usage in its README): Clang
parses and type-checks for `aarch64-unknown-linux-gnu` with the cross compiler's glibc headers,
and the AST is lowered to HFIR through `fir.h` only, verified, compiled with `fir_module_compile`
(`-O` runs the proved passes), and linked by the AArch64 C compiler. Decisions: C frontend, C
control flow, C struct layout, C external functions, C frontend testing, and Pointer bytes as
integers (`char` is `i8`, not `b8`).

- **Supported:** `_Bool`, `char` (unsigned), every integer type up to 64 bits, enums, pointers,
  arrays (multidimensional, flexible members), structs, unions, bitfields, typedefs, `const`; every
  integer and pointer operator, compound assignment, increment and decrement, short-circuit `&&`,
  `||`, `?:`, casts (integer↔pointer as `ptr.expose`/`ptr.from_exposed`), `sizeof`/`_Alignof`,
  string and compound literals, brace and designated initializers (local and global), struct
  assignment, the comma operator, direct and indirect calls; every statement, `goto` and `switch`
  with fall-through and Duff's device included, `static` locals, and globals initialized with
  integers, strings, and addresses of globals and functions; recursion; calls to libc as external
  functions; `malloc`/`free` as FIR heap allocations.
- **Rejected with a located diagnostic:** floating point and `_Complex` (F2), variadic functions
  (V), structs by value in calls (A), integers over 64 bits, `volatile`, `_Atomic`, VLAs, packed
  structs, thread-locals, inline assembly, statement expressions, computed `goto`, `++` on `_Bool`,
  wide strings, K&R definitions and calls without prototypes, external variables, and global
  initializers pointing inside an object.
- **Corpus:** 46 programs in `frontends/c/tests/` (each feature area, plus a hash table, four
  sorts, a bytecode interpreter, a tokenizer and expression evaluator, string routines, linked
  lists and a search tree on the heap, bignums, CRC-32, number theory, a BFS over a ring buffer,
  dynamic programming, and goto-, switch-, and Duff's-device-heavy programs) and 13 error tests.
  All 46 match the cross GCC at `-O1` under `qemu-aarch64`, with and without `-O`; 45 also match
  in `fir run` (the one that calls libc's `strlen`, `memcpy`, … can't be compared there). Every
  error test gets exactly its expected diagnostics. `cargo test -p fir-capi --test fai_cc` runs it
  (on Linux by default).
- **API added:** `fir_type_layout` and `fir_type_field_offset` (version 1.1), so the frontend checks
  every struct's FIR layout against Clang's.
- **API and IR friction found** (inputs for the next rounds):
  - No layout queries (added).
  - Global initializers can only name the start of a global, so `&table[2]` and `"abc" + 1` are
    rejected (Open item 1: initializers that point inside a global).
  - No external globals: `stdout`, `errno`, and any `extern int x;` defined elsewhere are rejected.
  - No linkage: C's `static` functions and globals become global symbols, so two `fai-cc` objects
    with the same `static` name don't link together, and generated names (`str.0`, `f.counter`)
    rely on `.` to stay out of C's namespace.
  - No fill op: zeroing a local aggregate copies a constant zero global of its type
    (`mem.copy`); a `mem.fill`/`memset` op would need neither.
  - `b8` can't be converted to an integer, so C's `char` can't be `b8`: `char` is `i8` (defined on
    pointer bytes, but exposing), and only whole objects of a known type copy exactly.
  - `i1` takes no bytes in memory, so `_Bool` is `i8`.
  - No unreachable terminator: every region must end in one, so code after `return` in a `cf.if`
    arm, or after a `cf.blocks` that never yields, gets a dead `func.ret poison` or `cf.yield`.
  - A value can't cross the blocks of a `cf.blocks` except as a block parameter; with locals in
    memory nothing needs to, but mem2reg in a frontend (or FIR) will thread them through.
  - One source file per function: code from macros and headers inside a function can't name its
    own file (ops get the expansion location).
  - Name lookups fail like errors: `fir_func_find` of a missing name overwrites the module's error
    message, and there is no `fir_global_find`.
  - Linking is the caller's job: `fai-cc` repeats `fir compile`'s choice of `$FIR_CC` and its
    command line.
- **Deferred:** floats, varargs, by-value structs, and `printf` (track F2); the gaps above;
  macOS binaries (the corpus needs Linux); an `effects` shorthand for "anything".
- **Fixed after review:** bitfields in bytes FIR's layout leaves implicit (a struct's tail, or the
  gap before an aligned member) had no padding slot, so global initializers dropped their bits;
  every gap holding bitfields now gets an explicit `array<k x i8>` slot. A compound literal that
  was a function's first stack slot (FIR id 0) was rejected as missing (`lookup`'s default);
  lookups of FIR ids use `find`. `bitfield_padding.c` covers both.

### Track M: Floats in the IR (done)

Decisions: Floats, Float ops, NaN choice, Float text.

- Lean: `spec/Fir/Float.lean` specifies IEEE 754 generically over the format (`FloatFmt`):
  decoding to a sign and a whole number of units (the smallest subnormal), each op's exact
  result as a rational number of units, one rounding function (`round`, ties to even),
  `sqrt` through an integer square root with a sticky bit, `fma` rounded once, conversions
  between formats and to and from integers, and NaN results as the oracle's choice
  (`nanResult`). `spec/Fir/FloatText.lean` reads and writes constants (the shortest decimal
  that rounds back). `f32`/`f64` are `Ty.float`, values `RVal.float`; the ops are in the op
  table (`float.*`, `int.to_float`), with new checks (`floats`, `numeric`, `sameWidth`,
  `floatBits`) and a `FloatBits` immediate; the interpreter runs them in `evalFloat`.
- Proofs (`spec/Fir/FloatProofs.lean`, no `sorry`, only `propext`, `Classical.choice`, and
  `Quot.sound`): rounding a representable value is the identity (`round_decode`, and
  `decode_round` the other way), `neg_neg`, `add_comm` and `mul_comm` up to the NaN choice
  (`nanResult_perm`), `cvt_cvt` and `ext_trunc` (`f32` through `f64` and back), and
  `truncInt_ofInt` (integers of at most `m + 1` bits; `f32` and `f64` instances).
  `Dce.float_pure` proves the float ops that can't trap pure. The existing proofs were
  extended for the new value (`RVal.float`: refinement, `Dse`, `Fwd.Exact` with floats, `Space`).
- Rust: `crates/fir/src/float.rs` (software arithmetic with NaN canonicalization, exact
  rounding for wide integers and decimals, the same shortest-decimal algorithm as Lean), the parser,
  printer, verifier, interpreter, builder (`float_const` and friends, generated), C API
  (`FIR_TYPE_F32`/`F64`, the `FirFBinOp`, `FirFUnOp`, `FirFPred`, `FirCvtEdge` constants,
  `fir_float_const_f32`/`_f64`, `FIR_TRAP_REASON_CONVERT`; version 1.2), lowering
  (floats scalarize like integers), and passes (`dce` deletes the pure float ops; `dse` and
  `fwd` handle float stores and loads). The AArch64 backend rejects floats with a compile
  error; its tests count and skip float runs, and the narrow fuzzer makes none.
- Tests: `tests/float/` (arithmetic and signed zeros, ties to even and subnormals at both
  formats' limits, NaN payloads through every copying op and memory, all 14 predicates with
  and without NaN, conversions at the limits for every modifier and width class, `fma` single
  rounding, `sqrt` of negatives and subnormals, `f64` → `f32` overflow and underflow,
  aggregates, unions, slices, and globals holding floats, and 20 error fixtures);
  `fir-ref test` passes on every file, and `fir run` prints what `fir-ref run` prints on every
  run line. The fuzzer generates float programs (every op and modifier, edge-case constants,
  floats in signatures, loop and block state, aggregates, unions, memory, and globals), checked
  against `fir-ref` and through lowering, the passes, and builder rebuilds (`FIR_FUZZ=3000` on
  seeds 7 and 11 for `fuzz.rs`, `opt.rs`, and `builder.rs`: no differences; float ops in about
  97% of the programs); `tests/capi/modules.c` builds, prints, and runs float functions through
  the C API and checks the compile error.
- Not yet: floats on AArch64 (track N), float initializers for globals (`zero` or `bytes` for
  now), `f16`/`bf16`.
- Fixed after review: the interpreter computed with the host's float arithmetic, so a C API
  caller's rounding mode or FTZ/DAZ changed its results (f32 `1 + 2^-24` gave `0x3f800001`
  rounding upward; two smallest subnormals summed to 0 under DAZ). `float.rs` now uses
  `rustc_apfloat`, an exact `u128` square root, and integer comparisons (decision: Float ops),
  checked against Lean's definitions on big integers and the host's default environment; a
  float-heavy `fir run` loop takes 1.7× as long, integer code is unchanged. `float_env.rs` runs
  every `tests/float/` run line with rounding toward +∞ and subnormals flushed (MXCSR or FPCR)
  and requires the expected outcomes (32 of 196 differed before).

### Track N: Floats on AArch64 (done)

Decisions: NaN choice (replaced), LFIR for AArch64, AArch64 semantics, Calling convention,
Instruction selection, Register allocation, Backend testing, Globals, Floats.

- **NaN choice:** the oracle is a structure (`Oracle`): `next` answers the sequential choices and
  `nan` picks a float op's NaN result from the op and its operands, so NaN payloads no longer
  share an answer with the next `freeze` or allocation, and hardware's fixed NaN rule is one of
  the choices. `Dce.evalFloat_oracle` proves every float op a function of the oracle (pure,
  deterministic, shareable); `Dce.float_pure` is unchanged.
- **Float globals:** `global @g: f64 = 1.5` and floats in `{…}` (`Init.float` with its format;
  the parsers read an initializer for its type), in both implementations, the builder, the C
  API (`fir_init_f32`, `fir_init_f64`; version 1.3), and the emitter.
- **LFIR:** FP registers `d0`…`d31` and virtual `fvN` (the top bit of `Reg` and `FirReg` is the
  class; `.s`/`.d` pick the width), and `fadd`/`fsub`/`fmul`/`fdiv`, `fmov` (also between
  classes), `fabs`, `fneg`, `fsqrt`, `fmadd` with the destination as addend (four registers don't
  fit `OpKind`), `fmov.imm` (Arm's 8-bit encoding), `fcmp`, `fcsel`, `fcvt`, `scvtf`/`ucvtf`,
  `fcvtzs`/`fcvtzu`, and FP `ldr`/`str`. `Fir.AArch64` specifies them in ASL's shape with Arm's
  NaN rules; `Fir.AArch64Proofs` proves each result one FIR allows, defines `Oracle.arm`, under
  which FIR's float ops compute the instructions' results exactly, and proves `fcvtz` is
  `float.to_int.*.sat`. Both machines check register classes, keep FP registers and FP virtual
  registers, follow AAPCS64 for floats (`abi.rs`), and check that `d8`…`d15` survive calls;
  `tests/lfir/floats.fir` runs them by hand.
- **Backend:** isel for every float op, `int.to_float`, `select`, `freeze`, `poison`, loads and
  stores, and float parameters, results, call arguments, and region state; the allocator's FP
  class (spills, scratch `d29`…`d31`, AAPCS64 clobbers, `d8`…`d15` saved in the frame, the
  checker over both classes); the emitter's FP instructions and float data, ELF and Mach-O.
- **Tests:** the backend harness passes floats as C types, renders their printed bits, and
  compares with `fir run` under Arm's NaN choice (`NanRule::Arm`), so native NaN payloads must
  be exactly the ones that allowed oracle gives. All 7 float fixtures with runs compile (except
  the runs that use integers over 64 bits); 188 float runs match natively (34 with NaN results),
  and every fixture's LFIR matches before and after allocation, also in `fir-ref`. The fuzzer's
  narrow mode makes floats (in about 98% of programs): `FIR_FUZZ=3000` on seeds 21 and 37 for
  `aarch64.rs` (about 3,100 float runs matching natively per seed, with and without `-O`, 54–68
  of them with NaN results), `fuzz.rs`, and `opt.rs`: no differences. `tests/capi/e2e.c`
  builds a float module through the C API that C calls (register and stack arguments, an HFA
  pair and a mixed pair, an `f64` global) and that calls libm's `sqrt` and `fabsf` and a
  ten-double C function, and checks that a FIR call keeps `d8`…`d15`; `modules.c` builds every
  new LFIR op and float initializer.
- **Not yet:** `fai-cc` still rejects floats (track F2); varargs with floats (track V) and HFAs
  by value (track A); macOS's argument packing; a four-register `fmadd`; a proof that isel
  refines its source.
- **Fixed after review:** the allocator's checker followed only value flow, so it accepted an
  FP virtual register in `x0`; it now first requires each virtual register's home to be an
  allocatable register of its class (never scratch, `x16`, `x18`, `x29`, `x30`, `sp`, `xzr`,
  `d29`…`d31`) or a slot of its own below the slot count (unit tests in `regalloc.rs`). The
  backend harness excused any numeric difference or arithmetic trap in a module that observed
  addresses anywhere (`ptr.addr` of null included, and every aggregate global counted as
  holding pointers), so a wrong float or a stray `convert` trap passed; a taint analysis
  (`tests/taint`: allocation-site points-to, calls, exceptions, branches taint their function)
  now excuses only tainted values, events' arguments, and traps at tainted locations, with
  self-tests for the reported outputs. It flags about 23% of the random programs (the old flag
  36%). The stricter rule exposed no backend bug; it needed two rules: a run that traps at a
  tainted location may stop before the other run's (deterministic) trap (`s21-p2636`), and
  `freeze` of what may be `poison` is the oracle's choice, 0 in the interpreter and the
  register's value in hardware (`s37-p621`), so the analysis tracks `poison`. Fixtures and
  `FIR_FUZZ=3000` on seeds 21, 37, and 53: no differences.

### Track F2a: floats in fai-cc (done)

Decisions: C frontend (float mapping, no contraction), C frontend testing.

- **Mapping:** `float` and `double` are `f32` and `f64` in values, memory, signatures (direct
  and indirect calls, AAPCS64 through FIR's calling convention), struct fields, arrays, unions,
  and globals. Literals are Clang's exact bits; `+ - * /` one `float.*` op each, never fused
  (`-ffp-contract=off`'s meaning; only `fma` fuses); unary minus `float.neg`; `< <= > >= ==` the
  ordered predicates and `!=` `une`; a float's truth `une` against 0.0; float→integer
  `float.to_int.*.ub`, integer→float `int.to_float` (a constant integer folds to the same
  rounded constant), `float.ext`/`float.trunc`; compound assignment and `++`/`--` through C's
  computation type. Global initializers (scalars, arrays, struct fields, union and bitfield byte
  images) take Clang's evaluated floats through `fir_init_f32`/`fir_init_f64`. Builtins with a
  FIR op are that op: the constants behind `INFINITY`, `HUGE_VAL`, `NAN` (`__builtin_nan("0x15")`
  keeps its payload), `__builtin_fabs`/`sqrt`/`copysign`/`fma`, `<math.h>`'s classifications
  (`isnan`, `isinf`, `__builtin_isinf_sign`, `isfinite`, `isnormal`, `signbit`, `fpclassify`
  as compares and `select`s), and `__builtin_isgreater` and friends; libm's functions are
  external calls. `long double` (binary128 on AArch64), `_Complex`, and the other formats stay
  diagnosed where used (`tests/errors/floats.c`).
- **Tests:** nine new corpus programs (55 in all): `float_arith` (every operator and
  comparison on pairs of edge values at both widths: signed zeros, infinities, subnormals, the
  limits, NaNs with payloads and signaling ones; ties to even; no contraction; compound
  assignment and increments; 51 NaN results checked bit for bit), `float_conversions` (every
  integer width to and from both formats at the edges of the range, rounding ties, overflow
  and underflow to `float`, NaNs through `ext`/`trunc`, `_Bool`), `float_aggregates`,
  `float_libm` (29 libm functions, the classification macros, the builtins), `float_calls` (ten
  float arguments, twenty mixed ones, function pointers to float functions), and the kernels
  `newton`, `float_matrix` (products, Gaussian elimination, power iteration), `integration`
  (trapezoid, Simpson, Kahan), and `mandelbrot`. All 55 match the reference natively without
  and with `-O`; 53 match in `fir run` under Arm's NaN choice (`float_libm` and `libc_calls`
  call other externals); 13 error tests.
- **Harness:** the reference compiles with `-ffp-contract=off` (GCC contracts across statements
  at `-O1` by default), every build links libm, and `fir run` picks NaNs by `NanRule::Arm`, so a
  printed NaN's payload must be the hardware's. Programs avoid two things C leaves open that GCC
  uses: the payload of an op on two different NaNs (GCC commutes `+` and `*`), and quieting by
  an op GCC folds away (`x * 1.0`). `fai_test.h` prints floats as bits and a rounded decimal.
- **API friction:** `fir_init_f32`/`fir_init_f64` take a host `float`/`double` while
  `fir_float_const` takes bits, so `fai-cc` copies Clang's bits into a host float to initialize
  a global; a signaling NaN survives that on AArch64 and x86-64 (no conversion in passing), but
  a bits-based initializer would make it exact by construction. Otherwise `fir.h` had every op
  the mapping needed.
- **Not yet:** `printf` with floats (track V); glibc's `isgreater` macros (statement
  expressions under Clang); float builtins without a FIR op (`__builtin_fmin`, …); rounding
  modes and exception flags (`FENV_ACCESS`).

## Not in this round

- Proofs beyond the float semantics and the purity of the new pure ops: scalarizing, lowering
  `cf.try`, composing rewrites, and the trust round's checkers stay open.
- `f16`/`bf16`, vectors, fast-math modifiers, rounding modes, `long double` beyond `double`
  (AAPCS64's `long double` is 128-bit; `fai-cc` rejects it), `_Complex`, atomics, threads,
  `volatile`, `setjmp`/`longjmp`, VLAs, inline assembly, and macOS binaries.
