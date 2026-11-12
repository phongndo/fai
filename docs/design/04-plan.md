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
  clang, run, and compared; most print through a small extern print helper, whose calls the
  interpreter's run can be compared on, and some through `printf` (track F2b).

## Varargs and aggregates by value (tracks V and A)

Designed when their tracks start, against AAPCS64 (Linux first; macOS's variant, where variadic
arguments all go on the stack, stays open). Tracks V's and A's designs are in their Progress
entries. Constraints: a variadic call names its fixed and
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

### Track V: Varargs (done)

Decisions: Varargs, va_list (new), and Calling convention, External functions, External call
semantics, Function pointers, Instruction selection, LFIR for AArch64, AArch64 semantics,
Register allocation, Data layout, Aggregates, Memory bytes, Stack lifetime, Builder API, API,
Lowering proofs, Backend testing, C external functions.

- **IR:** `func @f(%fmt: ptr, ...)`, `extern func @printf(ptr, ...) -> i32 …`, and
  `func<(ptr, ...) -> i32>`; a call writes `...` before its variadic arguments
  (`func.call @printf(%fmt, ... %x, %y)`), where the callee's signature says, which the parsers
  check and the printers follow (the op doesn't store it, so the call ops, builder methods, and C
  functions are unchanged). Variadic arguments are `iN`/`bN` of 8 to 64 bits, `ptr`, `f32`, or
  `f64`, passed as given. `va_list` is a memory type laid out by the memory space (`valist 32:8`
  by default, AAPCS64's on Linux). `va.start`, `va.arg`, `va.end` (HFIR and MFIR); `va_copy` is
  `mem.copy va_list`.
- **Semantics (Lean, both interpreters):** a call of a variadic function puts its variadic
  arguments in an allocation of their own (`AllocKind.va`), freed when the call returns; a
  `va_list` holds a cursor (`Byte.va` bytes naming that allocation and a position) that only
  `va.arg` reads and that reads as `poison` as anything else; `va.arg` reads the next argument's
  bytes as its result type, and is UB `va-arg` without a cursor, past the end, or across classes
  (integer and pointer, or float), `use-after-free` after the call returned. Indirect calls
  through the other kind of signature are `bad-call`. External calls show every argument, and a
  `va_list` an external function reads lets it reach the arguments.
- **Proofs:** every existing proof builds, with no `sorry`; `#print axioms` of `Dse.refines`,
  `Fwd.refines`, `CopyProp.refines`, `Dce.refines`, `Lower.Proof.Expand.refines`,
  `lowerFunc_refines`, `step_space`, and `step_trace` shows only `propext`, `Classical.choice`,
  and `Quot.sound`. The lockstep layer (`execFlat_eq`), copy propagation, and `Space` handle
  `va.start`, which reads the stack, and variadic calls (`enterFunc`); `Pure` and `RunsPure`
  exclude `va.start`; the refinement theorems take `tgt.variadic = src.variadic`. No new theorem
  about varargs: the argument that native code refines the cursor model is in decision va_list.
- **AArch64 (Linux):** variadic calls are `adrl.func` + `blr` with the call's argument types as
  the signature; a variadic function that uses `va.start` saves the leftover `x` and `d`
  argument registers in register save areas; `va.start` and `va.arg` (AAPCS64's algorithm) are
  plain LFIR instructions, so neither the LFIR op set nor the register allocator and its checker
  changed. The LFIR machines (Lean and Rust) read an external callee's arguments by `blr`'s
  signature. `--os darwin` rejects varargs with a compile error.
- **Builder and C API (version 1.4):** `declare_func_va`, `extern_func_va`, `func_ty_va`;
  `FIR_TYPE_VA_LIST`, `fir_type_func_va`, `fir_func_declare_va`, `fir_extern_declare_va`,
  `fir_module_set_va_list`, and the generated `fir_va_start`, `fir_va_arg`, `fir_va_end`.
- **Tests:** `tests/varargs/` (definitions and calls with mixed classes, more than eight of each
  class, `va_copy`, a `va_list` passed to another function and in a struct, nested variadic
  calls, restarts, narrow and wide reads, a `va_list`'s bytes, variadic externs and indirect
  calls; 30 run lines, 10 of them UB (`va-arg`, `use-after-free`, `bad-call`), and 19 error
  fixtures): `fir-ref test` and `fir run` agree on every run line; every run that the
  backend compiles matches natively under qemu, with and without `-O`, and in LFIR before and
  after allocation (also in `fir-ref`). `tests/capi/e2e.c` builds a module through the C API
  that calls glibc's `printf` (directly and through a pointer), `snprintf` (integers on the
  stack), and `vprintf` through a `va_list` it starts and copies, and that C calls with twelve
  ints and twelve doubles; the native output must equal the host's `snprintf` of the same
  formats. The fuzzer makes variadic functions (the entry included) and external functions,
  calls passing their usual argument types or others, and `va.arg` (sometimes of another width,
  class, or past the end), restarts, copies, and ends: `FIR_FUZZ=3000` on seeds 43 and 59 for
  `fuzz.rs`, `opt.rs` (in a release build: a few seed-59 programs' lowered runs take minutes in
  the interpreter, varargs or not), `builder.rs`, and `aarch64.rs`: no differences. Per seed,
  about 1,620 of the 3,000 programs have variadic functions and 720 `va.arg`, about 105 runs end
  in `va-arg` UB, and about 1,700 runs of programs with varargs match natively with and without
  `-O` (22 and 15 modules aren't run natively: a variadic external function called with
  several argument lists). The first native runs found that a `va_list`'s bytes, loaded as
  `bN` and returned, are the cursor's in FIR and the target's natively: any byte now refines a
  cursor's, as it refines `poison` (`Byte.Refines`).
- **Not yet:** `fai-cc`'s varargs (track F2); macOS's variant (open item 4); aggregates as
  variadic arguments (track A); integers wider than 64 bits as variadic arguments.
- **Fixed after review:** variadic arguments take 8-byte slots, but a pointer was encoded at its
  full width, so with `memspace default ptr 128 addr 64` the next argument overwrote a pointer's
  upper bytes (both interpreters agreed, so nothing compared differently); the verifier, the
  builder, both interpreters' entry arguments, and the variadic-arguments allocation now allow a
  `ptr` only where pointers take at most 64 bits (`SpaceCfg.isVararg`, decision: Varargs), and
  the fuzzer passes an `i64` in its place under wider pointers (`tests/varargs/layout.fir`,
  `layout-wide.fir`, and three error fixtures). The backend harness's taint analysis joined
  every variadic argument in the module into one list every `va.arg` read, so an address passed
  to one function excused a difference in another's; it now keeps a summary per callee, and a
  `va_list`'s bytes name the functions whose `va.start` wrote them, through copies and pointers.
  It also counted the location of any tainted op as a tainted trap location, so `trap overflow`
  at an `int.add.wrap` was excused; it now records only ops that can trap, with their reasons,
  and excuses a trap only when its reason is one of them and every op at its location that can
  trap with it is tainted. Self-tests reject both reported outcomes and accept the legitimate
  cases.

### Track F2b: varargs and printf in fai-cc (done)

Decisions: C frontend (varargs mapping), C external functions, C frontend testing; Varargs and
va_list (track V) unchanged.

- **Mapping:** a C function with `...` is a variadic FIR function (`fir_func_declare_va`), an
  undefined one a variadic external function with every effect (`fir_extern_declare_va`), and a
  pointer to one has a variadic signature (`fir_type_func_va`), so calls are the same
  `fir_func_call` and `fir_func_call_indirect` with the variadic arguments after the fixed ones.
  The variadic arguments are what Clang's AST already holds: C's default argument promotions are
  implicit casts (`float` to `double` is `float.ext`, `char` and `short` to `int` an extension),
  so every one is an `i32`, `i64`, `ptr`, or `f64`. `va_list` is, on AArch64 Linux, the struct
  `__va_list`, not an array (x86-64's): it maps to FIR's `va_list` memory type wherever it is an
  object (locals, globals, struct fields, arrays), checked against Clang's size and alignment.
  `__builtin_va_start` (and C23's `__builtin_c23_va_start`), `VAArgExpr`, `__builtin_va_end`, and
  `__builtin_va_copy` are `va.start`, `va.arg` of the type's FIR type, `va.end`, and
  `mem.copy va_list`. A `va_list` parameter is a `ptr`, as AAPCS64 passes a composite larger than
  16 bytes: the caller copies the argument into a `mem.stack.of va_list` of the call's region and
  passes its address, and the callee uses the pointer as its parameter's object. So C-defined
  functions taking a `va_list` and libc's `vprintf`, `vsnprintf`, `vfprintf` are called alike,
  directly or through pointers, and a callee's `va_arg`s leave the caller's cursor where it was
  (in C it is indeterminate). Structs and unions as variadic arguments or `va_arg` types (track
  A), `long double` arguments (`%Lf`), and returning a `va_list` are diagnosed.
- **Tests:** five new corpus programs (60 in all): `varargs` (variadic definitions printing
  through the helpers: sums, mixed classes, promoted `char`/`short`/`float`/`_Bool`/enum
  arguments, twelve longs and twelve doubles so both classes spill to the stack, `va_copy`, a
  `va_list` passed by value and by pointer and kept in a struct, restarts, pointers through the
  arguments, the limits of each type, nested variadic calls, calls through pointers to variadic
  functions), `varargs_printf` (a printf written over `va_arg`, checked against `vsnprintf` on
  `va_copy`'s copy of the same arguments, and forwarding from `...` through two functions taking
  a `va_list`), `printf_ints` (every length modifier, conversion, and flag at each type's limits,
  `*` widths and precisions, printf's result; `%p` into a buffer checked by `sscanf`),
  `printf_floats` (`%f %e %g %a` and upper-case forms with widths, precisions, and flags on signed
  zeros, subnormals, the limits, infinities, NaNs, ties, and promoted floats), and
  `printf_strings` (`%s` and `%c`, `puts`, `sprintf`, `snprintf` truncation and sizing,
  `vsnprintf` and `vprintf` wrappers, `fprintf` and `vfprintf` into `fmemopen`'s stream).
  `crc32`, `game_of_life`, `knapsack`, `libc_calls`, and `float_libm` now print with `printf`
  (the last two already called other externals). All 60 match the reference natively without and
  with `-O`; 51 match in `fir run` (`varargs` among them), and the 9 that call other external
  functions are listed with the first one (`printf`, `vsnprintf`, `strlen`) instead of being
  compared; 13 error tests (`errors/varargs.c` now holds what is still missing).
- **API friction:** none in building variadic signatures, calls, or the `va.*` ops: the C API's
  split of the call by the callee's signature meant no new call functions. Two gaps: FIR has no
  external globals, so `stdout` and `stderr` (and `fprintf` to them) stay out until it does; and
  passing a `va_list` by value is the frontend's job, in AAPCS64-Linux's form (the address of a
  copy). That form fits x86-64 too (an array, which decays to its address), but not macOS's or
  Windows's `char *` `va_list`, which is passed as its value: a load of the cursor's bytes, which
  FIR's semantics reads as `poison`. Open item 4 will need a way to pass a `va_list` by value.
- **Not yet:** external globals (`stdout`, `stderr`, `errno`); structs and unions by value,
  variadic ones included (track A); `long double`.

### Track A: Aggregates by value (done)

Decisions: C ABI for aggregates (new), and Calling convention, Aggregates, Aggregate values,
External functions, External call semantics, Varargs, HFIR lowering, Lowering proofs, Layers,
Instruction selection, Backend testing, Builder API, API.

- **Where the ABI is applied:** calls pass structs and arrays whole. Outside HFIR a value may be
  a composite (a struct or array of scalars and composites), made by `agg.make`, taken apart by
  `agg.extract`/`agg.insert` (now MFIR ops too), copied, and passed as a parameter, call
  argument or result, `va.arg` result, or a function's only result; MFIR memory stays scalar.
  The lowering keeps composites whole exactly there (`agg.make` where one is passed,
  `agg.extract`s where it arrives) and scalarizes the rest as before, so MFIR names only the
  ABI's unit and the backend classifies. HFIR's semantics of aggregate calls is unchanged, and
  MFIR's composites are the same tuples of leaves.
- **AAPCS64** (`spec/Fir/AArch64Abi.lean`, twin `abi.rs`): empty composites take nothing; HFAs
  (one to four floats of one format, no padding, no zero-length array: GCC's rule) take FP
  registers or, closing them, the stack; up to 16 bytes take one or two `x` registers (even
  first if 16-byte aligned) or, closing them, the stack; larger ones are a pointer to a copy in
  the caller's frame; results go where the first argument would, or at `x8`. Variadic composites
  go as named ones and `va.arg` follows AAPCS64's algorithm (general-purpose or FP save area,
  stack, by reference). `--os darwin` rejects composites passed on the stack.
- **Proofs:** every proof builds, with no `sorry` and no warnings; `#print axioms` of the main
  theorems shows only `propext`, `Classical.choice`, and `Quot.sound`. `Fir.AArch64Abi` proves
  that a composite's register pieces are its bytes (`pieces_flatten`), that a defined piece put in
  a register and stored back is itself, a pointer's eight fragments that pointer
  (`Word.bytes_ofBytes`), and so that registers carry a composite's defined bytes exactly
  (`roundTrip`). `lowerFunc_refines` covers what it covered (functions with no aggregate
  values; one that passes a struct has one).
- **Semantics (Lean, both interpreters):** external functions take and give structs and arrays
  (a struct result only alone); their events show them as values, pointers in their leaves are
  argument pointers for reach and `read(args)`, and the world's composite results are checked
  leaf by leaf. Variadic composites are C's (`struct<C>` and arrays, whose layout a value's
  shape gives), a slot each of their size rounded to 8; `va.arg T` of one needs its type up to
  an array being the struct of its elements, else UB `va-arg`. Both LFIR machines read an
  external callee's composite arguments and place its composite results by the ABI.
- **Backend:** a composite value is its leaves' registers; isel packs them into words (a
  pointer that fills a word moves as it is, keeping its provenance) or FP registers, stores
  them to the stack, a frame copy, or `x8`'s memory, and unpacks them where they arrive;
  `va.arg` of a composite, and variadic functions' save areas counted with composites. The
  allocator's call shapes come from the ABI (blr's precomputed per signature).
- **Text:** an op with no operands and no location no longer swallows the next line's result
  (`agg.make` of an empty composite, which the lowering emits): a `%name` followed by `:`
  starts the next op, in both parsers.
- **Tests:** `tests/abi/` (every class as parameter and result, 1 to 16 bytes with padding,
  floats mixed with integers, a 16-byte aligned struct, packed fields across words, large
  structs written by the callee, pointers dereferenced after crossing, empty, `auto`, and packed
  structs, stack placement after a class's registers close, nested and indirect calls, external
  calls, and variadic composites of every class, after the registers fill, read back as arrays,
  and UB for a wrong type; an MFIR module making, inserting into, and passing composites: 23 run
  lines); `fir-ref test`, `fir run`, the lowering, and native
  runs under qemu (with and without `-O`, and the LFIR before and after allocation in both
  machines) agree. `crates/fir/tests/abi.rs` is the ABI torture test: random signatures (up to
  12 arguments, structs of `i8`…`i64`, `f32`, `f64`, `ptr`, arrays, nested, packed, and 16-byte
  aligned structs, HFAs of 1 to 4 members) compiled by the cross GCC and FIR, each side calling
  the other directly and through `...`, every leaf reported and compared; 25 seeds of 1,000
  signatures each (about 14,000 leaves per seed in each of four directions) pass. It found GCC's
  HFA rule: a struct of floats with a zero-length array (even of floats) isn't one.
  `tests/capi/e2e.c` builds a module through the C API that C calls with every class (a large
  struct whose copy the callee keeps to itself), that calls C with them directly and through
  `...`, and reads C's composite variadic arguments, natively with and without `-O`, and checks
  the macOS rejection. The fuzzer gives external functions composite parameters and results and
  passes composites as variadic arguments (not the entry's, whose run lines can't write them);
  `FIR_FUZZ=3000` on seeds 67 and 73 for `fuzz.rs`, `opt.rs`, `builder.rs`, and `aarch64.rs`:
  no differences. Per seed 470 to 500 modules pass composites to or from external functions,
  145 to 170 pass them through `...`, 43 to 48 read them with `va.arg`, and 790 to 850 native
  runs (each with and without `-O`) pass structs by value. Seed 71 is the same except one
  program (`s71-p534`, no composites in it), whose exposed address of an 8-aligned zero-size
  stack slot is 16-aligned natively and in LFIR: every interpreter layout keeps bit 3 set, so
  main's moved-bits rule counts it as a difference; main fails it alike as a fixture (open). The
  native harness declares C structs of each composite's layout and class and prints them as
  `fir run` renders them. Its direct selection of HFIR (main's coverage builds) found that isel
  took a struct among several results, which only the lowering may scalarize, as one register:
  it refuses it now, as HFIR only. `cargo xtask verify full` requires the ABI torture test's
  evidence (240 signatures).
- **API:** version 1.5 (no new functions; external and MFIR functions take composites).
- **Not yet:** `fai-cc`'s structs by value (done in track F2c); macOS's stack packing (composites
  on the stack are a compile error there); integer leaves wider than 64 bits in a passed composite
  (`__int128` fields: the backend rejects them); composites in MFIR region state and memory
  accesses (the lowering never makes them; isel rejects them); other targets' classifications.

### Track F2c: structs and unions by value in fai-cc (done)

Decisions: C frontend (by-value mapping), C struct layout (empty structs), C frontend testing
(helpers compiled by the reference compiler, the ABI torture); C ABI for aggregates unchanged.

- **Mapping:** a struct or union passed by value (parameter, result, variadic argument,
  `va_arg`, direct and indirect calls, to and from functions defined here or compiled by GCC) is a
  FIR composite value: `mem.load` of its ABI type from the C object where it is sent, `mem.store`
  into one where it arrives. A call's or `va_arg`'s result is stored into a temporary made at the
  function's entry (as every local is), so `f().x`, `f().a[i]`, `g(f())`, `s = f()`, and
  `c ? f() : g()` are ordinary accesses to it (Clang's `MaterializeTemporaryExpr` and
  `ExprWithCleanups` are looked through). The ABI type gives FIR's classification GCC's class
  for the C type: GCC's HFAs (`aapcs_vfp_sub_candidate`: unions count their largest member,
  zero-width bitfields and empty structs are ignored, a zero-length array disqualifies, and an
  `aligned` attribute doesn't matter) are `struct<C>` of their floats read from the object's
  bytes; other composites of up to 16 bytes are their scalars at their offsets, unions and
  bitfield storage as bytes, with `array<0 x i128>` exactly when GCC's argument alignment (the
  fields', `aarch64_function_arg_alignment`; not the type's `aligned` attribute) is 16; larger
  ones their memory type (by reference), or their bytes when that holds an empty struct or a
  zero-length array. Empty structs (a GNU extension, rejected before) are `struct<C>{}` of size 0
  in memory and nothing as arguments, left out of variadic calls and read as nothing by
  `va_arg`, as GCC does. A function that falls off its end returns the leaves of a fresh object
  (`poison`), since FIR has no aggregate `poison`.
- **Rejected with a located diagnostic** (`tests/errors/struct_by_value.c`): an HFA GCC aligns
  to 16 (`_Alignas(16) double`: GCC aligns it to 16 on the stack, FIR's HFAs keep their floats'
  alignment); 16-byte aligned composites and floats beside a zero-length array through `...`
  (FIR's variadic composites have no zero-length arrays, which carry those); structs holding a
  `va_list` (its bytes would lose the cursor); returning a `va_list`.
- **Tests:** seven new corpus programs (67 in all): `struct_classes` (every class as parameter
  and result: HFAs of 1 to 4 `float`s and `double`s through arrays, nesting, a union, an
  `aligned` attribute, and a zero-width bitfield; 1 to 16 bytes with padding; floats with
  integers; a 16-byte aligned member (an even register pair) and an `aligned(16)` struct (not
  one); pointers, arrays, bitfields, unions, empty structs, a flexible array member, a
  zero-length array; 24- and 96-byte structs by reference, the callee's copy its own; more
  arguments than registers of each class), `struct_calls` (`f().x`, `g(f())`, chains, `?:` and
  `,` of calls, assignment chains, results in loops, recursion, a function falling off its end,
  `goto` and `switch` functions returning structs, function pointers in arrays and structs, every
  class through `...` past the registers, empty structs through `...`, `va_copy` and a callee
  taking a `va_list` reading structs), `vec3` (vectors as HFAs, 3x3 matrices by reference,
  rotations, an inverse, Gram-Schmidt, a ray caster), `complex_math` (complex numbers as HFAs:
  powers, a Julia set, a 16-point FFT and its inverse, Newton's method), `rational` (a rational
  library on 16-byte structs: series, continued fractions, Egyptian fractions, exact Gaussian
  elimination, a 24-byte result struct), `geometry` (segment intersection, bounding boxes, a
  convex hull returned in a 516-byte struct, area and centroid, closest pair), and
  `struct_extern`, whose `tests/extern/struct_extern.c` the reference compiler compiles (the
  harness now links a program's `tests/extern/NAME.c` into all three builds): calls of every
  class into GCC's code directly, through pointers, and through `...` past the registers, GCC's
  code calling back directly, through pointers, and variadically, and libc's `div`, `ldiv`,
  `lldiv`. All 67 match the reference natively without and with `-O`; 57 match in `fir run`
  (`struct_extern` joins the 9 that call other external functions); 13 error tests. A one-off
  run of the corpus compiled by Clang 23 (`-O1 -ffp-contract=off` for AArch64, glibc's headers,
  GCC's linker) printed what GCC's binaries print for all 67.
- **ABI torture** (`fai_cc_abi_torture` in `crates/fir-capi/tests/fai_cc.rs`): random C
  signatures (up to 14 parameters and a result; structs and unions of every scalar type, arrays,
  nesting, bitfields with zero-width ones, HFA candidates through arrays, nesting, and unions,
  `_Alignas(16)` members, `aligned(8)` and `aligned(16)` attributes, empty structs, pointers)
  in a callers file and a callees file, each compiled by GCC, `fai-cc`, or `fai-cc -O`; six
  pairings (gcc/gcc, fai/gcc, fai -O/gcc, gcc/fai, gcc/fai -O, fai/fai -O) must each find every
  member of every argument (direct, through a function pointer, and through `...` by `va_arg`)
  and of every result. 240 signatures by default (about 1,150 parameters, 12,000 members per
  pairing, 5 seconds); 20 seeds of 1,000 signatures each passed: 129,258 record types (61,734
  of floats only, 21,344 unions, 18,387 with bitfields, 15,641 aligned, 6,984 empty), 93,565
  parameters (88,454 also through `...`), 1,002,704 members checked in each pairing. It found
  that a large struct holding an empty struct used its memory type, which FIR can't pass through
  `...` (now its bytes). Mutations of the mapping (the type's alignment instead of the fields',
  a union never an HFA, zero-width bitfields not ignored) each fail it.
- **API:** none needed: version 1.5's composite signatures, `mem.load`/`mem.store` of a struct
  type, calls, `func.ret`, and `va.arg` of a composite were enough.
- **API and IR friction:** FIR can't express a 16-byte aligned HFA (an alignment marker is a
  zero-length array, which makes it not an HFA), nor a 16-byte aligned composite through `...`
  (variadic composites have no zero-length arrays); a richer alignment on `struct<C>` would
  cover both. FIR has no unions among composite values, so a union travels as an HFA's floats or
  its bytes, and its pointers as exposed bytes. A call result needs a temporary in memory (there
  are no aggregate locals in registers until mem2reg). Two `fai-cc` objects with string literals
  don't link together (the generated `str.N` names; no linkage yet), so the torture's callees
  avoid them.
- **Not yet:** the rejections above; `long double`, `_Complex`, and the other gaps track F2a
  and F2b list.

## Round status

Against "Done when", item by item:

- **A corpus of C programs compiled by `fai-cc` to AArch64 binaries:** met. 67 programs: integers
  (`arith_*`, `bigint`, `bit_tricks`, `number_theory`, …), pointers (`pointers`, `linked_list`,
  `bst`, `pointer_int_casts`), structs (`structs`, `aggregates`, `layouts`, `bitfields`), unions
  (`unions`, `struct_classes`), arrays (`arrays`, `matrix`, `sieve`), globals (`globals`,
  `initializers`), string literals (`chars_strings`, `string_routines`), every statement form
  including `goto` and `switch` (`goto`, `switches`, `duff`, `state_machine`, `loops`), function
  pointers (`function_pointers`, `struct_calls`), `float`/`double` (`float_*`, `newton`,
  `mandelbrot`, `integration`, `vec3`, `complex_math`), variadic functions defined and called
  (`varargs`, `varargs_printf`, `struct_calls`), structs passed and returned by value
  (`struct_classes`, `struct_calls`, `struct_extern`, `vec3`, `complex_math`, `rational`,
  `geometry`), and calls to libc including `printf` (`libc_calls`, `printf_*`, `struct_extern`).
- **Output matching the same programs compiled by clang, under `qemu-aarch64` on Linux:** met,
  with one substitution: the harness's reference compiler is the dev shell's AArch64 GCC (16.2,
  decision C frontend testing), and all 67 match it without and with `-O`. Clang compiled the
  same 67 for AArch64 once (by hand, not in the harness), and its binaries print what GCC's
  print, so `fai-cc`'s match Clang's too.
- **Natively on AArch64:** not run here (the host is x86-64); the harness runs the binaries
  directly when it is on AArch64.
- **Each program's HFIR also runs in `fir run` with the same output where its run is defined:**
  met for 57 of 67. The other 10 call external functions whose results the interpreter's world
  answers with zeros (`printf`, `vsnprintf`, `strlen`, and `struct_extern`'s GCC-compiled
  helpers), so their runs aren't comparable and are listed, not compared.

## Not in this round

- Proofs beyond the float semantics and the purity of the new pure ops: scalarizing, lowering
  `cf.try`, composing rewrites, and the trust round's checkers stay open.
- `f16`/`bf16`, vectors, fast-math modifiers, rounding modes, `long double` beyond `double`
  (AAPCS64's `long double` is 128-bit; `fai-cc` rejects it), `_Complex`, atomics, threads,
  `volatile`, `setjmp`/`longjmp`, VLAs, inline assembly, and macOS binaries.
