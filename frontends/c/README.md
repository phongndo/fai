# fcc: a C compiler on FIR

`fcc` compiles C to AArch64 Linux binaries through FIR, and, for the integer subset, to x86-64
Linux binaries (`--target x86_64`, below). Clang parses and type-checks the C (preprocessor and
system headers included) for `aarch64-unknown-linux-gnu` (or `x86_64-unknown-linux-gnu`), so
sizes, layouts, and `char`'s signedness (unsigned on AArch64, signed on x86-64) are the target's.
`fcc` lowers Clang's AST to HFIR through FIR's C API only (`sdk/c/include/fir.h`),
verifies it, compiles it with `fir_module_compile` (which lowers HFIR to MFIR, and runs the proved
passes with `-O`), and links it with the target's C compiler, as `fir compile` does.

`fcc` was called `fai-cc` until it was renamed: the binary, the CMake project and target, and the
usual build directory (`build/fcc`) are now `fcc`; the environment variables `FAI_CC_*` are now
`FCC_*` (`FCC_TESTS`, `FCC_ONLY`, `FCC_PASSES`, `FCC_ABI`, `FCC_ABI_SEED`, `FCC_DUMP`,
`FCC_RESOURCE_DIR`, `FCC_BUILD_CAPI`); the tests are `cargo test -p fir-capi --test fcc`
(`fcc_corpus`, `fcc_abi_torture`, whose evidence `fai verify` reads as `fcc_corpus`); and
`benchmarks/c/bench.py` reads `BENCH_FCC`. Older commits and logs say `fai-cc`. The project-wide `fai_`
names (the test runtime `fai_runtime.c`, its `fai_put_*` helpers, the C++ `namespace fai`) are
the project's, not the compiler's, and keep their names.

```
fcc FILE.c [-O [--check-dce FIR-REF] | --passes P,... [--experimental]] [-o OUT]
       [--emit hfir|mfir|asm] [--target aarch64|x86_64] [INPUT...] [-I DIR] [-D NAME[=V]]
       [-l LIB] [-L DIR] [-- CLANG-FLAG...]
```

- Without `--emit`, `OUT` (default `a.out`) is an executable; an object file if it ends in `.o`;
  assembly if it ends in `.s`. More `INPUT`s (objects, archives, C or assembly files) and `-l`/`-L`
  go to the linker.
- `--emit hfir` prints the HFIR as lowered, `--emit mfir` the MFIR (optimized with `-O` or
  `--passes`), and `--emit asm` the assembly, to `OUT` or standard output.
- `--passes P,...` runs the named passes on the MFIR, in order to a fixed point, instead of `-O`'s.
  Experimental (unproved) passes run only with `--experimental`, which prints a warning: the
  promotion pipeline is `--passes mem2reg,stackdce,fwd,copyprop,dse,dce --experimental` (see
  [docs/design/05-optimizing-c.md](../../docs/design/05-optimizing-c.md)).
- `-I`, `-D`, `-U`, and `-std=` go to Clang, and so does everything after `--`.
- `--check-dce FIR-REF` (with `-O`, or `--passes`) has every step of dead code elimination
  checked by the proved Lean checker (`FIR-REF` is `spec/.lake/build/bin/fir-ref`; see
  `docs/assurance/dce.md`): a refusal fails the compilation, and one line
  (`fir: check-dce: N steps accepted by Fir.Dce.checkModule (…)`) goes to stderr. The corpus tests
  build each program's `-O` binary this way, for AArch64 and for x86-64 (both corpora are
  required in `fai verify full` on Linux; the ABI torture test's `-O` builds are not
  checked), and the `FCC_PASSES` build too when it is set. Without the flag, every step's
  output is still checked, by an unproved Rust transcription of the same checker.
- `--target` picks the target: `aarch64` (the default) or `x86_64`. `-O`, `--passes`, and
  `--check-dce` run on the MFIR, before the target is involved, so they mean the same for both.
- The linker is `$FIR_CC`, or `cc` when the host is the target (its CPU, on Linux; macOS's `cc`
  makes Mach-O, so there `$FIR_CC` names a Linux cross compiler), else the target's cross compiler
  (`aarch64-unknown-linux-gnu-cc`, which the dev shell has on x86-64 Linux, or
  `x86_64-unknown-linux-gnu-cc`, which it has on other Linux hosts). Clang gets that compiler's
  system include directories after its own headers (Clang's resource directory, found when
  `fcc` is built, or `$FCC_RESOURCE_DIR`).
- Unsupported C is an error with its source location (`file.c:3:7: error: fcc does not support
  variable-length arrays yet`), and nothing is written; `fcc` exits with 1. `FCC_DUMP=1` prints
  the module when the HFIR doesn't verify (a bug in `fcc`).

## Build

From the repository root, in the dev shell (`nix develop`, which provides CMake, Ninja, and Clang's
and LLVM's libraries on `CMAKE_PREFIX_PATH`):

```sh
cmake -S frontends/c -B build/fcc -G Ninja
cmake --build build/fcc            # also runs `cargo build --release -p fir-capi`
build/fcc/fcc hello.c frontends/c/tests/runtime/fai_runtime.c -I frontends/c/tests/runtime -o hello
qemu-aarch64 hello                    # natively on AArch64 Linux
```

`-DFIR_CAPI_LIB=…/libfir_capi.a -DFCC_BUILD_CAPI=OFF` links a static library built elsewhere.
The C++ is warning-free under `-Wall -Wextra -Werror` and formatted by `clang-format` (`.clang-format`
here; `clang-format --dry-run -Werror frontends/c/src/*`).

## Tests

```sh
cargo test --release -p fir-capi --test fcc -- --nocapture
```

builds `fcc` with CMake (against the static library of the current sources), then:

- compiles every program in `tests/*.c` with the reference compiler (`aarch64-unknown-linux-gnu-cc
  -O1 -ffp-contract=off`, or `$FIR_CC`), with `fcc`, and with `fcc -O`, links each with
  `tests/runtime/fai_runtime.c`, libm (`-lm`), and, if the program has one, `tests/extern/NAME.c`
  compiled by the reference compiler (C functions it calls and that call it back, compiled
  separately), runs them (under `qemu-aarch64` off AArch64), and requires the same output and exit
  code;
- runs each program's HFIR in FIR's interpreter under Arm's NaN choice (`NanRule::Arm`, the NaNs
  the hardware gives): the calls of the output helpers (events) must spell the same output and
  `main` must return the same code. Programs that call other external functions (libc's `printf`,
  libm) can't be compared there, since the interpreter's world answers them with zeros: they are
  listed with the first such function they call;
- checks that each program in `tests/errors/` gets exactly the diagnostics its `// expect: LINE:COL:
  TEXT` lines name, and exit code 1;
- runs the ABI torture (`fcc_abi_torture`): random signatures of structs and unions (HFAs
  through arrays, nesting, and unions, small and large composites, bitfields, 16-byte aligned
  members and `aligned` attributes, empty structs, pointers, more arguments than registers) as
  two C files, callers and callees, each compiled by `fcc`, `fcc -O`, or the reference
  compiler; in every pairing the callees check each member they receive (directly, through a
  function pointer, and through `...` by `va_arg`) and the callers each member of each result.
  `FCC_ABI=N` sets the number of signatures (240 by default), `FCC_ABI_SEED` the seed.

`FCC_PASSES=p,q,…` adds a fourth build, `fcc --passes p,q,… --experimental`, which must
match the reference too, and runs the MFIR and allocated LFIR it makes in the interpreter.
[`benchmarks/c/`](../../benchmarks/c/) measures what each pipeline executes (instructions, loads,
stores) against GCC's, and `benchmarks/c/cbench.py` is the end-to-end baseline against GCC and Clang (behavior, executed
instructions, code size, compile time, and wall time measured on native AArch64 only; results
in [`docs/performance/c-baseline.md`](../../docs/performance/c-baseline.md)).

It runs by default on Linux; on macOS (whose binaries aren't Linux ones) only with `FCC_TESTS=1`
(given a Linux AArch64 toolchain in `FIR_CC` and a way to run its binaries), and `FCC_TESTS=0`
turns it off. Missing tools are a failure that names them, not a skip. `FCC_ONLY=name` runs only
the programs whose names contain `name`.

Most of the corpus prints through `tests/runtime/fai_test.h` (`fai_put_long`, `fai_put_char`, and
helpers written in C on top of them: `show_d` and `show_f` print a float's exact bits in hexadecimal
and a rounded decimal), so the interpreter's run is compared too; the `printf_*` programs and a few
others print with `printf`, and run only natively. Variadic functions defined in C that print
through the helpers (`varargs.c`) are compared in the interpreter as well. A program never prints an
address (`%p` goes into a buffer that is checked). Its programs must not have undefined behavior: UB
allows the three builds to differ. Nor may their output depend on what C leaves unspecified: which
NaN's payload an operation on two different NaNs keeps (the reference compiler commutes `+` and
`*`), or whether a signaling NaN is quieted by an operation the reference compiler folds away
(`x * 1.0`). Float inputs live in non-constant globals, so the reference compiler can't fold libm
calls with its own correctly rounded arithmetic.

## x86-64

`fcc --target x86_64` compiles the integer subset for x86-64 Linux, through FIR's x86-64 backend
(decision: x86-64 target): everything above except floats, variadic functions defined in C (calls
of `printf` and other variadic functions work), and structs and unions by value, which are
errors at the program level, as is passing a `char`, `short`, or `_Bool` to a function defined
elsewhere (C callees on x86-64 expect such arguments extended by their signedness, which FIR's
signatures don't record yet; pass an `int`). `long double` is x87's 80-bit format there, and
rejected.

```sh
build/fcc/fcc --target x86_64 prog.c frontends/c/tests/runtime/fai_runtime.c \
  -I frontends/c/tests/runtime -D FAI_TEST_INTEGERS_ONLY -o prog
./prog
```

`-D FAI_TEST_INTEGERS_ONLY` leaves `fai_test.h`'s float helpers out: `fcc` compiles every
function a file defines, used or not. `cargo test -p fir-capi --test fcc fcc_x86_64_corpus`
compiles the corpus this way and checks each program against the x86-64 reference compiler (the
dev shell's Clang at `-O1`, or `$FIR_CC_X86_64`), natively, with and without `-O` (the `-O`
builds with `--check-dce`, as for AArch64), with `FCC_PASSES`'s passes when it is set, and its
x86-64 HFIR in `fir run`; a program the backend refuses must be refused for one of the limitations
above. It runs on x86-64 Linux, or elsewhere with `x86_64-unknown-linux-gnu-cc` and
`qemu-x86_64`.

## What is supported

The integer, float, pointer, aggregate-in-memory, and control-flow subset of C11 (with common GNU
extensions Clang accepts, such as case ranges and `__extension__`):

- **Types:** `_Bool` (`i8` holding 0 or 1: FIR's `i1` takes no bytes in memory), `char` (unsigned),
  `short`, `int`, `long`, `long long`, their signed and unsigned forms, enums, `float` and `double`
  (`f32` and `f64`), pointers, arrays
  (multidimensional, flexible array members), structs, unions, bitfields, empty structs and unions
  (a GNU extension: size 0), typedefs, `const`.
- **Expressions:** all arithmetic, bitwise, shift, comparison, and logical operators; compound
  assignment; increment and decrement; `&&`, `||`, `?:` (short-circuiting, as `cf.if`); casts;
  pointer arithmetic, differences, and comparisons; `&`, `*`, `.`, `->`, `[]`; `sizeof` and
  `_Alignof` (Clang evaluates them); string literals; compound literals and brace and designated
  initializers, local and global; struct and union assignment; the comma operator; direct and
  indirect calls. On floats: literals (their exact bits), `+ - * /`, unary minus, comparisons,
  `!` and conditions, compound assignment, `++`/`--`, the usual arithmetic conversions, and casts
  to and from every integer type and between `float` and `double`.
- **Statements:** all of them, including `goto`, labels, `switch` with fall-through (and Duff's
  device), `static` locals, and file-scope globals whose initializers hold integers, floats,
  strings, and the addresses of globals and functions.
- **Functions:** definitions, prototypes, recursion, function pointers; calls to functions defined
  elsewhere (libc, libm) as FIR external functions that may do anything; `malloc` and `free` as
  FIR's `c.malloc` heap allocations; `main` returns 0 when it falls off its end.
- **Structs and unions by value** as AAPCS64 and GCC pass them: parameters and results of
  functions defined here or elsewhere (libc's `div` and `ldiv`, functions compiled by GCC), direct
  and indirect calls, variadic arguments and `va_arg`, `return s;`, and call results used in
  expressions (`f().x`, `f().a[i]`, `g(f())`, `s = f()`, `c ? f() : g()`). Every class works:
  HFAs of one to four `float`s or `double`s (through arrays, nested structs, and unions), small
  composites with padding and bitfields, 16-byte aligned ones, larger ones by reference, unions,
  and empty structs (no argument at all, as GCC's C does).
- **Varargs:** variadic functions defined here (`int sum(int n, ...)`, and C23's `f(...)`) and
  elsewhere (`printf`, `snprintf`, `sprintf`, `fprintf`, `vprintf`, `vsnprintf`, `vfprintf`, …),
  called directly or through pointers, with C's default argument promotions (`float` to `double`,
  narrower integers to `int`, as Clang inserts them); `<stdarg.h>`: `va_start`, `va_arg` of every
  scalar type, `va_end`, `va_copy`; a `va_list` as a local, a global, a struct field, an array
  element, a parameter (passed by value), or through a pointer.
- **Float builtins** with a FIR op: the constants (`__builtin_inf`, `__builtin_huge_val`,
  `__builtin_nan("…")`, `__builtin_nans`, and their `f` forms, which `<math.h>`'s `INFINITY`,
  `HUGE_VAL`, and `NAN` expand to), `__builtin_fabs`, `__builtin_sqrt`, `__builtin_copysign`,
  `__builtin_fma` (and `f` forms), the classifications `<math.h>`'s macros use (`isnan`, `isinf`,
  `isfinite`, `isnormal`, `signbit`, `fpclassify`, `__builtin_isinf_sign`), and the quiet
  comparisons (`__builtin_isgreater` and friends). The library functions (`sqrt`, `fabs`, …) stay
  calls of libm, which may set `errno`.

## How C maps to FIR

Each C rule is an explicit FIR modifier: signed `+ - *` are `.nsw` (overflow is UB in C, and
`poison` refines it), unsigned ones `.wrap`; `/` and `%` are `int.div.s.ub`/`int.rem.s.ub` (and `.u`
for unsigned); shifts are `.ub` (by at least the width, or negative); conversions truncate with
`.wrap` and extend by the source's signedness; integer↔pointer casts are `ptr.expose` and
`ptr.from_exposed`; pointer arithmetic is `ptr.index.inbounds`, and a pointer difference is a
difference of `ptr.addr`s divided exactly.

Floats are strict IEEE 754, one FIR op per C operator: `+ - * /` are `float.add` and friends, never
contracted (`a * b + c` is a `float.mul` and a `float.add`, as `-ffp-contract=off`; only `fma` and
`__builtin_fma` fuse), unary minus is `float.neg`; `<`, `<=`, `>`, `>=`, `==` are the ordered
`float.cmp.olt` … `oeq` (false on NaN) and `!=` is `une` (true on NaN); a float's truth (`!x`,
conditions, `&&`, conversion to `_Bool`) is `float.cmp.une` against 0.0. A float converts to an
integer with `float.to_int.s.ub`/`.u.ub` (C's NaN or out-of-range conversion is UB), an integer to
a float with `int.to_float` (rounded to nearest, ties to even; a constant integer converts to the
same rounded constant at compile time), `float` to `double` with `float.ext`, and back with
`float.trunc`. Literals and global initializers are Clang's exact bits (`float.const`,
`fir_init_f32`/`fir_init_f64`). `float` stays `float` (`FLT_EVAL_METHOD` is 0 on AArch64), and
parameters and results follow AAPCS64 through FIR's calling convention.

A function with `...` is a variadic FIR function (`func @sum(%n: i32, ...)`), one defined elsewhere
a variadic external function, and a pointer to one has a variadic signature
(`func.call.indirect func<(ptr, ...) -> i32>`); a call passes the variadic arguments as Clang
promoted them (`i32`, `i64`, `ptr`, `f64`). `va_list` is, on AArch64 Linux, the struct `__va_list`
(AAPCS64's five fields; not an array, as on x86-64), and FIR's `va_list` memory type, whose layout
is checked against Clang's: so `va_list` objects are `mem.stack.of va_list`, `va_start` is
`va.start`, `va_arg(ap, T)` `va.arg` of T's FIR type, `va_end` `va.end`, and `va_copy` (and
assigning a `va_list`) `mem.copy va_list`. A `va_list` parameter is a `ptr`: AAPCS64 passes a
composite larger than 16 bytes as the address of a copy the caller makes and the callee owns, so a
call copies the argument into a `mem.stack.of va_list` of its own and passes that, and the callee
uses the pointer as its parameter's object; this is the ABI libc's `vprintf` expects.

Every local and parameter is a `mem.stack.of` slot made at the function's entry (the
experimental `mem2reg` pass promotes the ones that don't escape, with `--passes`), so values never cross blocks. Statements are structured where C's are (`cf.if`, `cf.loop`;
`continue` repeats a `for` loop's step or a `do` loop's test); a `switch` is a `cf.blocks` whose entry
`cf.switch`es to one block per case group, with fall-through as `cf.br`; a function with `goto` or
labels, or with a `switch` whose cases are inside other statements, is one `cf.blocks` of basic
blocks. Every op carries its C construct's `@line:col` (the expansion location for macros), and
every function its file.

A struct or union passed by value (a parameter, a result, a variadic argument, or `va_arg`'s) is a
FIR composite value that `mem.load` reads from the C object where it is sent and `mem.store` writes
into one where it arrives; a call's or `va_arg`'s result goes into a temporary object made at the
function's entry, whose address the expression then is (so `f().x` is a member access, and `?:`
can choose between two calls' results). FIR classifies composites by AAPCS64 (decision C ABI for
aggregates); the value's type is chosen so that the class is the one GCC gives the C type, which
differs from what the memory type would get in a few places:

- an HFA by GCC's rule (one to four `float`s or `double`s through members, arrays, and unions,
  no padding, no zero-length array; zero-width bitfields and empty structs don't count) is a
  `struct<C>` of its floats, read from the object's bytes, so a union of floats, or an HFA with an
  `aligned` attribute, is one too;
- another composite of at most 16 bytes is its scalars at their offsets, unions and bitfield
  storage as bytes, with a leading `array<0 x i128>` exactly when GCC aligns the argument to 16:
  GCC takes the largest of the fields' alignments (`_Alignas(16)` on a member counts, an `aligned`
  attribute on the struct itself doesn't), not the type's;
- a larger one, which travels by reference, is its memory type, or its bytes when that type has
  an empty struct or a zero-length array in it, which a variadic C composite can't;
- an empty struct is `struct<C>{}`, which takes no register and no stack; through `...` it is
  left out, and `va_arg` of one reads nothing, as with GCC.

A struct is `struct<C>{…}` with its members in order; the bytes of bitfields and any gap are
`array<k x i8>` padding (explicit for bitfields even where FIR's alignment would leave the bytes
implicit, so a global's initializer can set them), and a struct Clang aligns more than its members (bitfields, `_Alignas`)
starts with an `array<0 x iN>` that carries the alignment. A union is a struct of its size and
alignment, read and written through pointers. Every struct's size, alignment, and member offsets
are checked against Clang's `ASTRecordLayout` with `fir_type_layout` and `fir_type_field_offset`;
a mismatch is a loud internal error. Bitfields are read and written a byte at a time over the bytes
they span (bytes shared with neighbors are frozen and written back unchanged).

Struct copies are `mem.copy` (exact, padding and pointers included); a zeroed local aggregate is
copied from a constant zero global, then its named members stored; a `char` array initialized by a
string is copied from a constant global. `char` loads and stores are `i8`: by the decision Pointer
bytes as integers an `i8` load of pointer bytes exposes the pointer and a later pointer load of
those bytes gets it back, so C's byte copies stay defined (FIR's `b8` would keep provenance
exactly, but has no conversion to integers for C to compute with).

## Not supported yet

Each is diagnosed where it appears:

- `long double` (binary128 on AArch64, which FIR doesn't have), `_Complex`, and the other float
  formats (`_Float16`, `__fp16`, `__bf16`, `_Float128`), so also `printf("%Lf", …)`; and a
  `va_list` returned by value.
- Structs and unions by value that FIR can't pass as GCC does: an HFA whose members GCC aligns to
  16 (`_Alignas(16) double`), which GCC puts on the stack 16-byte aligned while FIR's HFAs keep
  their floats' alignment; through `...` (as variadic arguments or `va_arg` types), a 16-byte
  aligned composite, or floats beside a zero-length array, since FIR's variadic composites have
  no alignment marker or zero-length array; and a struct holding a `va_list` (its bytes would
  lose the cursor).
- `<math.h>`'s `isgreater` family, which glibc defines with statement expressions under Clang (the
  `__builtin_isgreater` forms work); float builtins without a FIR op (`__builtin_fmin`, …);
  `#pragma STDC FENV_ACCESS`: FIR's floats round to nearest and have no exception flags, so a
  program that changes the rounding mode (`fesetround`) or tests the flags isn't modeled (the
  pragma isn't diagnosed).
- Integers over 64 bits (`__int128`, `_BitInt`), `volatile`, `_Atomic`, variable-length arrays,
  packed structs, alignments above 16, thread-local variables, inline assembly, statement
  expressions, labels as values, `++`/`--` on `_Bool`, wide string literals, calls with arguments
  through declarations without prototypes, old-style (K&R) definitions.
- Variables defined in another file (`extern int x;`, libc's `stdout`, `stderr`, and `errno`): FIR
  has no external globals, so `fprintf` and `vfprintf` work on streams the program opens
  (`fopen`, `fmemopen`, `fdopen`) but not on `stdout` and `stderr`.
- Global initializers that point inside an object (`&table[2]`, `"abc" + 1`), or that store an
  address as an integer: FIR's initializers name only the start of a global.

Also: C's `static` functions and globals become global symbols (FIR has no linkage yet), so a
program can't define a `static` function with a libc function's name; the generated names (`str.0`,
`zero.1`, `f.counter` for a static local) contain a `.`, so they can't clash with C names, but they
clash between two objects `fcc` compiled (two files with string literals don't link together).
