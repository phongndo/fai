# fai-cc: a C compiler on FIR

`fai-cc` compiles C to AArch64 Linux binaries through FIR. Clang parses and type-checks the C
(preprocessor and system headers included) for `aarch64-unknown-linux-gnu`, so sizes, layouts, and
`char`'s signedness (unsigned) are the target's. `fai-cc` lowers Clang's AST to HFIR through FIR's
C API only (`crates/fir-capi/include/fir.h`), verifies it, compiles it with `fir_module_compile`
(which lowers HFIR to MFIR, and runs the proved passes with `-O`), and links it with the AArch64 C
compiler, as `fir compile` does.

```
fai-cc FILE.c [-O] [-o OUT] [--emit hfir|mfir|asm] [INPUT...] [-I DIR] [-D NAME[=V]]
       [-l LIB] [-L DIR] [-- CLANG-FLAG...]
```

- Without `--emit`, `OUT` (default `a.out`) is an executable; an object file if it ends in `.o`;
  assembly if it ends in `.s`. More `INPUT`s (objects, archives, C or assembly files) and `-l`/`-L`
  go to the linker.
- `--emit hfir` prints the HFIR as lowered, `--emit mfir` the MFIR (optimized with `-O`), and
  `--emit asm` the assembly, to `OUT` or standard output.
- `-I`, `-D`, `-U`, and `-std=` go to Clang, and so does everything after `--`.
- The linker is `$FIR_CC`, or `cc` on an AArch64 host and `aarch64-unknown-linux-gnu-cc` (the dev
  shell's cross compiler) elsewhere. Clang gets that compiler's system include directories after
  its own headers (Clang's resource directory, found when `fai-cc` is built, or
  `$FAI_CC_RESOURCE_DIR`).
- Unsupported C is an error with its source location (`file.c:3:7: error: fai-cc does not support
  variable-length arrays yet`), and nothing is written; `fai-cc` exits with 1. `FAI_CC_DUMP=1` prints
  the module when the HFIR doesn't verify (a bug in `fai-cc`).

## Build

From the repository root, in the dev shell (`nix develop`, which provides CMake, Ninja, and Clang's
and LLVM's libraries on `CMAKE_PREFIX_PATH`):

```sh
cmake -S frontends/c -B build/fai-cc -G Ninja
cmake --build build/fai-cc            # also runs `cargo build --release -p fir-capi`
build/fai-cc/fai-cc hello.c frontends/c/tests/runtime/fai_runtime.c -I frontends/c/tests/runtime -o hello
qemu-aarch64 hello                    # natively on AArch64 Linux
```

`-DFIR_CAPI_LIB=…/libfir_capi.a -DFAI_CC_BUILD_CAPI=OFF` links a static library built elsewhere.
The C++ is warning-free under `-Wall -Wextra -Werror` and formatted by `clang-format` (`.clang-format`
here; `clang-format --dry-run -Werror frontends/c/src/*`).

## Tests

```sh
cargo test --release -p fir-capi --test fai_cc -- --nocapture
```

builds `fai-cc` with CMake (against the static library of the current sources), then:

- compiles every program in `tests/*.c` with the reference compiler (`aarch64-unknown-linux-gnu-cc
  -O1 -ffp-contract=off`, or `$FIR_CC`), with `fai-cc`, and with `fai-cc -O`, links each with
  `tests/runtime/fai_runtime.c` and libm (`-lm`), runs them (under `qemu-aarch64` off AArch64), and
  requires the same output and exit code;
- runs each program's HFIR in FIR's interpreter under Arm's NaN choice (`NanRule::Arm`, the NaNs
  the hardware gives): the calls of the output helpers (events) must spell the same output and
  `main` must return the same code. Programs that call other external functions (libc, libm) can't
  be compared there and are listed;
- checks that each program in `tests/errors/` gets exactly the diagnostics its `// expect: LINE:COL:
  TEXT` lines name, and exit code 1.

It runs by default on Linux; on macOS (whose binaries aren't Linux ones) only with `FAI_CC_TESTS=1`
(given a Linux AArch64 toolchain in `FIR_CC` and a way to run its binaries), and `FAI_CC_TESTS=0`
turns it off. Missing tools are a failure that names them, not a skip. `FAI_CC_ONLY=name` runs only
the programs whose names contain `name`.

The corpus prints through `tests/runtime/fai_test.h` (`fai_put_long`, `fai_put_char`, and helpers
written in C on top of them: `show_d` and `show_f` print a float's exact bits in hexadecimal and a
rounded decimal), since `printf` needs varargs (track V). Its programs must not have undefined
behavior: UB allows the three builds to differ. Nor may their output depend on what C leaves
unspecified: which NaN's payload an operation on two different NaNs keeps (the reference compiler
commutes `+` and `*`), or whether a signaling NaN is quieted by an operation the reference compiler
folds away (`x * 1.0`). Float inputs live in non-constant globals, so the reference compiler can't
fold libm calls with its own correctly rounded arithmetic.

## What is supported

The integer, float, pointer, aggregate-in-memory, and control-flow subset of C11 (with common GNU
extensions Clang accepts, such as case ranges and `__extension__`):

- **Types:** `_Bool` (`i8` holding 0 or 1: FIR's `i1` takes no bytes in memory), `char` (unsigned),
  `short`, `int`, `long`, `long long`, their signed and unsigned forms, enums, `float` and `double`
  (`f32` and `f64`), pointers, arrays
  (multidimensional, flexible array members), structs, unions, bitfields, typedefs, `const`.
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

Every local and parameter is a `mem.stack.of` slot made at the function's entry (mem2reg comes
later), so values never cross blocks. Statements are structured where C's are (`cf.if`, `cf.loop`;
`continue` repeats a `for` loop's step or a `do` loop's test); a `switch` is a `cf.blocks` whose entry
`cf.switch`es to one block per case group, with fall-through as `cf.br`; a function with `goto` or
labels, or with a `switch` whose cases are inside other statements, is one `cf.blocks` of basic
blocks. Every op carries its C construct's `@line:col` (the expansion location for macros), and
every function its file.

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
  formats (`_Float16`, `__fp16`, `__bf16`, `_Float128`); variadic functions, defined or called, so
  `printf` (track V); structs and unions passed or returned by value (track A).
- `<math.h>`'s `isgreater` family, which glibc defines with statement expressions under Clang (the
  `__builtin_isgreater` forms work); float builtins without a FIR op (`__builtin_fmin`, …);
  `#pragma STDC FENV_ACCESS`: FIR's floats round to nearest and have no exception flags, so a
  program that changes the rounding mode (`fesetround`) or tests the flags isn't modeled (the
  pragma isn't diagnosed).
- Integers over 64 bits (`__int128`, `_BitInt`), `volatile`, `_Atomic`, variable-length arrays,
  packed structs, alignments above 16, thread-local variables, inline assembly, statement
  expressions, labels as values, `++`/`--` on `_Bool`, wide string literals, calls with arguments
  through declarations without prototypes, old-style (K&R) definitions.
- Variables defined in another file (`extern int x;`, libc's `stdout` and `errno`): FIR has no
  external globals.
- Global initializers that point inside an object (`&table[2]`, `"abc" + 1`), or that store an
  address as an integer: FIR's initializers name only the start of a global.

Also: C's `static` functions and globals become global symbols (FIR has no linkage yet), so a
program can't define a `static` function with a libc function's name; the generated names (`str.0`,
`zero.1`, `f.counter` for a static local) contain a `.`, so they can't clash with C names.
