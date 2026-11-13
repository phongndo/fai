# Optimizing C: promotion first (experimental)

`fcc` gives every C local and parameter a stack slot at the function's entry, and `-O`'s
passes (`fwd`, `copyprop`, `dse`, `dce`) match only adjacent accesses, so on C they do almost
nothing: the layer audit found one change in a whole module ([layer-audit.md](../assurance/layer-audit.md),
section 2). This note records a prototype of the missing piece, promoting slots to values, what
it buys on the C corpus, what it doesn't do yet, what its correctness rests on, and what the
measurements say to do next. Everything here is opt-in and unproved: it never runs under `-O`.

## Summary

- **`mem2reg`** (experimental) promotes a slot whose every use is the address of a load or store,
  directly or through `ptr.offset`s by constants, field by field (scalar replacement of C
  structs and promotion in one step), threading values through `cf.if` results, loop state, and
  block parameters where they are live. **`stackdce`** (experimental) deletes the allocations
  it leaves.
- On the 67 corpus programs, against `fcc -O`, with every build's output identical to GCC's:
  loads executed **−95%**, stores **−92%**, instructions executed **−32%** (geometric mean of the
  per-program ratios ×0.845), code size ×0.85; 79% of MFIR stack slots go away.
- Memory traffic is now within ~4× of GCC `-O1`'s, and is 3% of what runs. The remaining
  instruction gap to GCC (3.8×) is in instruction selection and register allocation: constants
  rebuilt where they're used, inside loops (30% of what runs), register copies, compare-and-branch
  sequences, and repeated extensions.
- Correctness: differential tests against the interpreter (≈60k program runs, ≈12k of them also
  native), the C corpus natively and at every layer in the interpreter, and the native AArch64
  suite. Assumptions are listed below; the only one beyond the existing passes' is
  `stackdce`'s, that allocation numbers aren't observable.

## How to try it

```sh
fcc prog.c --passes mem2reg,stackdce,fwd,copyprop,dse,dce --experimental -o prog
fcc prog.c --passes mem2reg,stackdce,fwd,copyprop,dse,dce --experimental --emit mfir
fir opt prog.mfir --passes mem2reg,copyprop,dce --experimental --remarks
fir compile prog.mfir --passes mem2reg,stackdce,fwd,copyprop,dse,dce --experimental -o prog
```

`--passes` in `fcc` and `fir compile` runs the named passes in order to a fixed point
(`Pipeline::parse_fixpoint`); `fir opt --passes` runs them once each, as before. Experimental
passes are refused without `--experimental`, and print a warning with it. `fcc
--check-dce FIR-REF` (and `FIR_CHECK_DCE`) checks the `dce` steps of a `--passes` pipeline too;
`fir compile --check-dce` stays with `-O`. The list above is
`fir::passes::EXPERIMENTAL_O`. From C, `fir_module_compile_passes` and
`fir_module_optimize_passes` take the same list and flag. The test knobs:

| Knob | What it adds |
|---|---|
| `FIR_PASSES=… cargo test -p fir --test opt` | the differential suite (fixtures, random and memory programs) on that pipeline (existed) |
| `FIR_PASSES=… cargo test -p fir --test aarch64` | the native suite's optimized builds use that pipeline |
| `FCC_PASSES=… cargo test -p fir-capi --test fcc` | a fourth native build of each C program, and two more interpreter layers (its MFIR, its allocated LFIR) |
| `cargo test -p fir --test mem2reg` | random programs made for promotion, and focused cases (always runs) |

## What was built

**`mem2reg`** (`crates/fir/src/passes/mem2reg.rs`, a module pass: field sizes need the data
layout's pointer size).

- *Candidates.* A `mem.stack` or `mem.stack.of`, in any region, whose pointer is used only as the
  address of `mem.load` and `mem.store` (not as a stored value), directly or through chains of
  `ptr.offset` (`.inbounds` or `.wrap`) by `int.const`s. Each offset is a field; a field's
  accesses must all have one type that comes back from memory unchanged and whose unwritten
  bytes read as `poison`: `iN` of whole bytes, `ptr`, `f32`, `f64` (as `Fwd.Exact`, minus `bN`,
  whose loads keep `poison` bytes as they are). Fields must not overlap. Each field becomes a
  variable: a slot of one scalar is the special case of one field at offset 0.
- *Rewriting.* One walk in program order keeps each variable's current value: a store sets it
  and is deleted; a load's uses get it and the load is deleted (or becomes a `copy` if its result
  has facts, which keeps them); before any store the value is a `poison` made next to the slot.
  The allocation stays, unused, and so do the `ptr.offset`s (`dce` deletes them).
- *Structured control flow.* A value reaches a later op only through regions' own channels, so
  for each `cf.if`, `cf.loop`, and `cf.blocks` with a store to a variable inside it (the slot made
  outside it), the variable is threaded where it is **live** (some path reads it before a store):
  a new result if live after the op (each `cf.yield`, `cf.break`, or branch leaving to it gets
  an operand), a new loop parameter if live at the top of the body (fed by the loop's operands
  and each `cf.continue`), and a new parameter of each non-entry block where live (each branch
  to it gets an argument). A `cf.if` region that fell off its end gets an explicit `cf.yield`.
  Liveness is a backward dataflow over the ops, whose edges are the structured control flow's.
- *Skipped:* functions with `cf.try` (HFIR) or `func.invoke` (unwinding edges would need the
  values too), and LFIR; slots stored inside a `cf.blocks` whose entry block is a branch target
  (an entry block can't take parameters); stores of holes.
- *Arena support:* `Body::replace_op` (rebuild an op with a wider signature, keeping its regions
  and the uses of its results) and `Body::append_params`.

**`stackdce`** (`passes/stackdce.rs`) deletes `mem.stack`/`mem.stack.of` ops whose pointer has
no uses. It is separate so that `mem2reg` itself never changes which allocations exist (see
Assumptions).

**Plumbing:** `backend::prepare_with` (compile with any pipeline), `fir compile --passes`,
the two C API functions, `fcc --passes … --experimental`, and the test knobs above.

### What liveness pruning was for

The first version threaded every variable stored inside an op through it. C's block-scoped
variables, which `fcc` makes at the function's entry, then became state of every loop and
parameters of every block around them. On `interpreter.c` (a `switch` in a loop) each of its 15
case blocks took six dead parameters, and the moves and spills made it **1.6× slower than
`-O`** (119k instructions against 75k) with twice the loads. With pruning it runs 69k (−8%), with
fewer loads than GCC's. Across the corpus pruning took instructions from −25% to −28% before
fields were added.

## Correctness

### What it rests on

`mem2reg` changes no allocation: the slot stays, and only accesses to it go. Its output should
refine its input in the semantics as written; that is not proved. The argument:

1. *Nothing else reaches a promoted slot's bytes.* Memory is separate allocations reached only
   through pointers with their provenance, and every use of the slot's pointer is one of its own
   loads or stores or a constant `ptr.offset` leading to them. The pointer is never stored,
   passed, compared, exposed (`ptr.expose`), or converted, so no other op, external function,
   or `ptr.from_exposed` can reach the allocation. This is the semantics' property, not an
   assumption; the proof needs it as an invariant of a memory relation.
2. *A field's load reads the last value stored to it, or `poison`.* Fields don't overlap, and
   each is accessed with one exact type: a store writes the value's encoding, and a load of the
   same type decodes it unchanged (`Fwd.Exact`, proved for `fwd`); unwritten bytes are `poison`
   (`Mem.lean`), and a load of `iN`, `ptr`, or a float from them is `poison`.
3. *Out-of-bounds or misaligned accesses* through the slot are UB in the source, so giving them a
   value refines it. The pass doesn't check bounds or alignment.
4. *Structured threading is renaming.* A variable's value at a point is a value visible there:
   the stored operand, an op's new result after it, or a new parameter inside a region. Values
   are threaded only where live, and every edge into a point where a variable is live comes from
   a point where it is live, so a value that isn't threaded is never read.
5. As for the proved passes: the source is assumed `Decided` (never `ambiguous`), and the
   argument is per function.

`stackdce` deletes allocations nothing uses. Such an allocation is never observed, but
allocations are numbered in creation order and events print pointers by number (`ptr #3`), so
deleting one renumbers the later ones. **`stackdce` assumes allocation numbers are not
observable**: its output refines its input up to a bijection of allocation ids, which holds on
hardware (a pointer is an address) but isn't the semantics' refinement. The differential suite
compares runs up to renaming allocations when `stackdce` is in the pipeline
(`rename_allocs` in `tests/opt.rs`). Stack allocation can't fail in the semantics (`newAlloc`
always succeeds), so deleting one loses no failure. A scalar-replacement pass that *split* a
struct slot into new slots would add allocations and need the same assumption, which is why
`mem2reg` promotes fields in place instead.

On the C side: `fcc` rejects `volatile`, so no volatile local is promoted. If it ever accepts
`volatile`, it must keep such locals unpromotable (FIR has no volatile access; making the slot
escape would do). C allows promoting the other locals across `setjmp`/`longjmp` (their values
are indeterminate after `longjmp`), and FIR models neither.

### How it was tested

- `tests/mem2reg.rs` generates mostly defined programs whose locals are typed slots (`i8` to
  `i64`, `ptr`, `f32`, `f64`) and C structs of them, across nested `cf.if` (with and without
  results, falling off their ends), counted loops (state of their own, `cf.break` with results
  and `cf.continue` from nested regions), and `cf.blocks` (`cf.br`, `cf.cond_br`, `cf.switch`
  with shared targets, back edges, yields, blocks in loops and loops in blocks), with `func.ret`
  from nested regions, values read before any store, and non-promotable slots (escaping,
  type-punned, a struct with an escaping field). Struct fields are reached through pointers made
  with the slot, made at the access, or offset from another field's. Each program must promote
  exactly the promotable slots, leave no access through them, leave the others alone, be
  idempotent, print and parse back, and refine the original run by run in the interpreter, after
  `mem2reg` alone (exactly) and after the whole pipeline (up to allocation renaming); every
  fifth also runs natively under qemu. Three seeds of 5,000 programs: ≈111k slots promoted
  (≈29k of them structs), 60,000 interpreter runs compared per pipeline (97.9% defined and
  equal, the rest UB in the source) and ≈11,700 native runs, no failure. Focused cases cover the
  shapes that broke during development.
- `FIR_PASSES` with the existing differential suite: the fixtures, the memory programs, and
  4,000 random programs per seed (`mem2reg` fires on ~24% of them), with and without
  `stackdce`.
- `FIR_PASSES` with the native suite (fixtures and random programs compiled with the pipeline
  and run under qemu).
- `FCC_PASSES` with the C corpus: all 67 programs match GCC natively, and the 57 the
  interpreter can run match at MFIR after the pipeline and at its allocated LFIR.
- The C API's tests call both new functions (refusal without the flag, an unknown pass, runs of
  the optimized module, assembly).

Development found and fixed, each now covered by a test: a `cf.if` given results whose region
fell off its end without `cf.yield`; branch labels compared by string id (labels aren't
interned, so the targeted-entry exclusion never fired); a loop given new state but no new
results dropping the state's initial values; a field at a negative offset named `%s.at-8`, which
the text can't spell.

## Measurements

Method (`frontends/c/bench/`): each corpus program is built by GCC `-O1`, `fcc`, `fcc -O`,
and `fcc` with the experimental pipeline, linked non-PIE, and run under `qemu-aarch64` with
TCG plugins that count instructions, loads, and stores executed in the program's own `.text`
(libc and the GCC-compiled helpers excluded), and a per-instruction histogram. Every build's
output and exit code match GCC's. Qemu-user's wall time isn't a proxy for hardware, so these
are executed-instruction counts, not times.

| | GCC `-O1` | `fcc -O` | + `mem2reg` (scalars) | + `mem2reg` (fields) |
|---|---|---|---|---|
| Instructions executed | 12.9M | 72.4M | 52.1M | **49.3M** |
| — geometric mean vs `-O` | ×0.215 | 1 | ×0.869 | **×0.845** |
| Loads executed | 0.28M | 19.7M | 1.81M | **1.07M** |
| Stores executed | 0.20M | 9.08M | 1.17M | **0.72M** |
| Code size (geo. mean vs `-O`) | ×0.287 | 1 | ×0.871 | **×0.850** |
| MFIR stack slots | | 3,383 | 1,078 | **705** |

Programs that run longest (instructions; `-O` → promoted, GCC for scale):

| Program | GCC `-O1` | `-O` | promoted | ratio | loads `-O` → promoted (GCC) |
|---|---|---|---|---|---|
| integration | 9.15M | 53.4M | 36.3M | 0.68 | 15.1M → 16k (8k) |
| mandelbrot | 1.19M | 4.10M | 2.66M | 0.65 | 1.34M → 7k (3k) |
| complex_math | 0.36M | 3.96M | 1.64M | 0.42 | 1.10M → 351k (43k) |
| vec3 | 0.18M | 1.92M | 1.08M | 0.56 | 516k → 287k (40k) |
| number_theory | 0.35M | 1.58M | 1.32M | 0.83 | 301k → 5k (2k) |
| sieve | 0.26M | 1.53M | 1.31M | 0.86 | 239k → 20k (20k) |
| sorting | 0.21M | 0.97M | 0.78M | 0.80 | 227k → 44k (28k) |
| interpreter | 0.03M | 0.075M | 0.069M | 0.92 | 13k → 5k (5k) |

Field promotion is what moves `complex_math` (0.93 → 0.42) and `vec3` (0.92 → 0.56): their
`struct { double re, im; }` values live in slots accessed field by field.

### Where the instructions go now

Executed instructions by kind, whole corpus:

| | GCC `-O1` | `fcc -O` | promoted |
|---|---|---|---|
| Loads + stores | 3% | 40% | 3% |
| Constants and addresses (`movz`, `movk`, `adrp`, `mov`/`fmov` of an immediate) | 1% | 21% | 30% |
| `fmov` between registers (float copies, and moving a built constant to a float register) | 9% | 4% | 15% |
| `mov` between registers (integer copies) | 1% | 1% | 4% |
| Compares and flags (`cmp`, `csinc`, `cset`, `ands`, `tst`) | 11% | 7% | 10% |
| Branches | 14% | 7% | 10% |
| Extensions (`sxtw`, `sbfx`, `ubfx`, …) | 0% | 4% | 7% |
| Everything else (arithmetic, float ops, calls) | 61% | 16% | 21% |

objdump spells an immediate `movz` as `mov x0, #42`; the histogram counts a `mov` or `fmov` with
an immediate operand as a constant. Promotion moved the cost from memory to constants above
all, then copies. Two loops show why:

- `integration.c`'s hot loop rebuilds each `double` constant every iteration with `movz`, three
  `movk`s, and an `fmov` to a float register: 41% of what it runs is `movk` and `fmov`. Of its
  `fmov`s between registers, 3.0M finish a constant and 4.0M copy a float value.
  Instruction selection materializes constants where they're used, and nothing hoists them out
  of loops.
- `sieve.c`'s inner loop is 20 instructions where GCC's is about five. Besides constants
  (`movz x3, #20000` then `sbfx` of it, every iteration), the compare is `subs; csinc; ands;
  b.eq` instead of `cmp; b.gt`; the index goes `sext` to `i128`, `mul` by the element size (1),
  and `trunc.nsw` back (the lowering of `ptr.index` keeps the overflow check exact); and a
  block of one `b` sits between the test and the body.

### What isn't promoted yet

Of the 705 slots left, by a heuristic classification of their uses (a slot can have several
reasons): **struct copies** (`mem.copy`, from struct assignment and by-value temporaries):
385; **arrays indexed by variables**: 177; mixed types or overlapping fields (unions,
`array<0 x …>` members, byte views): 134; **addresses passed to calls**: 104; `va_list`: 25;
addresses compared, exposed, or stored: 6. `complex_math` and `vec3` still run 8× and 7× GCC's
loads: `complex_math`'s promoted MFIR keeps 42 slots and 28 struct copies (`r = cmul(r, z)`
copies a call's result slot into `r`).

## Next, by measured payoff

1. **Constants out of loops, and cheaper float constants** (30%, and part of the 15% `fmov`): materialize a
   constant once per function or loop nest instead of per use (an MFIR hoisting pass is simple
   on structured loops; `int.const` and `float.const` are pure), and use `fmov #imm` or a literal
   pool load for `double`s.
2. **Copies** (4% integer, and part of the 15% `fmov`): loop and block parameters are copied on every edge. Register allocation
   should coalesce a block argument with its parameter when their live ranges don't interfere;
   `mem2reg`'s output made this visible, and any SSA-producing pass will add more.
3. **Compare and branch** (10%): select `int.cmp` whose only use is a `cf.if` or `cf.cond_br`
   condition as `cmp` + `b.cond`; fold small constants into immediates.
4. **Index arithmetic and extensions** (7%): MFIR rewrites such as `trunc.nsw(mul.wrap(sext
   x, c))` → `mul.nsw x, c` at `i64`, `mul x, 1` → `x`, extensions of constants folded. Each is
   a small local rewrite, the kind the project proves in Lean.
5. **More promotion:** split `mem.copy` between promotable struct slots into per-field copies
   (the largest remaining group); promote arrays whose indices are all constants; let a field
   that escapes keep only itself in memory instead of the whole struct.
6. **Proof.** The decision log names mem2reg as FIR-1's headline proof (decision: FIR-1 scope)
   and lists what it needs: a relation between memories (the promoted slot's bytes against the
   variables' values) and target code that reads hidden names. The fixed allocation set is
   meant to keep that relation simple; a certificate checker (the map from slots to variables at
   each point, checked per run like `dce`'s) is an alternative while the proof is open.
   `stackdce` needs refinement up to a renaming of allocations first.
