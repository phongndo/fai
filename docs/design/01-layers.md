# The three layers: HFIR, MFIR, LFIR

FIR has one structure (ops, regions, typed values, one text grammar, one Lean semantics) used at three layers. Each layer has one audience, and each boundary between layers is both an API contract and a proof boundary.

This file is the design target, except [Layers in the op table](#layers-in-the-op-table), which describes what is built. What each layer means today, what each boundary keeps and loses, and what is still unknown are in [layers-as-built.md](layers-as-built.md).

```
 languages ──Builder API──▶ HFIR ──proved lowering──▶ MFIR ──checked isel──▶ LFIR ──validated regalloc──▶ code
                         (frontends)               (optimizer)            (backends)
```

| | HFIR | MFIR | LFIR |
|---|---|---|---|
| Audience | Frontends | The FIR optimizer | Backends |
| Allowed ops | Core ops plus building blocks | Core ops plus the ops the target declares legal | Target dialects |
| Hardware knowledge | None | Data layout and target-legal ops; target queries | Full |
| Control flow | Structured, plus opt-in `cf.blocks` jump regions | Structured, plus opt-in `cf.blocks` jump regions; explicit unwind handlers | Target-specific; `wasm` stays structured |
| Facts | Written by the frontend | Used and upgraded (`check` becomes `proved`) | Consumed: `check` facts become instructions, the rest disappear |

The verifier enforces each layer's allowed ops. A `slice.get` in MFIR or an `x86.*` op in HFIR is an error.

## Layers in the op table

Each op's declaration (`fir_ops` in `spec/Fir/Syntax.lean`) names the layers that allow it, `layers hfir mfir` by default, and belongs to a dialect: the namespace of its name (`int`, `mem`, `ptr`, `cf`, `func`, `ty`), or `value` for `poison`, `freeze`, `copy`, and `select`. A module states its layer before anything else it declares:

```
layer mfir
memspace default ptr 32 addr 32
```

`layer hfir`, `layer mfir`, or `layer lfir aarch64`. Without a `layer` line a module is HFIR, and HFIR prints as nothing, like the default memory space. The verifier rejects an op its module's layer doesn't allow, before checking anything else about it, with the same message in Lean and Rust: `ptr.field.inbounds is not allowed in layer mfir; it is allowed in hfir`.

| | HFIR | MFIR | LFIR for target `T` |
|---|---|---|---|
| Core ops | All | All but `ptr.field` and `ptr.index` | `func.ret` |
| Building blocks (`union`, `slice`, `int.*.overflow`, `cf.try`) | All | None | None |
| `agg.make`, `agg.extract`, `agg.insert` | All | For the structs and arrays calls pass whole | None |
| Exceptions (`exn.throw`; `func.invoke`) | `exn.throw` | `exn.throw`, `func.invoke` | The exception slot (`aarch64.exn.*`, `aarch64.b.exn`) |
| Value types | Scalars (`iN`, `bN`, `ptr`, `f32`, `f64`), structs, arrays, unions, slices | Scalars; structs and arrays only to pass whole across calls | None in function bodies (registers); signatures as MFIR's |
| Target dialects | None | None yet | `T`'s |

- The building blocks are HFIR only, and so are values of union and slice types. Structs and arrays stay in MFIR as values only so calls can pass them whole as the C ABI's unit: `agg.make` builds one where it is passed, and `agg.extract` takes it apart where it arrives (decisions: Aggregates, C ABI for aggregates). The MFIR verifier enforces this for loads, stores, and `select`, but not yet for region state and holes ([layers-as-built.md](layers-as-built.md#6-gaps), G9). `fir lower` turns an HFIR module into MFIR (decision: HFIR lowering). `cf.check`, which their checks lower to, is a core op.
- Exceptions (decisions: Exception values, Exceptions in MFIR): HFIR catches with `cf.try`; MFIR has no `cf.try`, and a call that may throw names its handler, a block of the nearest `cf.blocks` (`func.invoke`). `exn.throw` is in both: in MFIR it unwinds out of the function. LFIR for AArch64 passes exceptions back through the exception slot (decision: Exceptions at run time).
- `ptr.field` and `ptr.index` address by type, so they are HFIR only. MFIR addresses with `ptr.offset` by an offset: `ty.offset`, or the index times the stride (decision: Layout). `ty.size`, `ty.align`, and `ty.offset` stay in MFIR as layout queries the optimizer can fold.
- LFIR keeps `func.ret` because every layer has functions; globals and external functions are module structure, not ops. LFIR for AArch64 doesn't keep `cf.blocks`: a function's code is `aarch64.code`, labeled blocks of machine instructions on registers with explicit branches (decision: LFIR for AArch64). A function whose body is a plain `func.ret` of its parameters returns them where the calling convention puts results.
- The targets are listed in `Fir.targets` (`aarch64`). Adding one means naming it there and declaring its ops in its dialect with `layers lfir`. An unknown target is a parse error, like an unknown op.
- The interpreter runs HFIR and MFIR the same way. It never reads the layer, so an op means the same wherever it is allowed. LFIR modules run on their target's machine (`Fir.AArch64Machine`: registers, flags, and FIR's memory), since target ops read and write registers, not SSA values. Lean defines behaviors and refinement only for the first machine.
- Every layer depends on the module's data layout (its `memspace` line), which is chosen in HFIR and never changes. As built, HFIR is therefore not hardware-neutral: the AArch64 backend accepts only AAPCS64's layout.

## HFIR

HFIR is the contract between a language and FIR, and it carries no hardware information. It contains:

- **Core ops:** integers with explicit UB modifiers, pointers, memory, calls. C mostly uses these directly.
- **Building blocks:** language-neutral, proved ops such as slices, structs, tagged unions, closures, checked arithmetic, exceptions, GC references, and parallel loops.
- **Facts and source locations** on every op.

The reference interpreter, sanitizer mode, and UB finder report their results at this level, mapped to source lines.

## MFIR

MFIR is where optimization happens. Building blocks have been lowered by proved lowerings, so rewrite rules only need to reason about a small op set. It contains:

- core ops;
- facts;
- per-op effects;
- JIT speculation ops (`spec.assume` and `spec.anchor`, following CoreJIT), added in the JIT phase.

**Target legality rule.** MFIR is core ops plus whatever ops the chosen target declares it handles natively. For example, a CPU target lowers `tensor.matmul` to loops, while an accelerator keeps `tensor.matmul` intact down to LFIR.

Upper layers ask the target questions through the target-query API ("vector width?", "native matmul?"). Information flows up as answers; code never moves back up.

In the JIT phase, serialized MFIR becomes the portable bytecode shipped to JITs.

## LFIR

LFIR is the contract between FIR and a chip. It consists of target dialects (`x86`, `arm`, `riscv`, `gpu`, `wasm`, or a vendor's own), each with semantics taken from the ISA spec. Registers and branch-and-block control flow appear here.

To add a chip, a vendor writes:

1. the LFIR dialect and its semantics;
2. a legality declaration;
3. instruction-selection rules, which are SMT-checked against the dialect semantics;
4. a run of the conformance suite.

All frontends, MFIR optimizations, and tools then work on the new chip.

## Proof chain

This is the design's target. What is proved, checked, or only tested today is in
[the assurance report](../assurance/README.md#guarantees), and the boundaries as built are audited
in [layer-audit.md](../assurance/layer-audit.md). In particular, only the expansion step of the
lowering is proved, instruction selection is tested rather than checked against ISA semantics,
the allocation validator is not proved, there is no scheduler, facts are dropped by instruction
selection, and MFIR still has `agg.*` ops and composite values.

| Step | How it is justified |
|---|---|
| Source → HFIR | The frontend's responsibility; optional proofs through the Lean SDK |
| HFIR → MFIR | Building-block lowerings proved once, for every frontend |
| MFIR → MFIR | Each rewrite rule proved in Lean or SMT-checked in CI |
| MFIR → LFIR | Legalization and instruction selection checked against ISA semantics |
| LFIR → code | Register allocation certificate-checked on each run by a checker proved in Lean; scheduling SMT-validated; encoding tested by the conformance suite |

## Execution paths

- **AOT (the first phase):** HFIR → MFIR → LFIR (native target) → object file.
- **JIT (later):** HFIR → MFIR, shipped as bytecode. At runtime: interpreter or baseline tier, then an optimizing tier that reruns MFIR passes with speculation, then LFIR, then code in memory.
- **Web (later):** HFIR → MFIR → LFIR (`wasm`) → `.wasm`.

## Why three layers

- **One layer (the LLVM IR approach)** forces frontends to lower too early, so parallelism, tensors, and ownership are lost. LLVM ends up with hidden, unverified internal layers anyway.
- **Unbounded layers (the MLIR approach)** give no shared contract and no fixed pipeline to prove.
- **Three fixed contracts** keep MLIR-level flexibility inside each layer, LLVM-level agreement at the boundaries, and give each proof a fixed start and end.
