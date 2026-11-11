# The three layers: HFIR, MFIR, LFIR

FIR has one structure (ops, regions, typed values, one text grammar, one Lean semantics) used at three layers. Each layer has one audience, and each boundary between layers is both an API contract and a proof boundary.

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

| Step | How it is justified |
|---|---|
| Source → HFIR | The frontend's responsibility; optional proofs through the Lean SDK |
| HFIR → MFIR | Building-block lowerings proved once, for every frontend |
| MFIR → MFIR | Each rewrite rule proved in Lean or SMT-checked in CI |
| MFIR → LFIR | Legalization and instruction selection checked against ISA semantics |
| LFIR → code | Register allocation and scheduling validated on each run; encoding tested by the conformance suite |

## Execution paths

- **AOT (the first phase):** HFIR → MFIR → LFIR (native target) → object file.
- **JIT (later):** HFIR → MFIR, shipped as bytecode. At runtime: interpreter or baseline tier, then an optimizing tier that reruns MFIR passes with speculation, then LFIR, then code in memory.
- **Web (later):** HFIR → MFIR → LFIR (`wasm`) → `.wasm`.

## Why three layers

- **One layer (the LLVM IR approach)** forces frontends to lower too early, so parallelism, tensors, and ownership are lost. LLVM ends up with hidden, unverified internal layers anyway.
- **Unbounded layers (the MLIR approach)** give no shared contract and no fixed pipeline to prove.
- **Three fixed contracts** keep MLIR-level flexibility inside each layer, LLVM-level agreement at the boundaries, and give each proof a fixed start and end.
