# North star: semantics as the platform

FIR is a compiler environment for AOT, JIT, VM-based, and web (Wasm) targets, built around one formal semantics.

## Phasing

The first phase is the **AOT compiler** only, with a C subset as the first frontend. Nothing else is being built yet. Within it, the three layers and the builder API come first, then the C frontend as the first compiler on top; see [03-plan.md](03-plan.md).

Planned for later phases:

- **JIT:** serialized MFIR as portable bytecode, tiered compilation, and proved speculation.
- **VM embedding:** a kit for language VMs, with an interpreter tier, a GC interface, and deoptimization.
- **Web:** WebAssembly output.

Decisions made with these later phases in mind stay in the design, such as speculation ops, guaranteed tail calls, room for GC references, and `unordered` memory accesses. That way, adding a phase later won't change the core. Nothing is implemented for a phase until that phase starts.

Most verified compilers keep their proofs internal, so only the compiler author benefits. FIR exposes its semantics and proofs as the API that frontends, backends, and tools are built on. A frontend or backend that plugs into FIR gets correctness checking, debugging tools, and optimization for free.

## Goals

1. **One uniform IR for all hardware.** One structure and one semantics for CPUs, GPUs, accelerators, and Wasm. Hardware differences are explicit target dialects, never special cases.
2. **Formally backed.** Every op has a meaning defined in Lean. Every step is proved once, certificate-checked on each run by a checker proved in Lean, SMT-validated, or trusted. Each build reports which of these applies.
3. **Excellent developer experience** for people and agents: readable canonical text, fast feedback on rules, clear errors, and explanations of what the compiler did.

## Principles

- **The Lean spec is the source of truth.** The Rust implementation is checked against it by generated rule matchers, differential testing against the reference interpreter, certificate checkers proved in Lean, and SMT translation validation.
- **No op without semantics.** Every op has one of three trust tiers:
  - *verified*: Lean semantics with proofs;
  - *specified*: SMT-checkable semantics;
  - *opaque*: only a signature and declared effects, which the optimizer treats as a call.
- **UB is explicit.** Undefined behavior is never implied by a default. Ops name their overflow and trap behavior, and deferred UB is `poison` plus `freeze`. There is no `undef`.
- **Facts carry a trust level.** Claims the optimizer relies on are written on values as `assume`, `check`, or `proved`.
- **Layer boundaries are fixed contracts.** Inside a layer, dialects can be anything. See [01-layers.md](01-layers.md).
- **A stable C API from day one.** Frontends in any language bind to it, and the implementation behind it can be replaced later, including by a self-hosted one.

## What frontends get

- A builder API that requires explicit UB choices on every op.
- Facts, plus a sanitizer mode where every `assume` fact becomes a runtime check.
- A reference interpreter that reports UB at the source line.
- A UB finder that produces concrete counterexample inputs.
- Proved lowerings for common language features.
- Optionally, a Lean proof SDK for end-to-end proofs of the frontend itself.

## What backends get

- Target instruction semantics, imported from official ISA specs where they exist.
- Instruction-selection rules checked against those semantics.
- Proved legalization for operations the target doesn't support natively.
- A register allocator whose output is checked on every run by a checker proved in Lean.
- A conformance suite that compares the target against the reference interpreter.

## What everyone gets

- An assurance report per build.
- `--explain` provenance for every op.
- Automatic checking of rules and lowerings, whether a person or an agent wrote them.

Details are in [02-tooling.md](02-tooling.md). Decision status is in [decisions.md](decisions.md).
