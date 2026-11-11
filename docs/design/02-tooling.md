# Tooling goals

Every tool uses the same Lean semantics as the optimizer. If the optimizer may exploit a piece of undefined behavior, the tools can flag exactly that behavior. This closes the gap between "the sanitizer passed" and "the compiler broke my code".

All of these work for every language with a FIR frontend, including C and C++.

| Problem | Mechanism | Mode |
|---|---|---|
| UB: overflow, out-of-bounds, use-after-free, uninitialized reads, null | UB-precise reference interpreter; sanitizer mode where `assume` facts become runtime checks | Dynamic |
| Memory leaks | Allocation is a first-class op with provenance; unreachable allocations are reported at exit with their source site | Dynamic; static ownership analysis later |
| Infinite loops | Explicit forward-progress semantics. No-progress loops are detected at runtime. Statically, termination is proved where possible, with warnings for side-effect-free loops that can't be proved to terminate | Dynamic and static |
| What the optimizer assumed | A report of every UB exploitation, for example "deleted this null check because `p` was dereferenced at line 12" | Compile time |
| Inputs that trigger bugs | Symbolic execution and SMT over the exact semantics | Bounded |
| Data races | Follows from the concurrency semantics | Later |
| Why the code looks this way | `--explain`: the provenance chain of rules back to source | Compile time |
| Trust status of a build | Assurance report: which steps were proved, certificate-checked, SMT-validated, or trusted; which facts were assumed or checked | Per build |

## Limits

- No tool finds every leak or infinite loop, by the halting problem. Dynamic checking is precise but only sees executed inputs, bounded symbolic search finds real bugs within its bounds, and static analysis covers every input but gives false alarms.
- The tools are only as faithful as the frontend's lowering. C's aliasing, effective-type, and provenance rules must be translated correctly.
- FIR only knows what the frontend tells it. Ownership-aware leak analysis needs ownership facts in HFIR.
- Interpreter-based checking is orders of magnitude slower than native code. It is for tests and CI; sanitizer mode is the fast option.

## Design requirements these impose

- Allocation is a first-class op with provenance (memory decisions).
- Forward progress has explicit semantics (control-flow decisions).
- Every op has a source location and a provenance entry (structure decisions).
- HFIR can carry ownership facts (building-block decisions).
