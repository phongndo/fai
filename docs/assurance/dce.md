# Dead code elimination: from the Lean theorem to the binary

This is the assurance case for one pass, `dce`, written link by link: what connects the theorem in
`spec/` to the code `fcc -O` and `fir compile -O` produce, and which kind of support each link
has. It is the most complete chain in the repository and the template for the others. The table
of every component is in [README.md](README.md#guarantees); the earlier audit and measurements
are in [layer-audit.md](layer-audit.md#3-the-dce-checker-lean-and-rust).

## In one paragraph

Compile with `fcc -O --check-dce FIR-REF` (or `fir compile -O --check-dce FIR-REF`, or with
`FIR_CHECK_DCE=FIR-REF` in the environment), and every step of `dce` in that compilation is
checked by a checker proved in Lean, on the module the pipeline actually produced. An accepted
step means that each function after it refines the function of the same name before it, **in the
module before it**, **if** that function is `Decided`. Nothing more is proved about the binary:
not that the optimized module refines the source module (composition is open), not that the
step's input is `Decided` (assumed), and not anything about the other passes, the lowering,
instruction selection, or the encoding, which are tested or checked by unproved code. The checker
runs as code compiled by Lean's compiler, and it reads the module as text the Rust printer
wrote, so those are trusted. Without `--check-dce` or `FIR_CHECK_DCE`, which is the default, no
proved code runs at compile time: the compiler's own Rust checker is tested against the proved one, not proved.

## Vocabulary

| Status | Meaning here |
|---|---|
| **Proved** | A Lean theorem, registered with the proof audit (`fir-audit`: standard axioms only, no `sorry`, statement and dependencies locked in `proofs.lock.json`). |
| **Checked** | Decided at compile time, on this input, by code whose acceptance a *proved* theorem says implies the property. A checked result inherits the theorem's hypotheses and the checker's trusted base. |
| **Checked (unproved)** | Decided at compile time by code nobody has proved; it can still be wrong in the same way the pass is. |
| **Tested** | Shown on the inputs the test suites run (fixtures, random programs, the C corpus), and by planted defects the tests must catch (`cargo xtask mutate`). Says nothing about other inputs. |
| **Assumed** | A hypothesis of a theorem that nothing establishes for the programs compiled. |
| **Trusted** | Relied on without proof or check: if it is wrong, the conclusions above can be wrong without any check failing. |
| **Open** | Neither proved nor checked; the property may be true, but nothing here shows it. |

## The chain, for one `fcc -O --check-dce` compilation

| # | Link | Status | Backed by |
|---|---|---|---|
| 1 | The op kinds `dce` may delete are pure | **Proved** | `Fir.Dce.dcePerm_sound`; the Rust contract table is generated from `dcePerm` and checked fresh by `verify` |
| 2 | Deleting pure, unread ops refines a function (in a fixed module, `Decided` source) | **Proved** | `Fir.Dce.refines` |
| 3 | `checkFunc` accepting implies that relation | **Proved** | `Fir.Dce.checkFunc_sound` |
| 4 | The faster checker that runs (`checkFuncL`) decides what `checkFunc` does | **Proved** (new) | `Fir.Dce.checkFuncL_eq`: equal verdicts on every pair of functions |
| 5 | Accepting two modules relates their functions name by name | **Proved** (new) | `Fir.Dce.checkModule_sound`, stated over `Module.find?` (the first function of a name). The interpreter's calls take the *last* of a name (`Core.funcs`); the two agree because `fir-ref` verifies both modules and the verifier refuses duplicate names (`Verify.lean`), a fact the theorem doesn't carry. Before, this pairing was unproved code in `Main.lean` |
| 6 | The Rust pass's plan and `erase_many` | not relied on when checking | the output is checked whatever produced it |
| 7 | The module the checker reads is the module the pipeline holds | **Trusted**, partly **checked** | the Rust printer writes the module; Lean parses it and prints it back; the receipt must equal the Rust text byte for byte (`passes::reference`). That shows the printer and Lean's parser agree on *this text*, not that the text means what the in-memory module does. It also relies on link 9: a stand-in `fir-ref` that prints its inputs back would pass it |
| 8 | The checker computes what its Lean definition says | **Trusted** | `fir-ref` is Lean code compiled to C by Lean's compiler, then compiled and linked with Lean's runtime by the host's C compiler and linker (the Lean toolchain's, not the AArch64 target's) |
| 9 | The `fir-ref` used is built from these proofs | **Trusted** (checked in CI) | `verify full` rebuilds `spec/` from scratch (not with `--no-lean-clean`); a path given by hand is the caller's responsibility (the receipt doesn't name a version) |
| 10 | Every `dce` step of the run was sent to the checker | **Checked (unproved)** | `CheckDce` snapshots before each `dce` and skips a step only if the printed module is unchanged, not on the pass's own count (`check_dce_checks_steps_that_report_no_changes_but_change_the_module`) |
| 11 | The source of each step is `Decided` | **Assumed** | nothing checks it; see below |
| 12 | Per-function refinements compose into module refinement (each target function's calls go to *target* functions) | **Open** | `tests/opt.rs` runs optimized modules against their sources (tested) |
| 13 | Refinement composes across the steps of the pipeline | **Open** for modules | `Func.Refines.trans` composes steps of one function in a fixed module only |
| 14 | `fwd`, `copyprop`, `dse` | relations **proved**; passes **tested** | `Fir.Fwd/CopyProp/Dse.refines`; no checker of their outputs |
| 15 | C to HFIR (`fcc`'s lowering) | **Tested** | the C corpus against GCC, natively and in the interpreter |
| 16 | HFIR to MFIR | expansion **proved** per function; the rest **tested** | `Fir.Lower.Proof.lowerFunc_refines`; `tests/lower.rs` against `fir-ref lower` |
| 17 | Instruction selection, allocation, encoding | **Tested**; allocation **checked (unproved)** | native runs; `regcheck::validate` |
| 18 | The semantics in `spec/` is the meaning we want for FIR | **Assumed** (it is the definition) | the interpreters agree with it on the tests; it is what every theorem is about |

Links 1–5 are the proof; 7–10 connect it to the run; 11–13 are why "checked" does not mean "the
optimized program is correct"; 14–18 are everything else between the C source and the binary.

### Without `--check-dce` (every compilation by default)

Links 1–2 still hold for the *relation*, but no proved code runs. The compiler applies a deletion
only if the Rust checker `passes::dce::check` accepts it (**checked (unproved)**), and then
`Body::erase_many` performs it (**trusted**). That the Rust checker accepts only what the proved
one would is **tested**: `the_rust_and_lean_checkers_agree_on_random_candidates` gives both the
same candidates (thousands per run, none disagreeing), and the mutation
`dce-checker-weaker-than-proved` shows a weakened Rust checker is caught. The Rust checker checks
the *candidate*, not the output, so a bug in `erase_many` would not be seen by it.

## The theorem the check rests on

```lean
theorem Fir.Dce.checkModule_sound {tgt src : Module} (h : checkModule tgt src = true)
    (name : String) :
    Option.Rel (fun t s => s.Decided src → t.Refines src s) (tgt.find? name) (src.find? name)
```

For every name: both modules have a function by it or neither does, and if both do, the target's
refines the source's **in `src`**, if the source's is `Decided` in `src`. `Func.Refines mod tgt
src` quantifies over every argument list (`poison` included), every oracle, and every monotone
world, and says each behavior of `tgt` (its external calls and how it ends) refines some behavior
of `src`.

`checkModule` itself is `checkFuncL` on each pair of functions, in order, with equal names and
source files. `fir-ref check-dce` also requires the modules to print the same outside their
functions (layer, memory space, globals, externs). That comparison is **unproved** and is not
needed by the theorem (which never mentions the target's globals); it is there because the open
composition step would need it.

## What `Decided` rules out, and where it can fail

`Func.Decided mod f`: no run of `f`, for **any arguments** in any monotone world, ends
`ambiguous`. In the semantics (`spec/Fir/Interp.lean`; by reading and grep, not by proof) the
only `halt .ambiguous` is in `resolveIn`, reached through `resolve` when a pointer is turned into
an allocation: by a memory access, by `free`, by an indirect call, and when a `noalias` or
`readonly` scope opens. It halts `ambiguous` when an **address-only pointer** (`Ptr.abs`) could
belong to two live allocations (with size 0 that includes an address one past the end of one
allocation and at the start of the next), or carry two tags an active scope tells apart.

Address-only pointers enter a run from:

- **the arguments**: `Decided` quantifies over every argument list, and any pointer value,
  address-only ones with arbitrary candidates included, has type `ptr` (`RVal.hasTy`);
- `ptr.from_exposed`;
- loads of a pointer from bytes that don't form one whole pointer (integer bytes, or mixed or
  partial pointer fragments: `decodeAs`);
- `ptr.with_addr` and offsets of such a pointer;
- external calls, whose results and memory writes the world chooses.

So excluding the code that makes address-only pointers is not enough for a function that frees,
calls through, accesses, or scopes a pointer it was given: a crafted address-only argument
reaches `resolve`. (Some functions are `Decided` by their code alone, such as one that never
turns any pointer into an allocation, but that excludes almost every function with a pointer
parameter.) A useful sufficient condition for the rest has to restrict the arguments too (for example, to pointers with provenance, which is what a caller
inside the program passes unless the pointer came from one of the sources above) and the
world's answers. `fcc` emits `ptr.from_exposed` for casts from integers to pointers
(`frontends/c/tests/pointer_int_casts.c`), so within a C program those casts are the likeliest
place for the assumption to fail. Nothing checks it today.

## What changed in this round, and what it cost

1. **A faster proved checker.** `checkFunc`'s `deletable` scans the rest of the region for each
   deleted op, so the proved checker was quadratic: 16.5 s for one function of 128,000 ops (half
   of them deleted). `checkFuncL` keeps a count of reads per name for the target ops not yet
   matched (`Std.HashMap`), and is proved equal to `checkFunc`, so no theorem about verdicts
   changed. Its cost is linear in a function's size times its nesting depth (each region's
   counts are built once, and matching an op walks its regions), with hash-map operations at
   their expected cost; that is by construction and measured on flat functions below, not
   proved. `fir-ref check-dce` on one function (both builds of `fir-ref` from the same tree,
   differing only in the checker called; best of three; receipts byte-identical):

   | One function of | `checkFunc` (before) | `checkFuncL` (now) | parsing and printing alone |
   |---|---|---|---|
   | 2,000 ops | 13 ms | 10 ms | 7 ms |
   | 8,000 ops | 84 ms | 39 ms | 26 ms |
   | 32,000 ops | 1.0 s | 145 ms | 100 ms |
   | 128,000 ops | 16.5 s | 0.69 s | 0.44 s |

   What remains is mostly the text round trip and process start, not checking.
2. **A proved module checker.** The pairing of functions by name and file moved from `Main.lean`
   into `Fir.Dce.checkModule`, with `checkModule_sound`: `fir-ref check-dce` accepts only if
   `checkModule` does (the loop after it only names the function to blame). Its other checks,
   that both modules parse and verify and print the same outside their functions, can only
   refuse.
3. **The proved checker on the compiler's own path.** `fir::backend::optimize`, which
   `fir compile -O`, `fcc -O`, and the C API's `fir_module_optimize`/`fir_module_compile` run,
   checks every `dce` step when `FIR_CHECK_DCE` names a `fir-ref` (`fir opt -O` honours it too); `fir compile` and `fcc` take
   `--check-dce FIR-REF`. A refusal, a receipt for other modules, or a path that isn't a file
   fails the compilation (`the_compiler_runs_the_proved_checker_when_asked`, with stand-in
   `fir-ref`s that refuse or lie).
4. **The corpus's natively run binaries are checked builds.** The C corpus test builds each
   program's `fcc -O` binary with `--check-dce`, and `verify full` (on Linux) requires every
   program's `-O` build to have been checked, run natively, and matched GCC. Outside `verify full`
   the test builds unchecked when there is no `fir-ref` (or `FIR_REF=none`), and says so; the ABI
   torture test's `-O` builds are not checked. On the current corpus: 67 programs, 67 checked `-O` builds, 71
   `dce` steps accepted, 3,462 deletions (as the pass counted them; the checker doesn't count),
   none refused, and all 67 binaries print and exit as
   GCC's do. The check adds about 15 ms per program to a compilation of about 22 ms (`fcc` as
   the corpus test builds it, `--emit asm`, the whole corpus timed twice), almost all of it
   starting `fir-ref` and the text round trip.

## Reproducing

```sh
cd spec && lake build && cd ..                      # fir-ref, with the linear checker
cargo run --bin fir -- compile FILE -O --check-dce spec/.lake/build/bin/fir-ref --emit mfir
fcc FILE.c -O --check-dce spec/.lake/build/bin/fir-ref -o a.out
cargo test -p fir --test dce_check                  # the checker on fixtures, random programs, -O
cargo test -p fir-capi --test fcc -- fcc_corpus --nocapture   # the C corpus, checked
cargo test -p fir-capi --test fcc -- fcc_x86_64_corpus --nocapture   # the same on x86-64
cd spec && lake exe fir-audit --lock ../docs/assurance/proofs.lock.json   # the claims
```

## Next steps, by value per cost

1. **A checked `Decided` for the common case**: for a function that resolves a pointer it was
   given, `Decided` as defined can't be established from its code alone (arguments are
   arbitrary). The step is a weaker hypothesis the pass
   theorems can use instead: refinement for runs whose arguments and world answers carry
   provenance, plus a proved syntactic check that the code can't make an address-only pointer
   itself. Where that applies, link 11 goes from assumed to checked; the restriction on arguments
   becomes a statement about callers, to be discharged by module composition.
2. **Module composition** (link 12): if every function of the target refines its namesake in the
   source module, the target module refines the source module. This is what would let "checked"
   mean the optimized module is correct, and every pass needs it.
3. **Run the proved checker in CI builds of the corpus** (done here) and **in process**
   (Lean's C output linked into `fir` behind `@[export]`), which would remove the process and the
   files, but not the text round trip, and would put Lean's runtime in the compiler.
4. **An output checker in Rust**, a transcription of `checkOpsL`, run on every compilation and
   held to the Lean one by the agreement test: still unproved, but it would check the output
   instead of trusting `erase_many`, cheaply, without Lean at compile time.
