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
proved code runs at compile time. What runs instead, in every compilation, is two Rust checkers:
one judges the pass's candidate before it is applied, and one, a transcription of the proved
checker, judges the output after it is applied (`dce::check_output`). Neither is proved; both
are tested against the proved checker, on the pass's outputs and on thousands of targets it
would never produce.

## Vocabulary

| Status | Meaning here |
|---|---|
| **Proved** | A Lean theorem, registered with the proof audit (`fir-audit`: standard axioms only, no `sorry`, statement and dependencies locked in `proofs.lock.json`). |
| **Checked** | Decided at compile time, on this input, by code whose acceptance a *proved* theorem says implies the property. A checked result inherits the theorem's hypotheses and the checker's trusted base. |
| **Checked (unproved)** | Decided at compile time by code nobody has proved; it can still be wrong in the same way the pass is. |
| **Tested** | Shown on the inputs the test suites run (fixtures, random programs, the C corpus), and by planted defects the tests must catch (`fai mutate`). Says nothing about other inputs. |
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
| 6 | The Rust pass's plan and `erase_many` | not relied on when checking | the output is checked whatever produced it (by the proved checker with `--check-dce`; by its Rust transcription in every compilation) |
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

Links 1–2 still hold for the *relation*, but no proved code runs. Each run of `dce` that deletes
anything does three things (`passes::dce::run`):

1. The Rust checker `passes::dce::check` accepts the candidate (the ops to delete) or the run
   fails (**checked (unproved)**). That it accepts only what the proved checker would is
   **tested**: `the_rust_and_lean_checkers_agree_on_random_candidates` gives both the same
   candidates, and the mutation `dce-checker-weaker-than-proved` shows a weakened Rust checker is
   caught.
2. `Body::erase_many` performs the deletion.
3. `passes::dce::check_output` compares the body after with a copy of the body before, and the
   run fails, with the copy put back, unless the result is what the proved checker would accept
   (**checked (unproved)**). It is a transcription of `Fir.Dce.checkFuncL` over the compiler's
   own representation: the same greedy matching region by region, the same deletability rule
   (a kind `dcePerm` deletes, no regions, operands all variables, no read of its results by
   name among the target ops not yet matched in its region, at any depth), and the same read
   counts. It compares ops id by id, after checking that both bodies give every id the same
   meaning (`Body::same_tables`: the same values with the same names, types, and facts, the
   same strings, constants, holes, successors, cases, and types), which makes it stricter than
   Lean's comparison of names and printed fields, never looser. That its verdicts are the
   proved checker's is **tested**, not proved: the agreement test sends every target it builds
   to both (below), and the mutation `dce-output-check-weaker-than-proved` shows a weakened
   output check is caught. The mutation `dce-apply-deletes-more` plants the bug step 2 could
   have (applying an approved deletion also erases the function's stores, which verifies and
   which no candidate check sees) and the output check refuses the result.

So without `--check-dce`, `erase_many` is no longer trusted: its result is checked, by unproved
code that is tested against the proved code. A run with nothing to delete doesn't touch the
body, and is not checked.

`check_output` follows the pipeline's policy as the pass does: under `Policy::AllowTrusted` (the
default) it would let a kind with a *trusted* permission go, which the proved checker refuses.
No kind has one today (every `Dce::Delete` in the generated contracts is `Evidence::Proved`), so
the two policies decide the same.

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

## What the third round changed: the output checked in every compilation

The second round (next section) put the proved checker on the compiler's path, on request. This
round makes what runs by default check the pass's *output*, and puts more of the pipelines
programs actually go through under the proved checker.

1. **The output check, on by default.** `passes::dce::check_output` (described above, under
   *Without `--check-dce`*) runs in every `dce` run that deletes something, in `fir opt`,
   `fir compile`, `fcc`, and the C API alike. It closes the gap the previous section left open:
   the default path checked a candidate and trusted `erase_many` to apply it.
2. **Held to the proved checker by a differential test.** In `tests/rust/dce_check.rs`:
   * every module the pass changes in `the_pass_is_validated_by_the_proved_checker` (the
     fixtures, 200 random programs, and their lowered MFIR) goes to both: 1,089 function pairs,
     all accepted by both;
   * `the_rust_and_lean_checkers_agree_on_random_candidates` builds a target for every random
     candidate that can be written out (erasures of planned, kept, and arbitrary ops, from
     inside regions too), plus targets that aren't deletions at all (two operands of an op
     swapped), and requires `check_output` and `fir-ref check-dce` to agree on each one that
     verifies. At the default size: 78 deletions accepted by both, 1,761 deletions and 626
     swaps refused by both, and 2,239 deletions whose targets don't verify (the proved checker
     never sees those; `check_output` refused them all). At `FIR_FUZZ=800`: 238 accepted by
     both, 5,128 deletions and 1,194 swaps refused by both. None disagreed.
   * Unit tests in `dce.rs` give it a deleted store, a deleted read op, ops changed in place
     (at the top level and inside a region), a changed operand, a deleted region op and
     terminator, a `freeze`, and a body from elsewhere, and check each reason.
3. **Cost.** On one function of 128,000 ops of which 64,000 are dead (the measurement of the
   previous section), `dce` takes 6.1 ms without the output check, 9.0 ms with only the copy of
   the body, and 13.4 ms with copy and check (release build, best of five, `fir opt -O
   --stats`); the whole `fir opt -O` takes 60 ms. A `dce` run that deletes nothing, which is most
   runs (every fixed-point pipeline ends with one), costs nothing extra. The proved checker on
   the same function takes 0.69 s, nearly all of it the text round trip.
4. **The `FCC_PASSES` builds are checked too.** The C corpus test now passes `--check-dce` to
   the build with `FCC_PASSES`'s pipeline as well as to `-O`, on both targets, and counts those
   steps separately (and records them as evidence when `FCC_PASSES` is set). With the
   experimental promotion pipeline (`FCC_PASSES=mem2reg,stackdce,fwd,copyprop,dse,dce`):

   | | AArch64 | x86-64 |
   |---|---|---|
   | programs (x86-64: those it compiles) | 69 | 49 |
   | `-O` builds checked, all running as GCC's do | 69 | 49 |
   | `-O` `dce` steps accepted (deletions, the pass's count) | 73 (3,471) | 42 (3,301) |
   | `FCC_PASSES` builds checked, all running as GCC's do | 69 | 49 |
   | `FCC_PASSES` `dce` steps accepted (deletions) | 17 (5,998) | 9 (3,240) |
   | steps refused | 0 | 0 |

   Most programs' promotion pipeline gives `dce` nothing to do: `mem2reg` and `stackdce` delete
   the loads, stores, and slots they make dead themselves, and no checker sees those deletions
   (they are experimental and unproved: [README.md](README.md#guarantees)). Where `dce` does
   delete after promotion, the deletions are larger than `-O`'s.

## What the second round changed, and what it cost

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
FCC_PASSES=mem2reg,stackdce,fwd,copyprop,dse,dce \
  cargo test -p fir-capi --test fcc -- fcc_corpus fcc_x86_64_corpus --nocapture   # and the promotion pipeline's builds
cargo test -p fai-transforms --lib dce::tests       # the default output check, unit tests
fai mutate dce-apply-deletes-more dce-output-check-weaker-than-proved   # its planted defects
cd spec && lake exe fir-audit --lock ../docs/assurance/proofs.lock.json   # the claims
```

## Why composition (link 12) is open, and what closing it takes

`checkModule_sound` relates each target function to its source *in the source module*: the
target function's calls run the source's callees. Running the optimized module runs the
target's. The lockstep framework every pass proof uses (`spec/Fir/CodeRel.lean`) is where this
shows: `MRel` relates machines with **equal cores**, and the core holds the module's functions
(`Core.funcs`), so the two machines must be running the same module. A call pushes the callee's
body on both stacks unchanged (`execFlat_eq`, the `.func f` case, `(.refl _)`).

The semantics reads `Core.funcs` in three places only (`spec/Fir/Interp.lean`): `callTarget`, for
direct calls and for indirect ones (after resolving the pointer to a function's name), and
`funcAddr`, which asks only whether a name is defined. Nothing writes it after `Core.initial`.
So the step that would close link 12 for every pass built on `CodeRel` is:

1. generalize `MRel` to cores that are equal except for `funcs`, whose entries are related by
   the code relation (same names, parameters, results, and variadicity; bodies related by
   `OpsRel L`), which `checkModule` establishes for DCE through `checkOps_sound`;
2. show that every core computation `step` runs, other than those three lookups, neither reads
   nor writes `funcs` (one lemma per computation `execFlat` and `terminate` run, the evaluators
   of every op among them), and that the lookups give related functions on related cores;
3. let the call case push related bodies instead of equal ones.

The existing `Simulation.refines` then gives refinement between the two modules' runs. The size
is in step 2: it is a statement about most of the interpreter, which is why this round did not
attempt it. Until it is done, "checked" means each optimized function is correct in the context
of the unoptimized module, and the differential tests (`tests/opt.rs`, the C corpus) are what
show the optimized module as a whole behaves.

## Next steps, by value per cost

1. **Module composition** (link 12), as above: it is what would let "checked" mean the
   optimized module is correct, and every pass built on `CodeRel` needs it.
2. **A checked `Decided` for the common case**: for a function that resolves a pointer it was
   given, `Decided` as defined can't be established from its code alone (arguments are
   arbitrary). The step is a weaker hypothesis the pass theorems can use instead: refinement for
   runs whose arguments and world answers carry provenance, plus a proved syntactic check that
   the code can't make an address-only pointer itself. Where that applies, link 11 goes from
   assumed to checked; the restriction on arguments becomes a statement about callers, to be
   discharged by module composition.
3. **The proved checker in process** (Lean's C output linked into `fir` behind `@[export]`),
   which would remove the process and the files, but not the text round trip, and would put
   Lean's runtime in the compiler. With it, the output check could be the proved code itself
   rather than a transcription tested against it. (Done: the corpus's `-O` and `FCC_PASSES`
   builds run the proved checker in CI, and every compilation runs the Rust transcription.)
4. **Checkers for the passes that delete without one**: `mem2reg` and `stackdce` delete loads,
   stores, and slots that no checker sees (the corpus numbers above). They need theorems first.
