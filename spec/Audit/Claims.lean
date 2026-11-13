import Fir

/-!
# The registered assurance claims

The theorems `fir-audit` (`spec/Audit.lean`) checks, with what each guarantees. Registering a
claim is a statement that its theorem is part of what the project relies on; the audit then
watches its statement, assumptions, axioms, and semantic dependencies (`docs/assurance/
proofs.lock.json`). Supporting lemmas are theorems the audit would otherwise flag (a bold
headline, or a conclusion in a tracked relation) that are steps toward a claim, not claims.

**Bindings** write out, in this file, the statements the Rust side was built against; each is
proved by its claim, and the audit checks that the two statements are the same expression.
-/

namespace Fir.Audit

/-- An assurance claim: a theorem, its role, a sentence on what it guarantees, the axioms beyond
the standard three it may use (with the reason), and the binding that writes out its statement
for the Rust side, if one does. -/
structure Claim where
  name : Lean.Name
  role : String
  summary : String
  axioms : List (Lean.Name × String) := []
  binding : Option Lean.Name := none

namespace Bindings

/-- What `compiler/ir/src/generated/contracts.rs` cites as `DCE_THEOREM`: every kind the
classification deletes is pure. -/
theorem dce_classification : ∀ k, Fir.Dce.dcePerm k = .delete → Fir.Dce.PureKind k :=
  Fir.Dce.dcePerm_sound

/-- What `fir-ref check-dce` relies on: acceptance implies refinement in the source module. -/
theorem dce_checker : ∀ {mod : Module} {tgt src : Func}, Fir.Dce.checkFunc tgt src = true →
    src.Decided mod → tgt.Refines mod src :=
  Fir.Dce.checkFunc_sound

/-- What `fir-ref check-dce`'s counting checker relies on: it is the proved checker. -/
theorem dce_checker_linear : ∀ (tgt src : Func), Fir.Dce.checkFuncL tgt src = Fir.Dce.checkFunc tgt src :=
  Fir.Dce.checkFuncL_eq

/-- What `fir-ref check-dce` accepts on, and what an acceptance gives: for every name, both modules
have a function by that name or neither does, and the target's refines the source's in the
source module if the source's is `Decided` there. -/
theorem dce_module_checker : ∀ {tgt src : Module}, Fir.Dce.checkModule tgt src = true →
    ∀ name, Option.Rel (fun t s => s.Decided src → t.Refines src s) (tgt.find? name)
      (src.find? name) :=
  Fir.Dce.checkModule_sound

end Bindings

def claims : List Claim := [
  { name := ``Fir.Dce.dcePerm_sound, role := "binding: Rust permissions",
    summary := "Every op kind the generated DCE contract lets the Rust pass delete is pure (PureKind): no call, no stack allocation, not a terminator, and its computation only reads the core and fails only by UB or getting stuck.",
    binding := some ``Bindings.dce_classification },
  { name := ``Fir.Dce.checkFunc_sound, role := "binding: proved checker",
    summary := "If the DCE checker run by fir-ref check-dce accepts a target function for a Decided source function, the target refines the source in the source module.",
    binding := some ``Bindings.dce_checker },
  { name := ``Fir.Dce.checkFuncL_eq, role := "binding: proved checker (counting)",
    summary := "The DCE checker fir-ref check-dce runs (checkFuncL: read counts instead of a scan of the rest of the region per deleted op) gives the same verdict as checkFunc on every pair of functions, so checkFunc_sound holds for it.",
    binding := some ``Bindings.dce_checker_linear },
  { name := ``Fir.Dce.checkModule_sound, role := "binding: proved checker (modules)",
    summary := "If checkModule (what fir-ref check-dce accepts on) accepts, then for every name the target module has a function by that name exactly when the source does, and the target's refines the source's in the source module if the source's is Decided there. Not module refinement: each target function's calls go to the source's functions.",
    binding := some ``Bindings.dce_module_checker },
  { name := ``Fir.Dce.refines, role := "pass correctness",
    summary := "DCE: deleting pure ops whose results no later op of their region reads, anywhere in a function, gives a function that refines it in the module, if the source is Decided." },
  { name := ``Fir.Dce.freeze_changes_core, role := "counterexample",
    summary := "freeze of poison changes the core (it consults the oracle), although its declaration lists no effects: an effects declaration is not evidence of purity." },
  { name := ``Fir.Dse.refines, role := "pass correctness",
    summary := "DSE: deleting a store that the next op overwrites through the same pointer variable with a same-size scalar store refines the function, if the source is Decided." },
  { name := ``Fir.Fwd.refines, role := "pass correctness",
    summary := "Store-to-load forwarding: a load right after a store of its type through the same pointer variable may read the stored value instead, if the source is Decided." },
  { name := ``Fir.CopyProp.refines, role := "pass correctness",
    summary := "Copy propagation through straight-line code (up to the first op with regions or a call) refines the function, if the source is Decided." },
  { name := ``Fir.Lower.Proof.Expand.refines, role := "lowering correctness",
    summary := "The HFIR lowering's expansion pass (checked arithmetic, ptr.field, ptr.index) refines each function, given variable operands, no pass temporaries, and a Decided source." },
  { name := ``Fir.Lower.Proof.lowerFunc_refines, role := "lowering correctness (partial)",
    summary := "The whole lowering of a function refines it where scalarizing and lowering cf.try change nothing. Scalarization, cf.try lowering, and module composition are not proved." },
  { name := ``Fir.Simulation.refines, role := "proof framework",
    summary := "A lockstep simulation from every related start gives refinement of Decided functions." },
  { name := ``Fir.SimulationS.refines, role := "proof framework",
    summary := "A simulation with stuttering gives refinement of Decided functions." },
  { name := ``Fir.Rules.mul_two, role := "rewrite rule",
    summary := "int.mul.wrap x, 2 is refined by int.add.wrap x, x, for every width and poison." },
  { name := ``Fir.Rules.add_zero, role := "rewrite rule",
    summary := "int.add with 0 is refined by its operand, for every overflow modifier." },
  { name := ``Fir.Rules.add_nsw_one_sgt, role := "rewrite rule",
    summary := "int.cmp.sgt (int.add.nsw x, 1), x is refined by true at widths of at least 2." }
,
  { name := ``Fir.Dce.float_pure, role := "pass correctness (DCE permission)",
    summary := "The float ops that can't trap (all but float.to_int.*.trap) are pure: a NaN result is the oracle's choice from the op and its operands, so computing one only reads the core." },
  { name := ``Fir.Dce.evalFloat_oracle, role := "float semantics",
    summary := "Every float op, traps included, depends on the core only through the oracle and leaves the core as it was, so within a run it is a function of its operands." },
  { name := ``Fir.Float.add_comm, role := "float semantics law",
    summary := "Float addition commutes, up to the NaN payload the oracle picks." },
  { name := ``Fir.Float.mul_comm, role := "float semantics law",
    summary := "Float multiplication commutes, up to the NaN payload the oracle picks." },
  { name := ``Fir.Float.neg_neg, role := "float semantics law",
    summary := "float.neg is an involution on bits." },
  { name := ``Fir.Float.cvt_cvt, role := "float semantics law",
    summary := "Widening, then narrowing back, gives every non-NaN value back, whatever NaN choices the oracle makes." },
  { name := ``Fir.Float.ext_trunc, role := "float semantics law",
    summary := "float.ext then float.trunc is the identity on f32, NaNs aside." },
  { name := ``Fir.Float.truncInt_ofInt, role := "float semantics law",
    summary := "Integers of at most m + 1 bits convert to a float and back (toward zero) unchanged, when the format's range holds them." },
  { name := ``Fir.Float.round_decode, role := "float semantics law",
    summary := "Rounding a representable value gives its bits back." },
  { name := ``Fir.Float.decode_round, role := "float semantics law",
    summary := "A representable number of units rounds to bits that decode to it." },
  { name := ``Fir.AArch64.fpAlu_allowed, role := "AArch64 float semantics",
    summary := "fadd, fsub, fmul, and fdiv give results float.add and friends allow (for some oracle answer)." },
  { name := ``Fir.AArch64.fpSqrt_allowed, role := "AArch64 float semantics",
    summary := "fsqrt gives a result float.sqrt allows." },
  { name := ``Fir.AArch64.fpMulAdd_allowed, role := "AArch64 float semantics",
    summary := "fmadd gives a result float.fma allows, its addend last." },
  { name := ``Fir.AArch64.fpConvert_allowed, role := "AArch64 float semantics",
    summary := "fcvt gives a result float.ext and float.trunc allow." },
  { name := ``Fir.AArch64.fcvtz_sat, role := "AArch64 float semantics",
    summary := "fcvtzs and fcvtzu are float.to_int.s.sat and float.to_int.u.sat." },
  { name := ``Fir.AArch64.floatBin_arm, role := "AArch64 float semantics",
    summary := "Under Arm's NaN choice, float.add and friends are fadd and friends." },
  { name := ``Fir.AArch64.floatSqrt_arm, role := "AArch64 float semantics",
    summary := "Under Arm's NaN choice, float.sqrt is fsqrt." },
  { name := ``Fir.AArch64.floatFma_arm, role := "AArch64 float semantics",
    summary := "Under Arm's NaN choice, float.fma a, b, c is fmadd with addend c." },
  { name := ``Fir.AArch64.floatExt_arm, role := "AArch64 float semantics",
    summary := "Under Arm's NaN choice, float.ext and float.trunc are fcvt." },
  { name := ``Fir.AArch64.roundTrip, role := "AArch64 C ABI",
    summary := "A struct or array passed in registers (an HFA or up to 16 bytes) arrives with its defined bytes exactly: its pieces, each loaded into a register and stored back, are its bytes; a word of eight fragments of one pointer stays that pointer. That native code passes exactly these pieces where Fir.AArch64.argLocs says is tested (the ABI torture test), not proved." },
  { name := ``Fir.AArch64.pieces_flatten, role := "AArch64 C ABI",
    summary := "The register pieces of a composite passed in registers (8-byte words, or an HFA's members), joined, are its bytes." },
  { name := ``Fir.AArch64.arrives, role := "AArch64 C ABI",
    summary := "A struct or array passed in registers arrives with every defined byte in place even when its pieces are partly undefined (padding or poison leaves): any words that hold its pieces (Word.Holds), stored back, give as many bytes with each defined one unchanged." },
  { name := ``Fir.AArch64.ptrLeaf_inReg, role := "AArch64 C ABI",
    summary := "In a composite passed as x-register words that doesn't split a pointer (Ty.splitsPtr, which instruction selection refuses), a pointer leaf's register holds that pointer, provenance included, whatever the other pieces hold." },
  { name := ``Fir.AArch64.Word.holds_fill, role := "AArch64 C ABI",
    summary := "The machine's word for a piece (Word.fill, the shape of AArch64Machine's wordOfBytes: an arbitrary choice for poison and stray fragment bytes) holds it: a whole pointer's eight fragments are that pointer, and every defined byte is in the register. That wordOfBytes is this function is by inspection, not proved." }
]

/-- Theorems the audit would flag that are steps toward claims. -/
def supporting : List Lean.Name := [
  ``Fir.step_space, ``Fir.step_trace, ``Fir.Behavior.refines_after_ub,
  ``Fir.CopyProp.sim, ``Fir.Dce.sim, ``Fir.Dse.sim, ``Fir.Fwd.sim, ``Fir.Lower.Proof.sim,
  ``Fir.Dce.copy_pure, ``Fir.Dce.refines_copy, ``Fir.Dce.refines_copy_in_block,
  ``Fir.LowerBits.flag_ext, ``Fir.StackRel.lookup,
  ``Fir.Behavior.Refines.of_extends, ``Fir.Behavior.Refines.of_prefix,
  ``Fir.Behavior.Refines.refl, ``Fir.Behavior.Refines.trans,
  ``Fir.Func.Refines.refl, ``Fir.Func.Refines.trans,
  ``Fir.OpOut.Refines.refl, ``Fir.OpOut.Refines.trans,
  ``Fir.Lower.Proof.ovf_runs, ``Fir.Lower.Proof.refines_of_rel, ``Fir.Dce.floatPure_kind,
  ``Fir.Dce.checkFuncL_sound,
  ``Fir.AArch64.Word.bytes_ofBytes]

end Fir.Audit
