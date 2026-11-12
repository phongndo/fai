import Fir.DceKinds

/-!
# A checker for dead code elimination

`Dce.refines` proves a *relation* between a function and its rewrite correct; a compiler pass
produces one particular rewrite. `checkFunc tgt src` decides, for the two concrete functions, a
sufficient condition for that relation: the target is the source with some ops deleted, each of
a kind `dcePerm` lets go (so `dcePerm_sound` proves it pure), with no regions, only variables as
operands, and results that no op left after it in its region (in the target) reads, at any
depth. Everything else must be equal, op for op and region for region.

`checkFunc_sound`: acceptance implies refinement, under the same side condition as
`Dce.refines` (the source is `Decided`). The checker runs in `fir-ref check-dce SRC TGT`, which
the Rust tests run on what the Rust pass produced, so each checked run of the pass is
translation-validated by a proved checker; the Rust pass itself is not proved.

The checker matches greedily: where the target's next op equals the source's (up to related
regions), they are matched; otherwise the source's op must be deletable. With SSA names that is
complete for what the pass does, and soundness doesn't depend on it.
-/

namespace Fir.Dce

/-- Whether the source op `o` may be deleted in front of target ops `t`: its kind is one
`dcePerm` deletes, it has no regions, its operands are variables, and `t` doesn't read its
results. -/
def deletable (o : Op) (t : List Op) : Bool :=
  match o with
  | .mk k res args rs _ =>
    dcePerm k == .delete && rs.isEmpty &&
      args.all (fun | .var _ => true | .hole .. => false) &&
      res.all (fun r => !opsReads r.name t)

mutual
/-- Target `ot` and source `os` are the same op, up to related regions. -/
def checkOp : Op → Op → Bool
  | .mk k res args rt loc, .mk k' res' args' rs loc' =>
    decide (k = k') && decide (res = res') && decide (args = args') && decide (loc = loc') &&
      checkRegions rt rs

def checkRegions : List Region → List Region → Bool
  | [], [] => true
  | .mk ps ot lbl :: rt, .mk ps' os lbl' :: rs =>
    decide (ps = ps') && decide (lbl = lbl') && checkOps ot os && checkRegions rt rs
  | _, _ => false

/-- Target ops `t` are source ops `s` with deletable ops left out. -/
def checkOps : List Op → List Op → Bool
  | [], [] => true
  | o' :: t', o :: s =>
    if checkOp o' o then checkOps t' s else deletable o (o' :: t') && checkOps (o' :: t') s
  | [], o :: s => deletable o [] && checkOps [] s
  | _ :: _, [] => false
end

/-- The checker for a function: the same parameters, results, and variadicity, and checked
bodies. -/
def checkFunc (tgt src : Func) : Bool :=
  decide (tgt.params = src.params) && decide (tgt.rets = src.rets) &&
    decide (tgt.variadic = src.variadic) && checkOps tgt.body.ops src.body.ops

theorem deletable_L {o : Op} {t : List Op} (h : deletable o t = true) : L [] [o] t := by
  obtain ⟨k, res, args, rs, loc⟩ := o
  simp only [deletable, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, List.all_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hk, rfl⟩, hargs⟩, hres⟩ := h
  refine ⟨_, rfl, rfl, Pure.of_kind (dcePerm_sound k hk) ?_, fun r hr => hres r hr⟩
  intro a ha
  have := hargs a ha
  cases a with
  | var n => exact ⟨n, rfl⟩
  | hole n ty => exact absurd this (by simp)

mutual
theorem checkOp_sound : ∀ (ot os : Op), checkOp ot os = true → OpRel L ot os
  | .mk k res args rt loc, .mk k' res' args' rs loc', h => by
    simp only [checkOp, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hr⟩ := h
    exact .regions (checkRegions_sound rt rs hr)

theorem checkRegions_sound : ∀ (rt rs : List Region), checkRegions rt rs = true →
    RegionsRel L rt rs
  | [], [], _ => .nil
  | .mk ps ot lbl :: rt, .mk ps' os lbl' :: rs, h => by
    simp only [checkRegions, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, ho⟩, hr⟩ := h
    exact .cons (checkOps_sound ot os ho) (checkRegions_sound rt rs hr)
  | [], _ :: _, h => by simp [checkRegions] at h
  | _ :: _, [], h => by simp [checkRegions] at h

theorem checkOps_sound : ∀ (t s : List Op), checkOps t s = true → OpsRel L t s
  | [], [], _ => .refl []
  | o' :: t', o :: s, h => by
    simp only [checkOps] at h
    split at h
    · rename_i hc
      exact .cons (checkOp_sound o' o hc) (checkOps_sound t' s h)
    · simp only [Bool.and_eq_true] at h
      exact OpsRel.rw (pt := []) (ps := [o]) (deletable_L h.1) (checkOps_sound (o' :: t') s h.2)
  | [], o :: s, h => by
    simp only [checkOps, Bool.and_eq_true] at h
    exact OpsRel.rw (pt := []) (ps := [o]) (deletable_L h.1) (checkOps_sound [] s h.2)
  | _ :: _, [], h => by simp [checkOps] at h
end

/-- **The dead code elimination checker is sound.** If `checkFunc` accepts a target for a
source function that is `Decided` in `mod`, the target refines the source, for every argument,
oracle, and monotone world. -/
theorem checkFunc_sound {mod : Module} {tgt src : Func} (h : checkFunc tgt src = true)
    (dec : src.Decided mod) : tgt.Refines mod src := by
  simp only [checkFunc, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, hr⟩, hv⟩, ho⟩ := h
  exact refines hp hr hv (checkOps_sound _ _ ho) dec

end Fir.Dce
