import Fir.Basic

/-!
# Refinement

`t ⊑ s` ("t refines s") means `t` may replace `s`: everything `t` can do, `s` could already do.
This is FIR's definition of a correct transformation. Two loopholes give optimizations their
power:

* where `s` is `poison`, `t` may be any value;
* where `s` has UB, `t` may do anything.

This module depends only on the value types, not on the interpreter or any proof tactics, so
certificate checkers can import it alone. Each relation comes as a `Prop` for proofs, a `Bool`
function that checkers can run, and a theorem that the two agree. Each `Prop` is a preorder
(reflexive and transitive), so rewrites compose.

Program-level refinement, which needs the interpreter, is in `Fir.Behavior`.
-/

namespace Fir

/-! ## Values -/

/-- `t.Refines s`: value `t` may replace value `s`. -/
def Val.Refines : Val w → Val w → Prop
  | _, .poison => True
  | .bits a, .bits b => a = b
  | .poison, .bits _ => False

def Val.refines : Val w → Val w → Bool
  | _, .poison => true
  | .bits a, .bits b => a == b
  | .poison, .bits _ => false

theorem Val.refines_iff {t s : Val w} : t.refines s = true ↔ t.Refines s := by
  cases t <;> cases s <;> simp [Val.refines, Val.Refines]

@[refl] theorem Val.Refines.refl (v : Val w) : v.Refines v := by
  cases v <;> simp [Val.Refines]

theorem Val.Refines.trans {a b c : Val w} : a.Refines b → b.Refines c → a.Refines c := by
  cases a <;> cases b <;> cases c <;> simp_all [Val.Refines]

/-! ## Op outcomes -/

/-- `t.Refines s` for the outcome of one op. UB in `s` allows anything; a trap must be kept,
with the same reason. -/
def OpOut.Refines : OpOut w → OpOut w → Prop
  | _, .ub _ => True
  | .ok v, .ok v' => v.Refines v'
  | .trap r, .trap r' => r = r'
  | _, _ => False

def OpOut.refines : OpOut w → OpOut w → Bool
  | _, .ub _ => true
  | .ok v, .ok v' => v.refines v'
  | .trap r, .trap r' => r == r'
  | _, _ => false

theorem OpOut.refines_iff {t s : OpOut w} : t.refines s = true ↔ t.Refines s := by
  cases t <;> cases s <;> simp [OpOut.refines, OpOut.Refines, Val.refines_iff]

@[refl] theorem OpOut.Refines.refl (o : OpOut w) : o.Refines o := by
  cases o <;> simp [OpOut.Refines, Val.Refines.refl]

theorem OpOut.Refines.trans {a b c : OpOut w} : a.Refines b → b.Refines c → a.Refines c := by
  intro h₁ h₂
  cases a <;> cases b <;> cases c <;> simp only [OpOut.Refines] at h₁ h₂ ⊢
  all_goals first | trivial | contradiction | exact Val.Refines.trans h₁ h₂ | exact h₁.trans h₂

/-! ## Runtime values -/

/-- `t.Refines s` for values whose widths are only known at runtime: same width, and `t` refines
`s` as a value. -/
def RVal.Refines (t s : RVal) : Prop :=
  ∃ h : t.w = s.w, Val.Refines (h ▸ t.v) s.v

def RVal.refines (t s : RVal) : Bool :=
  if h : t.w = s.w then Val.refines (h ▸ t.v) s.v else false

theorem RVal.refines_iff {t s : RVal} : t.refines s = true ↔ t.Refines s := by
  unfold RVal.refines RVal.Refines
  split
  · rename_i h
    exact ⟨fun hr => ⟨h, Val.refines_iff.mp hr⟩, fun ⟨_, hr⟩ => Val.refines_iff.mpr hr⟩
  · rename_i h
    simp [h]

@[refl] theorem RVal.Refines.refl (v : RVal) : v.Refines v := ⟨rfl, Val.Refines.refl _⟩

theorem RVal.Refines.trans {a b c : RVal} : a.Refines b → b.Refines c → a.Refines c := by
  obtain ⟨aw, av⟩ := a
  obtain ⟨bw, bv⟩ := b
  obtain ⟨cw, cv⟩ := c
  intro ⟨hab, h₁⟩ ⟨hbc, h₂⟩
  dsimp only at hab hbc h₁ h₂
  subst hab hbc
  exact ⟨rfl, Val.Refines.trans h₁ h₂⟩

/-- Element-wise refinement of value lists of equal length. -/
def RVal.RefinesList : List RVal → List RVal → Prop
  | [], [] => True
  | t :: ts, s :: ss => t.Refines s ∧ RefinesList ts ss
  | _, _ => False

def RVal.refinesList : List RVal → List RVal → Bool
  | [], [] => true
  | t :: ts, s :: ss => t.refines s && refinesList ts ss
  | _, _ => false

theorem RVal.refinesList_iff {ts ss : List RVal} :
    RVal.refinesList ts ss = true ↔ RVal.RefinesList ts ss := by
  induction ts generalizing ss with
  | nil => cases ss <;> simp [refinesList, RefinesList]
  | cons t ts ih => cases ss <;> simp [refinesList, RefinesList, RVal.refines_iff, ih]

theorem RVal.RefinesList.refl (vs : List RVal) : RVal.RefinesList vs vs := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨RVal.Refines.refl v, ih⟩

theorem RVal.RefinesList.trans {as bs cs : List RVal} :
    RVal.RefinesList as bs → RVal.RefinesList bs cs → RVal.RefinesList as cs := by
  induction as generalizing bs cs with
  | nil => cases bs <;> cases cs <;> simp [RefinesList]
  | cons a as ih =>
    cases bs <;> cases cs <;> simp only [RefinesList, imp_self, implies_true, false_implies]
    exact fun ⟨h₁, t₁⟩ ⟨h₂, t₂⟩ => ⟨RVal.Refines.trans h₁ h₂, ih t₁ t₂⟩

/-! ## Function behaviors -/

/-- `t.Refines s` for the observable behavior of a run. -/
def Behavior.Refines : Behavior → Behavior → Prop
  | _, .ub _ => True
  | .ret vs, .ret vs' => RVal.RefinesList vs vs'
  | .trap r, .trap r' => r = r'
  | .diverge, .diverge => True
  | .hole n, .hole n' => n = n'
  | .stuck _, .stuck _ => True
  | _, _ => False

def Behavior.refines : Behavior → Behavior → Bool
  | _, .ub _ => true
  | .ret vs, .ret vs' => RVal.refinesList vs vs'
  | .trap r, .trap r' => r == r'
  | .diverge, .diverge => true
  | .hole n, .hole n' => n == n'
  | .stuck _, .stuck _ => true
  | _, _ => false

theorem Behavior.refines_iff {t s : Behavior} : t.refines s = true ↔ t.Refines s := by
  cases t <;> cases s <;> simp [Behavior.refines, Behavior.Refines, RVal.refinesList_iff]

@[refl] theorem Behavior.Refines.refl (b : Behavior) : b.Refines b := by
  cases b <;> simp [Behavior.Refines, RVal.RefinesList.refl]

theorem Behavior.Refines.trans {a b c : Behavior} :
    a.Refines b → b.Refines c → a.Refines c := by
  intro h₁ h₂
  cases a <;> cases b <;> cases c <;> simp only [Behavior.Refines] at h₁ h₂ ⊢
  all_goals first | trivial | contradiction | exact RVal.RefinesList.trans h₁ h₂ | exact h₁.trans h₂

end Fir
