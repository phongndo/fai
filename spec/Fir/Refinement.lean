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

/-! ## Lists -/

/-- Two lists of equal length, related element by element. -/
def Forall2 (r : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => r a b ∧ Forall2 r as bs
  | _, _ => False

def all2 (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && all2 f as bs
  | _, _ => false

theorem all2_iff {f : α → β → Bool} {r : α → β → Prop} (h : ∀ a b, f a b = true ↔ r a b)
    {as : List α} {bs : List β} : all2 f as bs = true ↔ Forall2 r as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [all2, Forall2]
  | cons a as ih => cases bs <;> simp [all2, Forall2, h, ih]

theorem Forall2.refl {r : α → α → Prop} (h : ∀ a, r a a) (as : List α) : Forall2 r as as := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨h a, ih⟩

theorem Forall2.trans {r : α → α → Prop} (h : ∀ a b c, r a b → r b c → r a c)
    {as bs cs : List α} : Forall2 r as bs → Forall2 r bs cs → Forall2 r as cs := by
  induction as generalizing bs cs with
  | nil => cases bs <;> cases cs <;> simp [Forall2]
  | cons a as ih =>
    cases bs <;> cases cs <;> simp only [Forall2, imp_self, implies_true, false_implies]
    exact fun ⟨h₁, t₁⟩ ⟨h₂, t₂⟩ => ⟨h _ _ _ h₁ h₂, ih t₁ t₂⟩

/-! ## Bytes -/

/-- A `poison` byte may be replaced by any byte; other bytes must stay the same. -/
def Byte.Refines (t s : Byte) : Prop := s = .poison ∨ t = s

def Byte.refines (t s : Byte) : Bool := s == .poison || t == s

theorem Byte.refines_iff {t s : Byte} : t.refines s = true ↔ t.Refines s := by
  simp [Byte.refines, Byte.Refines]

theorem Byte.Refines.refl (b : Byte) : b.Refines b := .inr rfl

theorem Byte.Refines.trans {a b c : Byte} : a.Refines b → b.Refines c → a.Refines c := by
  rintro (h₁ | rfl) (h₂ | rfl)
  · exact .inl h₂
  · exact .inl h₁
  · exact .inl h₂
  · exact .inr rfl

/-! ## Runtime values -/

/-- `t.Refines s` for runtime values: the same kind and width, with `poison` replaceable by any
value of its type. -/
def RVal.Refines : RVal → RVal → Prop
  | .int w v, .int w' v' => ∃ h : w = w', Val.Refines (h ▸ v) v'
  | .ptr _, .ptr none => True
  | .ptr (some p), .ptr (some p') => p = p'
  | .bytes bs, .bytes bs' => Forall2 Byte.Refines bs bs'
  | _, _ => False

def RVal.refines : RVal → RVal → Bool
  | .int w v, .int w' v' => if h : w = w' then Val.refines (h ▸ v) v' else false
  | .ptr _, .ptr none => true
  | .ptr (some p), .ptr (some p') => p == p'
  | .bytes bs, .bytes bs' => all2 Byte.refines bs bs'
  | _, _ => false

theorem RVal.refines_iff {t s : RVal} : t.refines s = true ↔ t.Refines s := by
  cases t with
  | int w v =>
    cases s with
    | int w' v' =>
      simp only [RVal.refines, RVal.Refines]
      split
      · rename_i h
        exact ⟨fun hr => ⟨h, Val.refines_iff.mp hr⟩, fun ⟨_, hr⟩ => Val.refines_iff.mpr hr⟩
      · rename_i h
        simp [h]
    | _ => simp [RVal.refines, RVal.Refines]
  | ptr p => cases s with
    | ptr q => cases p <;> cases q <;> simp [RVal.refines, RVal.Refines]
    | _ => simp [RVal.refines, RVal.Refines]
  | bytes bs => cases s with
    | bytes bs' => simp [RVal.refines, RVal.Refines, all2_iff (fun _ _ => Byte.refines_iff)]
    | _ => simp [RVal.refines, RVal.Refines]

theorem RVal.Refines.refl (v : RVal) : v.Refines v := by
  cases v with
  | int w v => exact ⟨rfl, Val.Refines.refl v⟩
  | ptr p => cases p <;> simp [RVal.Refines]
  | bytes bs => exact Forall2.refl Byte.Refines.refl bs

theorem RVal.Refines.trans {a b c : RVal} : a.Refines b → b.Refines c → a.Refines c := by
  intro h₁ h₂
  cases a <;> cases b <;> cases c <;> simp only [RVal.Refines] at h₁ h₂ ⊢
  case int.int.int =>
    obtain ⟨hab, h₁⟩ := h₁
    obtain ⟨hbc, h₂⟩ := h₂
    subst hab hbc
    exact ⟨rfl, Val.Refines.trans h₁ h₂⟩
  case bytes.bytes.bytes => exact Forall2.trans (r := Byte.Refines) (fun _ _ _ => Byte.Refines.trans) h₁ h₂
  all_goals
    first
    | trivial
    | contradiction
    | (rename_i p q r; cases p <;> cases q <;> cases r <;>
        simp_all)

/-- Element-wise refinement of value lists of equal length. -/
abbrev RVal.RefinesList := Forall2 RVal.Refines

def RVal.refinesList : List RVal → List RVal → Bool := all2 RVal.refines

theorem RVal.refinesList_iff {ts ss : List RVal} :
    RVal.refinesList ts ss = true ↔ RVal.RefinesList ts ss :=
  all2_iff (fun _ _ => RVal.refines_iff)

theorem RVal.RefinesList.refl (vs : List RVal) : RVal.RefinesList vs vs :=
  Forall2.refl RVal.Refines.refl vs

theorem RVal.RefinesList.trans {as bs cs : List RVal} :
    RVal.RefinesList as bs → RVal.RefinesList bs cs → RVal.RefinesList as cs :=
  Forall2.trans (r := RVal.Refines) (fun _ _ _ => RVal.Refines.trans)

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
