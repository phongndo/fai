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

mutual
  /-- `t.Refines s` for runtime values: the same kind and width, with `poison` replaceable by any
  value of its type. Aggregates refine part by part. -/
  def RVal.Refines : RVal → RVal → Prop
    | .int w v, .int w' v' => ∃ h : w = w', Val.Refines (h ▸ v) v'
    | .ptr _, .ptr none => True
    | .ptr (some p), .ptr (some p') => p = p'
    | .bytes bs, .bytes bs' => Forall2 Byte.Refines bs bs'
    | .agg ts, .agg ss => RVal.RefinesParts ts ss
    | _, _ => False
  /-- `Forall2 RVal.Refines`, spelled out for the nested recursion (`RVal.refinesParts_eq`). -/
  def RVal.RefinesParts : List RVal → List RVal → Prop
    | [], [] => True
    | t :: ts, s :: ss => RVal.Refines t s ∧ RVal.RefinesParts ts ss
    | _, _ => False
end

mutual
  def RVal.refines : RVal → RVal → Bool
    | .int w v, .int w' v' => if h : w = w' then Val.refines (h ▸ v) v' else false
    | .ptr _, .ptr none => true
    | .ptr (some p), .ptr (some p') => p == p'
    | .bytes bs, .bytes bs' => all2 Byte.refines bs bs'
    | .agg ts, .agg ss => RVal.refinesParts ts ss
    | _, _ => false
  def RVal.refinesParts : List RVal → List RVal → Bool
    | [], [] => true
    | t :: ts, s :: ss => RVal.refines t s && RVal.refinesParts ts ss
    | _, _ => false
end

theorem RVal.refinesParts_eq : ∀ (ts ss : List RVal), RVal.RefinesParts ts ss = Forall2 RVal.Refines ts ss
  | [], [] => rfl
  | t :: ts, s :: ss => by simp only [RVal.RefinesParts, Forall2, RVal.refinesParts_eq ts ss]
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

mutual
  theorem RVal.refines_iff : ∀ {t s : RVal}, t.refines s = true ↔ t.Refines s
    | .int w v, .int w' v' => by
      simp only [RVal.refines, RVal.Refines]
      split
      · rename_i h
        exact ⟨fun hr => ⟨h, Val.refines_iff.mp hr⟩, fun ⟨_, hr⟩ => Val.refines_iff.mpr hr⟩
      · rename_i h
        simp [h]
    | .ptr p, .ptr q => by cases p <;> cases q <;> simp [RVal.refines, RVal.Refines]
    | .bytes bs, .bytes bs' => by
      simp [RVal.refines, RVal.Refines, all2_iff (fun _ _ => Byte.refines_iff)]
    | .agg ts, .agg ss => by
      simp only [RVal.refines, RVal.Refines]; exact RVal.refinesParts_iff
    | .int .., .ptr _ | .int .., .bytes _ | .int .., .agg _ | .ptr _, .int .. | .ptr _, .bytes _
    | .ptr _, .agg _ | .bytes _, .int .. | .bytes _, .ptr _ | .bytes _, .agg _ | .agg _, .int ..
    | .agg _, .ptr _ | .agg _, .bytes _ => by simp [RVal.refines, RVal.Refines]
  theorem RVal.refinesParts_iff : ∀ {ts ss : List RVal},
      RVal.refinesParts ts ss = true ↔ RVal.RefinesParts ts ss
    | [], [] => by simp [RVal.refinesParts, RVal.RefinesParts]
    | t :: ts, s :: ss => by
      simp only [RVal.refinesParts, RVal.RefinesParts, Bool.and_eq_true]
      exact and_congr RVal.refines_iff RVal.refinesParts_iff
    | [], _ :: _ | _ :: _, [] => by simp [RVal.refinesParts, RVal.RefinesParts]
end

mutual
  theorem RVal.Refines.refl : ∀ (v : RVal), v.Refines v
    | .int w v => ⟨rfl, Val.Refines.refl v⟩
    | .ptr p => by cases p <;> simp [RVal.Refines]
    | .bytes bs => Forall2.refl Byte.Refines.refl bs
    | .agg vs => by simp only [RVal.Refines]; exact RVal.RefinesParts.refl vs
  theorem RVal.RefinesParts.refl : ∀ (vs : List RVal), RVal.RefinesParts vs vs
    | [] => trivial
    | v :: vs => ⟨RVal.Refines.refl v, RVal.RefinesParts.refl vs⟩
end

mutual
  theorem RVal.Refines.trans : ∀ {a b c : RVal}, a.Refines b → b.Refines c → a.Refines c
    | .agg as, .agg bs, .agg cs, h₁, h₂ => by
      simp only [RVal.Refines] at h₁ h₂ ⊢; exact RVal.RefinesParts.trans h₁ h₂
    | .int .., .int .., .int .., h₁, h₂ => by
      simp only [RVal.Refines] at h₁ h₂ ⊢
      obtain ⟨hab, h₁⟩ := h₁
      obtain ⟨hbc, h₂⟩ := h₂
      subst hab hbc
      exact ⟨rfl, Val.Refines.trans h₁ h₂⟩
    | .bytes _, .bytes _, .bytes _, h₁, h₂ => by
      simp only [RVal.Refines] at h₁ h₂ ⊢
      exact Forall2.trans (r := Byte.Refines) (fun _ _ _ => Byte.Refines.trans) h₁ h₂
    | .ptr p, .ptr q, .ptr r, h₁, h₂ => by
      cases p <;> cases q <;> cases r <;> simp_all [RVal.Refines]
    | .int .., .ptr _, _, h₁, _ | .int .., .bytes _, _, h₁, _ | .int .., .agg _, _, h₁, _
    | .ptr _, .int .., _, h₁, _ | .ptr _, .bytes _, _, h₁, _ | .ptr _, .agg _, _, h₁, _
    | .bytes _, .int .., _, h₁, _ | .bytes _, .ptr _, _, h₁, _ | .bytes _, .agg _, _, h₁, _
    | .agg _, .int .., _, h₁, _ | .agg _, .ptr _, _, h₁, _ | .agg _, .bytes _, _, h₁, _ => by
      cases h₁
    | .int .., .int .., .ptr _, _, h₂ | .int .., .int .., .bytes _, _, h₂
    | .int .., .int .., .agg _, _, h₂ | .ptr _, .ptr _, .int .., _, h₂
    | .ptr _, .ptr (some _), .bytes _, _, h₂ | .ptr _, .ptr (some _), .agg _, _, h₂
    | .ptr _, .ptr none, .bytes _, _, h₂ | .ptr _, .ptr none, .agg _, _, h₂
    | .bytes _, .bytes _, .int .., _, h₂ | .bytes _, .bytes _, .ptr _, _, h₂
    | .bytes _, .bytes _, .agg _, _, h₂ | .agg _, .agg _, .int .., _, h₂
    | .agg _, .agg _, .ptr _, _, h₂ | .agg _, .agg _, .bytes _, _, h₂ => by
      simp [RVal.Refines] at h₂
  theorem RVal.RefinesParts.trans : ∀ {as bs cs : List RVal},
      RVal.RefinesParts as bs → RVal.RefinesParts bs cs → RVal.RefinesParts as cs
    | [], [], [], _, _ => trivial
    | _ :: _, _ :: _, _ :: _, ⟨h₁, t₁⟩, ⟨h₂, t₂⟩ =>
      ⟨RVal.Refines.trans h₁ h₂, RVal.RefinesParts.trans t₁ t₂⟩
    | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => by cases h
    | [], [], _ :: _, _, h | _ :: _, _ :: _, [], _, h => by cases h
end

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

/-! ## Outcomes -/

/-- `t.Refines s` for how a run ends. A source that is UB or stuck (malformed; verified programs
never get stuck) allows anything. An `ambiguous` run has an unknown behavior: as a target it
refines only those, and as a source nothing refines it. So refinement is not reflexive on
`ambiguous`. -/
def Outcome.Refines : Outcome → Outcome → Prop
  | _, .ub _ => True
  | _, .stuck _ => True
  | .ret vs, .ret vs' => RVal.RefinesList vs vs'
  | .threw v, .threw v' => RVal.Refines v v'
  | .trap r, .trap r' => r = r'
  | .diverge, .diverge => True
  | .hole n, .hole n' => n = n'
  | _, _ => False

def Outcome.refines : Outcome → Outcome → Bool
  | _, .ub _ => true
  | _, .stuck _ => true
  | .ret vs, .ret vs' => RVal.refinesList vs vs'
  | .threw v, .threw v' => RVal.refines v v'
  | .trap r, .trap r' => r == r'
  | .diverge, .diverge => true
  | .hole n, .hole n' => n == n'
  | _, _ => false

theorem Outcome.refines_iff {t s : Outcome} : t.refines s = true ↔ t.Refines s := by
  cases t <;> cases s <;> simp [Outcome.refines, Outcome.Refines, RVal.refinesList_iff,
    RVal.refines_iff]

theorem Outcome.Refines.refl (b : Outcome) (h : b ≠ .ambiguous) : b.Refines b := by
  cases b <;> simp_all [Outcome.Refines, RVal.RefinesList.refl, RVal.Refines.refl]

/-- A source outcome that every target outcome refines: UB, or stuck. -/
def Outcome.Absorbing : Outcome → Prop
  | .ub _ | .stuck _ => True
  | _ => False

theorem Outcome.Refines.of_absorbing {t s : Outcome} (h : s.Absorbing) : t.Refines s := by
  cases s <;> cases t <;> simp_all [Outcome.Absorbing, Outcome.Refines]

theorem Outcome.Refines.trans {a b c : Outcome} :
    a.Refines b → b.Refines c → a.Refines c := by
  intro h₁ h₂
  cases a <;> cases b <;> cases c <;> simp only [Outcome.Refines] at h₁ h₂ ⊢
  all_goals first
    | trivial | contradiction | exact RVal.RefinesList.trans h₁ h₂
    | exact RVal.Refines.trans h₁ h₂ | exact h₁.trans h₂

theorem Outcome.Absorbing.of_refines {t s : Outcome} (ht : t.Absorbing) (h : t.Refines s) :
    s.Absorbing := by
  cases t <;> cases s <;> simp_all [Outcome.Absorbing, Outcome.Refines]

/-! ## Events -/

/-- `t.Refines s` for events: a call to the same function, with arguments that refine the
source's (any value where the source passed `poison`), and the same results. The results are
what the environment returned, so they are inputs to the rest of the run, not outputs: the source
must have seen exactly them. -/
def Event.Refines (t s : Event) : Prop :=
  t.callee = s.callee ∧ RVal.RefinesList t.args s.args ∧ t.results = s.results

def Event.refines (t s : Event) : Bool :=
  t.callee == s.callee && RVal.refinesList t.args s.args && t.results == s.results

theorem Event.refines_iff {t s : Event} : t.refines s = true ↔ t.Refines s := by
  simp [Event.refines, Event.Refines, RVal.refinesList_iff, and_assoc]

theorem Event.Refines.refl (e : Event) : e.Refines e :=
  ⟨rfl, RVal.RefinesList.refl _, rfl⟩

theorem Event.Refines.trans {a b c : Event} : a.Refines b → b.Refines c → a.Refines c :=
  fun ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩ => ⟨h1.trans h1', RVal.RefinesList.trans h2 h2', h3.trans h3'⟩

/-- Event-by-event refinement of traces of equal length. -/
abbrev Events.Refines := Forall2 Event.Refines

def Events.refines : List Event → List Event → Bool := all2 Event.refines

theorem Events.refines_iff {ts ss : List Event} : Events.refines ts ss = true ↔ Events.Refines ts ss :=
  all2_iff (fun _ _ => Event.refines_iff)

theorem Events.Refines.refl (es : List Event) : Events.Refines es es :=
  Forall2.refl Event.Refines.refl es

theorem Events.Refines.trans {as bs cs : List Event} :
    Events.Refines as bs → Events.Refines bs cs → Events.Refines as cs :=
  Forall2.trans (r := Event.Refines) (fun _ _ _ => Event.Refines.trans)

theorem Forall2.length_eq {r : α → β → Prop} : ∀ {as : List α} {bs : List β},
    Forall2 r as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => by simp [Forall2.length_eq h]

/-- Lists related to a concatenation split the same way. -/
theorem Forall2.split {r : α → β → Prop} : ∀ {as : List α} {bs cs : List β},
    Forall2 r as (bs ++ cs) → ∃ as1 as2, as = as1 ++ as2 ∧ Forall2 r as1 bs ∧ Forall2 r as2 cs
  | as, [], cs, h => ⟨[], as, rfl, trivial, h⟩
  | a :: as, b :: bs, cs, ⟨hab, h⟩ => by
    obtain ⟨as1, as2, rfl, h1, h2⟩ := Forall2.split (bs := bs) h
    exact ⟨a :: as1, as2, rfl, ⟨hab, h1⟩, h2⟩
  | [], _ :: _, _, h => h.elim

theorem Forall2.append {r : α → β → Prop} : ∀ {as1 as2 : List α} {bs1 bs2 : List β},
    Forall2 r as1 bs1 → Forall2 r as2 bs2 → Forall2 r (as1 ++ as2) (bs1 ++ bs2)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, ⟨h, t⟩, h2 => ⟨h, Forall2.append t h2⟩

/-- Related lists are related at every index. -/
theorem Forall2.getElem? {r : α → β → Prop} : ∀ {as : List α} {bs : List β},
    Forall2 r as bs → ∀ {i : Nat} {b : β}, bs[i]? = some b → ∃ a, as[i]? = some a ∧ r a b
  | [], [], _, _, _, e => by simp at e
  | a :: _, _ :: _, ⟨hab, _⟩, 0, _, e => by simp at e; subst e; exact ⟨a, rfl, hab⟩
  | _ :: _, _ :: _, ⟨_, h⟩, i + 1, _, e => by simpa using Forall2.getElem? h (i := i) (by simpa using e)

theorem getElem?_append_some {l1 l2 : List α} {i : Nat} {x : α} (h : l1[i]? = some x) :
    (l1 ++ l2)[i]? = some x := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1, h]

/-! ## Behaviors -/

/-- `t.Refines s` for whole runs. The traces match event by event and the outcomes refine, except
that a source that is UB or stuck after some events lets the target do anything once it has
matched those events: UB is not time travel past observable events, so the target must still
perform every event the source performed before its UB. A run with infinitely many events refines
one with infinitely many events, matching each, or a source that is UB after some of them; it
never refines a finite run that doesn't end in UB, even one that diverges silently. -/
def Behavior.Refines : Behavior → Behavior → Prop
  | .fin et ot, .fin es os =>
    (Events.Refines et es ∧ ot.Refines os) ∨
    (os.Absorbing ∧ ∃ pre post, et = pre ++ post ∧ Events.Refines pre es)
  | .inf et, .fin es os => os.Absorbing ∧ ∀ i e, es[i]? = some e → (et i).Refines e
  | .fin .., .inf _ => False
  | .inf et, .inf es => ∀ i, (et i).Refines (es i)

/-- Refinement is reflexive except on runs that end `ambiguous`. -/
theorem Behavior.Refines.refl : ∀ (b : Behavior), (∀ es, b ≠ .fin es .ambiguous) → b.Refines b
  | .fin es o, h => .inl ⟨Events.Refines.refl es, Outcome.Refines.refl o fun e => h es (by rw [e])⟩
  | .inf _, _ => fun _ => Event.Refines.refl _

/-- The target matches the source's events, then the source is UB or stuck. -/
theorem Behavior.Refines.of_prefix {t : Behavior} {es : List Event} {o : Outcome}
    (ho : o.Absorbing)
    (h : match t with
      | .fin et _ => ∃ pre post, et = pre ++ post ∧ Events.Refines pre es
      | .inf et => ∀ i e, es[i]? = some e → (et i).Refines e) :
    t.Refines (.fin es o) := by
  cases t with
  | fin et ot => exact .inr ⟨ho, h⟩
  | inf et => exact ⟨ho, h⟩

/-- UB is not time travel: a target that skips an event the source performed before its UB does
not refine it. -/
theorem Behavior.not_refines_skipped_event (e : Event) (o : Outcome) (k : UBKind) :
    ¬ (Behavior.fin [] o).Refines (.fin [e] (.ub k)) := by
  rintro (⟨h, -⟩ | ⟨-, pre, post, hpp, h⟩)
  · exact h
  · obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hpp.symm
    exact h

/-- After the source's events, UB lets the target do anything, even run forever with events. -/
theorem Behavior.refines_after_ub (es : List Event) (k : UBKind) (t : Behavior)
    (h : match t with
      | .fin et _ => es <+: et
      | .inf et => ∀ i e, es[i]? = some e → et i = e) :
    t.Refines (.fin es (.ub k)) := by
  cases t with
  | fin et ot =>
    obtain ⟨post, rfl⟩ := h
    exact .inr ⟨trivial, es, post, rfl, Events.Refines.refl es⟩
  | inf et => exact ⟨trivial, fun i e he => by rw [h i e he]; exact Event.Refines.refl e⟩

/-- A run with infinitely many events never refines one that diverges silently, and the other
way around. -/
theorem Behavior.inf_not_refines_diverge (et : Nat → Event) (es : List Event) :
    ¬ (Behavior.inf et).Refines (.fin es .diverge) := fun h => h.1

theorem Behavior.fin_not_refines_inf (es : List Event) (o : Outcome) (et : Nat → Event) :
    ¬ (Behavior.fin es o).Refines (.inf et) := id

theorem Behavior.Refines.trans {a b c : Behavior} :
    a.Refines b → b.Refines c → a.Refines c := by
  intro hab hbc
  match a, b, c, hab, hbc with
  | .fin as ao, .fin bs bo, .fin cs co, hab, hbc =>
    rcases hab with ⟨h1, h2⟩ | ⟨hbo, p', q', rfl, hp'⟩ <;>
      rcases hbc with ⟨h3, h4⟩ | ⟨hco, p, q, rfl, hp⟩
    · exact .inl ⟨Events.Refines.trans h1 h3, Outcome.Refines.trans h2 h4⟩
    · obtain ⟨as1, as2, rfl, h1', -⟩ := Forall2.split h1
      exact .inr ⟨hco, as1, as2, rfl, Events.Refines.trans h1' hp⟩
    · exact .inr ⟨hbo.of_refines h4, p', q', rfl, Events.Refines.trans hp' h3⟩
    · obtain ⟨x1, x2, rfl, hx1, -⟩ := Forall2.split hp'
      exact .inr ⟨hco, x1, x2 ++ q', by simp, Events.Refines.trans hx1 hp⟩
  | .inf ae, .fin bs bo, .fin cs co, ⟨hbo, hab⟩, hbc =>
    rcases hbc with ⟨h3, h4⟩ | ⟨hco, p, q, rfl, hp⟩
    · refine ⟨hbo.of_refines h4, fun i e he => ?_⟩
      obtain ⟨b, hb, hbe⟩ := Forall2.getElem? h3 he
      exact Event.Refines.trans (hab i b hb) hbe
    · refine ⟨hco, fun i e he => ?_⟩
      obtain ⟨b, hb, hbe⟩ := Forall2.getElem? hp he
      exact Event.Refines.trans (hab i b (getElem?_append_some hb)) hbe
  | .inf ae, .inf be, .fin cs co, hab, ⟨hco, hbc⟩ =>
    exact ⟨hco, fun i e he => Event.Refines.trans (hab i) (hbc i e he)⟩
  | .inf ae, .inf be, .inf ce, hab, hbc => exact fun i => Event.Refines.trans (hab i) (hbc i)
  | .fin .., .inf _, _, hab, _ => exact hab.elim
  | _, .fin .., .inf _, _, hbc => exact hbc.elim

end Fir
