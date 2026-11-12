import Fir.Sim

/-!
# Running related code in lockstep

Many rewrites change code without changing what the core computes: they delete or replace ops
whose effect is the same. Their proofs share one fact, proved here once. Two machines with the
same core, whose stacks hold the same code except where a rewrite applies, step together: each
step gives the same core again, or halts the same way, until the target reaches a rewritten
spot. A proof about such a rewrite only reasons about the rewritten spot itself.

`OpsRel L` relates target code to source code that is the same except that `L` relates some
target op sequences to source op sequences, at any depth (inside `cf.if` and `cf.loop`
regions too). `MRel L` relates machines with the same core whose stacks hold related code.
-/

namespace Fir

mutual
/-- Two ops that are the same, or differ only in their regions' code. -/
inductive OpRel (L : List Op → List Op → Prop) : Op → Op → Prop
  | refl (o : Op) : OpRel L o o
  | regions {k res args rt rs loc} : RegionsRel L rt rs →
      OpRel L (.mk k res args rt loc) (.mk k res args rs loc)

inductive RegionsRel (L : List Op → List Op → Prop) : List Region → List Region → Prop
  | nil : RegionsRel L [] []
  | cons {ps ot os rt rs} : OpsRel L ot os → RegionsRel L rt rs →
      RegionsRel L (.mk ps ot :: rt) (.mk ps os :: rs)

/-- Op lists that are the same except where `L` relates a target sequence to a source one. -/
inductive OpsRel (L : List Op → List Op → Prop) : List Op → List Op → Prop
  | refl (l : List Op) : OpsRel L l l
  | cons {o o' t s} : OpRel L o o' → OpsRel L t s → OpsRel L (o :: t) (o' :: s)
  | rw {pt ps t s} : L pt ps → OpsRel L t s → OpsRel L (pt ++ t) (ps ++ s)
end

variable {L : List Op → List Op → Prop}

theorem RegionsRel.refl : (rs : List Region) → RegionsRel L rs rs
  | [] => .nil
  | .mk _ _ :: rs => .cons (.refl _) (RegionsRel.refl rs)

/-- Frames that are the same except for related code. -/
inductive FrameRel (L : List Op → List Op → Prop) : Frame → Frame → Prop
  | refl (f : Frame) : FrameRel L f f
  | block {t s ids} : OpsRel L t s → FrameRel L (.block t ids) (.block s ids)
  | loop {p bt bs rs loc} : RegionsRel L [bt] [bs] →
      FrameRel L (.loop p bt rs loc) (.loop p bs rs loc)

/-- Machines with the same core whose stacks hold related code. -/
def MRel (L : List Op → List Op → Prop) (mt ms : Machine) : Prop :=
  mt.core = ms.core ∧ Forall2 (FrameRel L) mt.stack ms.stack

/-- Two results of a step: the same halt, or related machines. -/
def Lockstep (L : List Op → List Op → Prop) (rt rs : Except Halt Machine) : Prop :=
  (∃ h, rt = .error h ∧ rs = .error h) ∨ (∃ mt ms, rt = .ok mt ∧ rs = .ok ms ∧ MRel L mt ms)

theorem Lockstep.halt {h : Halt} : Lockstep L (.error h) (.error h) := .inl ⟨h, rfl, rfl⟩

/-! ## Frames -/

theorem Forall2.length_eq {r : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Forall2 r as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => by simp [Forall2.length_eq h]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem FrameRel.isProgressLoop {f f' : Frame} (h : FrameRel L f f') :
    f.isProgressLoop = f'.isProgressLoop := by
  cases h with
  | refl => rfl
  | block => rfl
  | loop => rename_i p _ _ _ _ _; cases p <;> rfl

theorem shape_eq {ft fs : List Frame} (h : Forall2 (FrameRel L) ft fs) :
    ft.map Frame.isProgressLoop = fs.map Frame.isProgressLoop := by
  induction ft generalizing fs with
  | nil => cases fs <;> simp_all [Forall2]
  | cons f ft ih =>
    cases fs with
    | nil => exact h.elim
    | cons f' fs => simp [h.1.isProgressLoop, ih h.2]

theorem blockIds_eq {ft fs : List Frame} (h : Forall2 (FrameRel L) ft fs) :
    blockIds ft = blockIds fs := by
  induction ft generalizing fs with
  | nil => cases fs <;> simp_all [Forall2]
  | cons f ft ih =>
    cases fs with
    | nil => exact h.elim
    | cons f' fs =>
      obtain ⟨hf, h⟩ := h
      cases hf with
      | refl => cases f <;> simp [blockIds, ih h]
      | block => simp [blockIds, ih h]
      | loop => simp [blockIds, ih h]

theorem splitStack_eq {α : Type} {pick : Frame → Option α} (XR : α → α → Prop)
    (hpick : ∀ f f', FrameRel L f f' → Option.Rel XR (pick f) (pick f'))
    (hcall : ∀ f f', FrameRel L f f' → f.isCall = f'.isCall) :
    ∀ {ft fs : List Frame}, Forall2 (FrameRel L) ft fs →
      Option.Rel (fun x y => Forall2 (FrameRel L) x.1 y.1 ∧ XR x.2.1 y.2.1 ∧
        Forall2 (FrameRel L) x.2.2 y.2.2) (splitStack pick ft) (splitStack pick fs)
  | [], [], _ => .none
  | f :: ft, f' :: fs, ⟨hf, h⟩ => by
    simp only [splitStack]
    have hrel := hpick f f' hf
    cases hp : pick f <;> cases hp' : pick f' <;> rw [hp, hp'] at hrel <;> cases hrel
    · rw [hcall f f' hf]
      cases f'.isCall
      · simp only [Bool.false_eq_true, ite_false]
        have ih := splitStack_eq XR hpick hcall h
        revert ih
        generalize splitStack pick ft = x
        generalize splitStack pick fs = y
        intro ih
        cases ih with
        | none => exact .none
        | some hxy => exact .some ⟨⟨hf, hxy.1⟩, hxy.2⟩
      · simp only [ite_true]
        exact .none
    · rename_i hxy
      exact .some ⟨trivial, hxy, h⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

abbrev LoopSplit := List Frame × (Bool × Region × List Result × Option Loc) × List Frame

abbrev CallSplit := List Frame × (Env × List Result × List Ty × List Nat × Option Loc) × List Frame

theorem splitStack_loop {ft fs : List Frame} (h : Forall2 (FrameRel L) ft fs) :
    Option.Rel (fun (x y : LoopSplit) => Forall2 (FrameRel L) x.1 y.1 ∧
      (x.2.1.1 = y.2.1.1 ∧ RegionsRel L [x.2.1.2.1] [y.2.1.2.1] ∧ x.2.1.2.2 = y.2.1.2.2) ∧
      Forall2 (FrameRel L) x.2.2 y.2.2) (splitStack pickLoop ft) (splitStack pickLoop fs) :=
  splitStack_eq (fun (x y : Bool × Region × List Result × Option Loc) =>
      x.1 = y.1 ∧ RegionsRel L [x.2.1] [y.2.1] ∧ x.2.2 = y.2.2)
    (fun f f' hf => by
      cases hf with
      | refl f =>
        cases f with
        | loop p body rs loc => exact .some ⟨rfl, RegionsRel.refl _, rfl⟩
        | _ => exact .none
      | block => exact .none
      | loop hb => exact .some ⟨rfl, hb, rfl⟩)
    (fun f f' hf => by cases hf <;> rfl) h

theorem splitStack_call {ft fs : List Frame} (h : Forall2 (FrameRel L) ft fs) :
    Option.Rel (fun (x y : CallSplit) => Forall2 (FrameRel L) x.1 y.1 ∧ x.2.1 = y.2.1 ∧
      Forall2 (FrameRel L) x.2.2 y.2.2) (splitStack pickCall ft) (splitStack pickCall fs) :=
  splitStack_eq Eq
    (fun f f' hf => by
      cases hf with
      | refl f => cases pickCall f <;> constructor <;> rfl
      | block => exact .none
      | loop => exact .none)
    (fun f f' hf => by cases hf <;> rfl) h

/-! ## Core computations -/

/-- Running the same core computation on machines with the same core. -/
theorem lockstep_exec {xt xs : Machine} {c : CM α} {kt ks : α × Machine → Except Halt Machine}
    (hc : xt.core = xs.core)
    (hk : ∀ a core, Lockstep L (kt (a, { xt with core })) (ks (a, { xs with core }))) :
    Lockstep L (xt.exec c >>= kt) (xs.exec c >>= ks) := by
  simp only [Machine.exec, hc]
  cases c.run xs.core with
  | error h => exact .halt
  | ok p => exact hk p.1 p.2

/-- The result of a core computation run on related machines, then returned. -/
theorem Forall2.cons' {r : α → β → Prop} {a : α} {b : β} {as : List α} {bs : List β}
    (h : r a b) (hs : Forall2 r as bs) : Forall2 r (a :: as) (b :: bs) := ⟨h, hs⟩

theorem MRel.mk' {mt ms : Machine} (hc : mt.core = ms.core)
    (hst : Forall2 (FrameRel L) mt.stack ms.stack) : MRel L mt ms := ⟨hc, hst⟩

theorem lockstep_exec_pure {xt xs : Machine} {c : CM α} (hc : xt.core = xs.core)
    (hst : Forall2 (FrameRel L) xt.stack xs.stack) :
    Lockstep L (xt.exec c >>= fun r => pure r.2) (xs.exec c >>= fun r => pure r.2) :=
  lockstep_exec hc fun _ _ => .inr ⟨_, _, rfl, rfl, rfl, hst⟩

theorem enterBody_eq {mt ms : Machine} (hR : MRel L mt ms) (loc : Option Loc) {bt bs : Region}
    (hb : RegionsRel L [bt] [bs]) (vs : List RVal) :
    Lockstep L (enterBody mt loc bt vs) (enterBody ms loc bs vs) := by
  obtain ⟨hc, hst⟩ := hR
  cases hb with
  | cons hops _ =>
    unfold enterBody
    refine lockstep_exec (by exact hc) ?_
    intro _ core
    exact .inr ⟨_, _, rfl, rfl, MRel.mk' rfl (Forall2.cons' (.block hops) hst)⟩

/-! ## Control flow -/

theorem terminate_eq {mt ms : Machine} (hR : MRel L mt ms) (loc : Option Loc) (k : OpKind)
    (vs : List RVal) : Lockstep L (terminate mt loc k vs) (terminate ms loc k vs) := by
  obtain ⟨hc, hst⟩ := hR
  cases k
  case yield =>
    unfold terminate
    cases ht : mt.stack with
    | nil =>
      cases hs : ms.stack with
      | nil => exact .halt
      | cons => rw [ht, hs] at hst; exact hst.elim
    | cons f rt =>
      cases hs : ms.stack with
      | nil => rw [ht, hs] at hst; exact hst.elim
      | cons f' rs =>
        rw [ht, hs] at hst
        obtain ⟨hf, hrest⟩ := hst
        cases hf with
        | refl f =>
          cases f with
          | ifJoin rs' loc' => exact lockstep_exec_pure (xt := { mt with stack := rt }) hc hrest
          | _ => exact .halt
        | block => exact .halt
        | loop => exact .halt
  case brk =>
    unfold terminate
    have hsp := splitStack_loop hst
    revert hsp
    cases splitStack pickLoop mt.stack <;> cases splitStack pickLoop ms.stack <;> intro hsp
    · exact .halt
    · cases hsp
    · cases hsp
    · rename_i x y
      obtain ⟨above, ⟨p, body, rs, loc'⟩, below⟩ := x
      obtain ⟨above', ⟨p', body', rs', loc''⟩, below'⟩ := y
      cases hsp with
      | some hxy =>
        obtain ⟨habove, ⟨-, -, he⟩, hbelow⟩ := hxy
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp only
        rw [blockIds_eq habove]
        exact lockstep_exec_pure hc hbelow
  case cont =>
    unfold terminate
    have hsp := splitStack_loop hst
    revert hsp
    cases splitStack pickLoop mt.stack <;> cases splitStack pickLoop ms.stack <;> intro hsp
    · exact .halt
    · cases hsp
    · cases hsp
    · rename_i x y
      obtain ⟨above, ⟨p, body, rs, loc'⟩, below⟩ := x
      obtain ⟨above', ⟨p', body', rs', loc''⟩, below'⟩ := y
      cases hsp with
      | some hxy =>
        obtain ⟨habove, ⟨hp, hb, he⟩, hbelow⟩ := hxy
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        dsimp only at hp
        subst hp
        simp only
        rw [blockIds_eq habove]
        refine lockstep_exec (by exact hc) ?_
        intro _ core
        refine enterBody_eq ?_ loc hb vs
        exact MRel.mk' rfl (Forall2.cons' (.loop hb) hbelow)
  case ret =>
    unfold terminate
    have hsp := splitStack_call hst
    revert hsp
    cases splitStack pickCall mt.stack <;> cases splitStack pickCall ms.stack <;> intro hsp
    · exact .halt
    · cases hsp
    · cases hsp
    · rename_i x y
      obtain ⟨above, info, below⟩ := x
      obtain ⟨above', info', below'⟩ := y
      cases hsp with
      | some hxy =>
        obtain ⟨habove, rfl, hbelow⟩ := hxy
        obtain ⟨saved, rs, rets, scopes, loc'⟩ := info
        simp only
        split
        · exact .halt
        · rw [blockIds_eq habove]
          refine lockstep_exec (by exact hc) ?_
          intro _ core
          simp only [Forall2.length_eq hbelow, List.isEmpty_iff_length_eq_zero]
          split
          · exact .halt
          · exact lockstep_exec_pure rfl hbelow
  all_goals exact .halt

theorem addAllocId_eq {ft fs : List Frame} (h : Forall2 (FrameRel L) ft fs) (id : Nat) :
    Forall2 (FrameRel L) (addAllocId id ft) (addAllocId id fs) := by
  cases ft with
  | nil => cases fs with
    | nil => trivial
    | cons => exact h.elim
  | cons f rt =>
    cases fs with
    | nil => exact h.elim
    | cons f' rs =>
      obtain ⟨hf, hrest⟩ := h
      cases hf with
      | refl f => cases f <;> exact Forall2.cons' (.refl _) hrest
      | block hops => exact Forall2.cons' (.block hops) hrest
      | loop hb => exact Forall2.cons' (.loop hb) hrest

theorem execFlat_eq {mt ms : Machine} (hR : MRel L mt ms) (kind : OpKind) (results : List Result)
    (args : List Operand) (loc : Option Loc) :
    Lockstep L (execFlat mt kind results args loc) (execFlat ms kind results args loc) := by
  obtain ⟨hc, hst⟩ := hR
  unfold execFlat
  cases kind.callee? with
  | some callee =>
    simp only
    refine lockstep_exec (by exact hc) ?_
    intro vs core
    simp only
    cases core.funcs[callee]? with
    | none => exact .halt
    | some f =>
      simp only
      refine lockstep_exec rfl ?_
      intro _ core'
      exact .inr ⟨_, _, rfl, rfl, MRel.mk' rfl
        (Forall2.cons' (.refl _) (Forall2.cons' (.refl _) hst))⟩
  | none =>
  cases kind.stackAlloc? with
  | some sa =>
    simp only
    refine lockstep_exec (by exact hc) ?_
    intro p core
    exact .inr ⟨_, _, rfl, rfl, MRel.mk' rfl (addAllocId_eq hst _)⟩
  | none =>
  simp only
  split
  · refine lockstep_exec (by exact hc) ?_
    intro vs core
    simp only
    cases ht : mt.stack with
    | nil =>
      cases hs : ms.stack with
      | nil =>
        refine terminate_eq ?_ loc kind vs
        exact MRel.mk' rfl trivial
      | cons => rw [ht, hs] at hst; exact hst.elim
    | cons f rt =>
      cases hs : ms.stack with
      | nil => rw [ht, hs] at hst; exact hst.elim
      | cons f' rs =>
        rw [ht, hs] at hst
        obtain ⟨hf, hrest⟩ := hst
        simp only
        rw [blockIds_eq (Forall2.cons' hf (show Forall2 (FrameRel L) [] [] from trivial))]
        refine lockstep_exec rfl ?_
        intro _ core'
        refine terminate_eq ?_ loc kind vs
        exact MRel.mk' rfl hrest
  · exact lockstep_exec_pure hc hst

theorem execOp_eq {mt ms : Machine} (hR : MRel L mt ms) {ot os : Op} (ho : OpRel L ot os) :
    Lockstep L (execOp mt ot) (execOp ms os) := by
  obtain ⟨k, res, args, rt, rs, loc, hreg, rfl, rfl⟩ :
      ∃ k res args rt rs loc, RegionsRel L rt rs ∧ ot = .mk k res args rt loc ∧
        os = .mk k res args rs loc := by
    cases ho with
    | refl => cases ot; exact ⟨_, _, _, _, _, _, RegionsRel.refl _, rfl, rfl⟩
    | regions h => exact ⟨_, _, _, _, _, _, h, rfl, rfl⟩
  obtain ⟨hc, hst⟩ := hR
  rcases hreg with _ | ⟨hops1, _ | ⟨hops2, _ | ⟨hops3, hrest⟩⟩⟩
  · exact execFlat_eq (MRel.mk' hc hst) k res args loc
  · simp only [execOp]
    cases k.loopProgress? with
    | none => exact .halt
    | some p =>
      simp only
      refine lockstep_exec (by exact hc) ?_
      intro vs core
      refine enterBody_eq ?_ loc (.cons hops1 .nil) vs
      exact MRel.mk' rfl (Forall2.cons' (.loop (.cons hops1 .nil)) hst)
  · simp only [execOp]
    split
    · refine lockstep_exec (by exact hc) ?_
      intro c core
      cases c with
      | poison => exact .halt
      | bits b =>
        refine .inr ⟨_, _, rfl, rfl, MRel.mk' rfl (Forall2.cons' ?_ (Forall2.cons' (.refl _) hst))⟩
        by_cases hb : b = 1
        · simp only [hb, ite_true]; exact .block hops1
        · simp only [hb, ite_false]; exact .block hops2
    · exact .halt
  · exact .halt

/-- A step from machines whose next ops are related (or both at the end of a block) gives the
same halt or related machines. A step at the start of a rewritten sequence is not covered: that
is what each rewrite's proof handles. -/
theorem step_eq {mt ms : Machine} (hR : MRel L mt ms)
    (hhead : ∀ ot t ids rt, mt.stack = .block (ot :: t) ids :: rt →
      ∃ os s rs, ms.stack = .block (os :: s) ids :: rs ∧ OpRel L ot os ∧ OpsRel L t s)
    (hnil : ∀ ids rt, mt.stack = .block [] ids :: rt → ∃ rs, ms.stack = .block [] ids :: rs) :
    Lockstep L (step mt) (step ms) := by
  obtain ⟨hc, hst⟩ := hR
  cases ht : mt.stack with
  | nil =>
    cases hs : ms.stack with
    | nil => simp only [step, ht, hs]; exact .halt
    | cons => rw [ht, hs] at hst; exact hst.elim
  | cons f rt =>
    cases hs : ms.stack with
    | nil => rw [ht, hs] at hst; exact hst.elim
    | cons f' rs =>
      have hst' := hst
      rw [ht, hs] at hst'
      obtain ⟨hf, hrest⟩ := hst'
      cases f with
      | block ops ids =>
        cases ops with
        | nil =>
          obtain ⟨rs', hs'⟩ := hnil ids rt ht
          rw [hs] at hs'
          simp only [List.cons.injEq] at hs'
          obtain ⟨rfl, rfl⟩ := hs'
          simp only [step, ht, hs]
          refine lockstep_exec (by exact hc) ?_
          intro _ core
          refine terminate_eq ?_ none .yield []
          exact MRel.mk' rfl hrest
        | cons ot t =>
          obtain ⟨os, s, rs', hs', ho, hops⟩ := hhead ot t ids rt ht
          rw [hs] at hs'
          simp only [List.cons.injEq] at hs'
          obtain ⟨rfl, rfl⟩ := hs'
          simp only [step, ht, hs]
          refine execOp_eq ?_ ho
          exact MRel.mk' hc (Forall2.cons' (.block hops) hrest)
      | _ =>
        cases hf <;> (simp only [step, ht, hs]; exact .halt)

/-! ## Steps that run the same core computation -/

theorem execOp_simple (m : Machine) (k : OpKind) (res : List Result) (args : List Operand)
    (loc : Option Loc) (h1 : k.callee? = none) (h2 : k.stackAlloc? = none)
    (h3 : k.isTerminator = false) :
    execOp m (.mk k res args [] loc) =
      match simpleOp loc k res args m.core with
      | .ok (_, core) => .ok { m with core }
      | .error h => .error h := by
  simp only [execOp, execFlat, h1, h2, h3, Machine.exec, StateT.run, Bool.false_eq_true, ite_false]
  cases simpleOp loc k res args m.core with
  | error h => rfl
  | ok r => rfl

theorem shape_cons {f f' : Frame} {rt rs : List Frame} (h : f.isProgressLoop = f'.isProgressLoop)
    (hrest : Forall2 (FrameRel L) rt rs) :
    (f :: rt).map Frame.isProgressLoop = (f' :: rs).map Frame.isProgressLoop := by
  simp [h, shape_eq hrest]

/-- The machine after a core computation `x`, with stack `m`'s. -/
def afterOp (m : Machine) : Except Halt (Unit × Core) → Except Halt Machine
  | .ok (_, core) => .ok { m with core }
  | .error h => .error h

/-- One target step matched by one source step that runs the same core computation, from tops of
the stack that differ only in code. -/
theorem step_same {R : Machine → Machine → Prop} {mt ms mt'' ms'' : Machine} {x : Except Halt (Unit × Core)}
    (ht : step mt = afterOp mt'' x) (hs : step ms = afterOp ms'' x)
    (hshape : ms.shape = mt.shape)
    (hR : ∀ u core, x = .ok (u, core) → R { mt'' with core } { ms'' with core }) :
    StepMatch R mt ms := by
  cases x with
  | ok p =>
    obtain ⟨_, core⟩ := p
    refine ⟨fun mt' e => ?_, fun h e => ?_⟩
    · rw [ht, afterOp] at e
      cases e
      refine .inr ⟨0, { ms'' with core }, by rw [runSteps_one, hs, afterOp], hR _ core rfl, ?_⟩
      intro j mj hj ej
      obtain rfl : j = 0 := by omega
      simp only [runSteps, Except.ok.injEq] at ej
      subst ej
      exact hshape
    · rw [ht, afterOp] at e; cases e
  | error h' =>
    refine ⟨fun mt' e => ?_, fun h e => ?_⟩
    · rw [ht, afterOp] at e; cases e
    · rw [ht, afterOp] at e
      cases e
      by_cases hamb : h'.behavior = .ambiguous
      · exact .inl ⟨1, h', by rw [runSteps_one, hs, afterOp], .inr hamb⟩
      · exact .inr ⟨1, h', by rw [runSteps_one, hs, afterOp], Behavior.Refines.refl _ hamb⟩

/-- A lockstep step is a simulation step: the source takes one step. -/
theorem StepMatch.of_lockstep {mt ms : Machine} (hR : MRel L mt ms)
    (h : Lockstep L (step mt) (step ms)) : StepMatch (MRel L) mt ms := by
  constructor
  · intro mt' e
    rcases h with ⟨h, e1, _⟩ | ⟨mt'', ms', e1, e2, hR'⟩
    · rw [e] at e1; cases e1
    · rw [e, Except.ok.injEq] at e1
      subst e1
      refine .inr ⟨0, ms', by rw [runSteps_one]; exact e2, hR', fun j mj hj ej => ?_⟩
      obtain rfl : j = 0 := by omega
      simp only [runSteps, Except.ok.injEq] at ej
      subst ej
      exact (shape_eq hR.2).symm
  · intro ht e
    rcases h with ⟨h, e1, e2⟩ | ⟨_, _, e1, _⟩
    · rw [e, Except.error.injEq] at e1
      subst e1
      by_cases hamb : ht.behavior = .ambiguous
      · exact .inl ⟨1, ht, by rw [runSteps_one]; exact e2, .inr hamb⟩
      · exact .inr ⟨1, ht, by rw [runSteps_one]; exact e2, Behavior.Refines.refl _ hamb⟩
    · rw [e] at e1; cases e1

/-- A lockstep step is a simulation step, for machines whose stacks agree on `progress` loops. -/
theorem StepMatch.of_lockstep' {mt ms : Machine} (hshape : ms.shape = mt.shape)
    (h : Lockstep L (step mt) (step ms)) : StepMatch (MRel L) mt ms := by
  constructor
  · intro mt' e
    rcases h with ⟨h, e1, _⟩ | ⟨mt'', ms', e1, e2, hR'⟩
    · rw [e] at e1; cases e1
    · rw [e, Except.ok.injEq] at e1
      subst e1
      refine .inr ⟨0, ms', by rw [runSteps_one]; exact e2, hR', fun j mj hj ej => ?_⟩
      obtain rfl : j = 0 := by omega
      simp only [runSteps, Except.ok.injEq] at ej
      subst ej
      exact hshape
  · intro ht e
    rcases h with ⟨h, e1, e2⟩ | ⟨_, _, e1, _⟩
    · rw [e, Except.error.injEq] at e1
      subst e1
      by_cases hamb : ht.behavior = .ambiguous
      · exact .inl ⟨1, ht, by rw [runSteps_one]; exact e2, .inr hamb⟩
      · exact .inr ⟨1, ht, by rw [runSteps_one]; exact e2, Behavior.Refines.refl _ hamb⟩
    · rw [e] at e1; cases e1

end Fir
