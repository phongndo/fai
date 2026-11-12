import Fir.Behavior

/-!
# The memory space is fixed and the trace only grows

No step changes the core's memory space (its pointer and address sizes), and no step removes or
changes an event: every core computation updates other fields only, and the control layer changes
only the stack, except that an external call adds its event to the end of the trace
(`Machine.record`). Proofs that need facts about the space, such as pointers taking at least one
byte, get them from the module once and keep them for the whole run; the simulation theorem
(`Fir.Sim`) uses that a run's traces are prefixes of each other.
-/

namespace Fir

/-- A core computation started on a core where `proj` is `v` ends on one where it is still `v`.
The combinators below build such proofs from a computation's structure, for any part of the core
that the computation's updates leave alone (with `proj := id`, for computations that only read
the core). -/
def Keeps (proj : Core → γ) (v : γ) (x : CM α) : Prop :=
  ∀ c r, proj c = v → x c = .ok r → proj r.2 = v

/-- What no core computation changes: the memory space and the trace. -/
abbrev Core.fixed (c : Core) : SpaceCfg × List Event := (c.space, c.trace)

/-- A core computation keeps the memory space and the trace. -/
abbrev KeepsFixed (v : SpaceCfg × List Event) (x : CM α) : Prop := Keeps Core.fixed v x

namespace Keeps

variable {proj : Core → γ} {v : γ}

theorem pure' (a : α) : Keeps proj v (pure a : CM α) := by
  intro c r hc e; cases e; exact hc

theorem bind' {x : CM α} {f : α → CM β} (hx : Keeps proj v x) (hf : ∀ a, Keeps proj v (f a)) :
    Keeps proj v (x >>= f) := by
  intro c r hc e
  simp only [bind, StateT.bind, Except.bind] at e
  cases ex : x c with
  | error h => rw [ex] at e; cases e
  | ok p =>
    rw [ex] at e
    exact hf p.1 p.2 r (hx c p hc ex) e

theorem bind_get {f : Core → CM β} (hf : ∀ c, proj c = v → Keeps proj v (f c)) :
    Keeps proj v (get >>= f) := by
  intro c r hc e
  exact hf c hc c r hc e

theorem set' {c' : Core} (h : proj c' = v) : Keeps proj v (set c' : CM PUnit) := by
  intro c r _ e; cases e; exact h

theorem modify' {f : Core → Core} (h : ∀ c, proj (f c) = proj c) :
    Keeps proj v (modify f : CM PUnit) := by
  intro c r hc e; cases e; exact (h c).trans hc

theorem get' : Keeps proj v (get : CM Core) := by
  intro c r hc e; cases e; exact hc

theorem throw' (h : Halt) : Keeps proj v (throw h : CM α) := by
  intro c r _ e; cases e

theorem lift' (x : Except Halt α) : Keeps proj v (liftM x : CM α) := by
  intro c r hc e
  cases x with
  | error h => cases e
  | ok a => cases e; exact hc

theorem monadLift' (x : Except Halt α) : Keeps proj v (MonadLiftT.monadLift x : CM α) :=
  lift' x

theorem map' {f : α → β} {x : CM α} (hx : Keeps proj v x) : Keeps proj v (f <$> x) := by
  intro c r hc e
  simp only [Functor.map, StateT.map] at e
  cases ex : x c with
  | error h => rw [ex] at e; cases e
  | ok p => rw [ex] at e; cases e; exact hx c p hc ex

theorem tryCatch' {x : CM α} {handle : Halt → CM α} (hx : Keeps proj v x)
    (hh : ∀ h, Keeps proj v (handle h)) : Keeps proj v (tryCatch x handle) := by
  intro c r hc e
  have e' : (match x c with | .error h => handle h c | .ok p => .ok p) = Except.ok r := by
    rw [← e]
    simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch]
    cases x c <;> rfl
  cases ex : x c with
  | error h => rw [ex] at e'; exact hh h c r hc e'
  | ok p => rw [ex] at e'; cases e'; exact hx c _ hc ex

theorem ite' {p : Prop} [Decidable p] {x y : CM α} (hx : Keeps proj v x) (hy : Keeps proj v y) :
    Keeps proj v (if p then x else y) := by
  split <;> assumption

theorem forIn' {l : List α} {init : β} {f : α → β → CM (ForInStep β)}
    (hf : ∀ a b, Keeps proj v (f a b)) : Keeps proj v (forIn l init f) := by
  induction l generalizing init with
  | nil => exact pure' _
  | cons a l ih =>
    rw [List.forIn_cons]
    refine bind' (hf a init) fun s => ?_
    cases s with
    | done b => exact pure' _
    | yield b => exact ih

theorem mapM' {l : List α} {f : α → CM β} (hf : ∀ a, Keeps proj v (f a)) :
    Keeps proj v (l.mapM f) := by
  induction l with
  | nil => exact pure' _
  | cons a l ih =>
    rw [List.mapM_cons]
    exact bind' (hf a) fun b => bind' ih fun bs => pure' _

theorem halt' (b : Outcome) (loc : Option Loc) (note : String) :
    Keeps proj v (halt b loc note : CM α) := throw' _

theorem ub' (k : UBKind) (loc : Option Loc) (note : String) :
    Keeps proj v (ub k loc note : CM α) := throw' _

end Keeps

/-- One step of `keeps` that applies a lemma about a named computation. Extended below. -/
syntax "keeps_lemma" : tactic
macro_rules | `(tactic| keeps_lemma) => `(tactic| fail)

/-- Prove `Keeps proj v x` by following `x`'s structure. -/
macro "keeps" : tactic => `(tactic| repeat' (first
  | with_reducible exact Fir.Keeps.pure' _
  | with_reducible exact Fir.Keeps.get'
  | with_reducible exact Fir.Keeps.throw' _
  | with_reducible exact Fir.Keeps.halt' _ _ _
  | with_reducible exact Fir.Keeps.ub' _ _ _
  | with_reducible exact Fir.Keeps.lift' _
  | with_reducible exact Fir.Keeps.monadLift' _
  | with_reducible exact Fir.Keeps.set' (by assumption)
  | with_reducible exact Fir.Keeps.modify' (fun _ => rfl)
  | with_reducible refine Fir.Keeps.bind_get (fun _ _ => ?_)
  | with_reducible refine Fir.Keeps.bind' ?_ (fun _ => ?_)
  | with_reducible refine Fir.Keeps.map' ?_
  | with_reducible refine Fir.Keeps.tryCatch' ?_ (fun _ => ?_)
  | with_reducible refine Fir.Keeps.forIn' (fun _ _ => ?_)
  | with_reducible refine Fir.Keeps.mapM' (fun _ => ?_)
  | keeps_lemma
  | split
  | dsimp only))

section
variable {sp : SpaceCfg × List Event}

theorem keeps_choose : KeepsFixed sp choose := by unfold choose; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible exact keeps_choose)

theorem keeps_freshId (used : Nat → Bool) (keys : List Nat) :
    KeepsFixed sp (freshId used keys) := by
  unfold freshId; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_freshId)

theorem keeps_freshTag (parent : Option Nat) : KeepsFixed sp (freshTag parent) := by
  unfold freshTag; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_freshTag)

theorem keeps_checkTypes (loc : Option Loc) : ∀ (rs : List Result) (vs : List RVal),
    KeepsFixed sp (checkTypes loc rs vs)
  | [], [] => by unfold checkTypes; keeps
  | r :: rs, v :: vs => by
    unfold checkTypes; keeps
    all_goals exact keeps_checkTypes loc rs vs
  | [], _ :: _ => by unfold checkTypes; keeps
  | _ :: _, [] => by unfold checkTypes; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_checkTypes)

theorem keeps_getAlloc (loc : Option Loc) (a : Nat) : KeepsFixed sp (getAlloc loc a) := by
  unfold getAlloc; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_getAlloc)

theorem keeps_setAlloc (a : Nat) (al : Alloc) : KeepsFixed sp (setAlloc a al) := by
  unfold setAlloc; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_setAlloc)

theorem keeps_realize (loc : Option Loc) (a : Nat) : KeepsFixed sp (realize loc a) := by
  unfold realize; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_realize)

theorem keeps_ptrAddr (loc : Option Loc) (p : Ptr) : KeepsFixed sp (ptrAddr loc p) := by
  unfold ptrAddr; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_ptrAddr)

theorem keeps_ptrExpose (loc : Option Loc) (p : Ptr) : KeepsFixed sp (ptrExpose loc p) := by
  unfold ptrExpose; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_ptrExpose)

theorem keeps_fromExposed (n : Nat) : KeepsFixed sp (fromExposed n) := by
  unfold fromExposed; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_fromExposed)

theorem keeps_resolve (loc : Option Loc) (p : Ptr) (n : Nat) : KeepsFixed sp (resolve loc p n) := by
  unfold resolve; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_resolve)

theorem keeps_access (loc : Option Loc) (p : Ptr) (n A : Nat) (w : Bool) :
    KeepsFixed sp (access loc p n A w) := by
  intro c r hc e
  simp only [access, bind, Except.bind, pure, Except.pure] at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e; exact hc
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_access)

theorem keeps_fragToBits (loc : Option Loc) (b : Byte) : KeepsFixed sp (fragToBits loc b) := by
  unfold fragToBits; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_fragToBits)

theorem keeps_decodeAs (loc : Option Loc) (T : Ty) (bs : List Byte) :
    KeepsFixed sp (decodeAs loc T bs) := by
  unfold decodeAs; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_decodeAs)

theorem keeps_loadC (loc : Option Loc) (T : Ty) (A : Nat) (p : Option Ptr) :
    KeepsFixed sp (loadC loc T A p) := by
  unfold loadC; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_loadC)

theorem keeps_storeC (loc : Option Loc) (T : Ty) (A : Nat) (v : RVal) (p : Option Ptr) :
    KeepsFixed sp (storeC loc T A v p) := by
  cases p with
  | none => exact Keeps.ub' _ _ _
  | some p =>
    intro c r hc e
    cases hty : v.hasTy T with
    | false =>
      simp [storeC, hty, halt, throw, throwThe, MonadExcept.throw, bind, Except.bind] at e
    | true =>
      simp only [storeC, hty, bind, Except.bind, pure, Except.pure] at e
      cases ha : access loc p (v.encode c.space).length A true c with
      | error => rw [ha] at e; cases e
      | ok q => rw [ha] at e; cases e; exact keeps_access loc p _ A true c q hc ha
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_storeC)

theorem keeps_newAlloc (loc : Option Loc) (size align : Nat) (kind : AllocKind) :
    KeepsFixed sp (newAlloc loc size align kind) := by
  unfold newAlloc; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_newAlloc)

theorem keeps_releaseIds (ids : List Nat) : KeepsFixed sp (releaseIds ids) := by
  unfold releaseIds; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_releaseIds)

theorem keeps_freePtr (loc : Option Loc) (family : String) (p : Option Ptr) :
    KeepsFixed sp (freePtr loc family p) := by
  unfold freePtr; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_freePtr)

theorem keeps_ptrView (p : Ptr) : KeepsFixed sp (ptrView p) := by
  unfold ptrView; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_ptrView)

theorem keeps_cmpPtrs (loc : Option Loc) (pred : Pred) (p q : Ptr) :
    KeepsFixed sp (cmpPtrs loc pred p q) := by
  unfold cmpPtrs; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_cmpPtrs)

theorem keeps_factHolds (loc : Option Loc) (f : Fact) (v : RVal) :
    KeepsFixed sp (factHolds loc f v) := by
  unfold factHolds ptrFactHolds; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_factHolds)

theorem keeps_checkResults (loc : Option Loc) (rs : List Result) (vs : List RVal) :
    KeepsFixed sp (checkResults loc rs vs) := by
  unfold checkResults; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_checkResults)

theorem keeps_asInt (loc : Option Loc) (w : Nat) (v : RVal) : KeepsFixed sp (asInt loc w v) := by
  unfold asInt; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_asInt)

theorem keeps_asFloat (loc : Option Loc) (f : FloatTy) (v : RVal) :
    KeepsFixed sp (asFloat loc f v) := by
  unfold asFloat; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_asFloat)

theorem keeps_asPtr (loc : Option Loc) (v : RVal) : KeepsFixed sp (asPtr loc v) := by
  unfold asPtr; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_asPtr)

theorem keeps_fromOut (loc : Option Loc) (o : OpOut w) : KeepsFixed sp (fromOut loc o) := by
  unfold fromOut; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_fromOut)

theorem keeps_offsetBy (loc : Option Loc) (inbounds : Bool) (p : Ptr) (n : Int) :
    KeepsFixed sp (offsetBy loc inbounds p n) := by
  unfold offsetBy; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_offsetBy)

theorem keeps_callTarget (loc : Option Loc) (callee : Callee) (vs : List RVal) :
    KeepsFixed sp (callTarget loc callee vs) := by
  unfold callTarget; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_callTarget)

theorem keeps_leafPtr (loc : Option Loc) (p : Option Ptr) (off : Nat) :
    KeepsFixed sp (leafPtr loc p off) := by
  unfold leafPtr; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_leafPtr)

theorem keeps_loadLeaves (loc : Option Loc) (A : Nat) (p : Option Ptr) :
    ∀ ls, KeepsFixed sp (loadLeaves loc A p ls)
  | [] => by unfold loadLeaves; keeps
  | _ :: ls => by
    unfold loadLeaves; keeps
    all_goals exact keeps_loadLeaves loc A p ls
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_loadLeaves)

theorem keeps_storeLeaves (loc : Option Loc) (A : Nat) (p : Option Ptr) :
    ∀ ls vs, KeepsFixed sp (storeLeaves loc A p ls vs)
  | (_, _) :: ls, _ :: vs => by
    unfold storeLeaves; keeps
    all_goals exact keeps_storeLeaves loc A p ls vs
  | [], _ => by unfold storeLeaves; keeps
  | _ :: _, [] => by unfold storeLeaves; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_storeLeaves)

theorem keeps_loadAny (loc : Option Loc) (T : Ty) (A : Nat) (p : Option Ptr) :
    KeepsFixed sp (loadAny loc T A p) := by
  unfold loadAny; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_loadAny)

theorem keeps_storeAny (loc : Option Loc) (T : Ty) (A : Nat) (v : RVal) (p : Option Ptr) :
    KeepsFixed sp (storeAny loc T A v p) := by
  unfold storeAny; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_storeAny)

theorem keeps_sliceElem (loc : Option Loc) (trap : Bool) (T : Ty) (s i : RVal) :
    KeepsFixed sp (sliceElem loc trap T s i) := by
  unfold sliceElem; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_sliceElem)

theorem keeps_evalFloat (loc : Option Loc) (k : OpKind) (rs : List Result) (vs : List RVal) :
    KeepsFixed sp (evalFloat loc k rs vs) := by
  unfold evalFloat; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_evalFloat)

theorem keeps_evalSimple (loc : Option Loc) (k : OpKind) (rs : List Result) (vs : List RVal) :
    KeepsFixed sp (evalSimple loc k rs vs) := by
  unfold evalSimple; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_evalSimple)

theorem keeps_simpleOp (loc : Option Loc) (k : OpKind) (rs : List Result) (vs : List RVal) :
    KeepsFixed sp (simpleOp loc k rs vs) := by
  unfold simpleOp; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_simpleOp)

theorem keeps_openScope (loc : Option Loc) (r : Result) (v : RVal) :
    KeepsFixed sp (openScope loc r v) := by
  unfold openScope; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_openScope)

theorem keeps_enterCall (loc : Option Loc) (params : List Result) (vs : List RVal) :
    KeepsFixed sp (enterCall loc params vs) := by
  unfold enterCall; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_enterCall)

theorem keeps_closeScopes (ids : List Nat) : KeepsFixed sp (closeScopes ids) := by
  unfold closeScopes; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_closeScopes)

theorem keeps_applyAnswer (loc : Option Loc) (writes : List (Nat × Nat × List Byte))
    (frees : List Nat) (news : List NewAlloc) : KeepsFixed sp (applyAnswer loc writes frees news) := by
  unfold applyAnswer; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_applyAnswer)

theorem keeps_callExtern (loc : Option Loc) (x : Extern) (vs : List RVal) :
    KeepsFixed sp (callExtern loc x vs) := by
  unfold callExtern; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_callExtern)

theorem keeps_unwindStack : ∀ (fs : List Frame), KeepsFixed sp (unwindStack fs)
  | [] => by unfold unwindStack; keeps
  | .block _ _ _ :: fs => by
    unfold unwindStack; keeps
    all_goals exact keeps_unwindStack fs
  | .try_ .. :: _ => by unfold unwindStack; keeps
  | .call _ _ _ _ uw :: fs => by
    unfold unwindStack; keeps
    all_goals exact keeps_unwindStack fs
  | .ifJoin .. :: fs => by unfold unwindStack; exact keeps_unwindStack fs
  | .loop .. :: fs => by unfold unwindStack; exact keeps_unwindStack fs
  | .blocks .. :: fs => by unfold unwindStack; exact keeps_unwindStack fs
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_unwindStack)

end

/-! ## Steps -/

/-- A machine in memory space `sp` whose trace extends `tr`. -/
def Grows (sp : SpaceCfg) (tr : List Event) (m : Machine) : Prop :=
  m.core.space = sp ∧ tr <+: m.core.trace

theorem Grows.refl (m : Machine) : Grows m.core.space m.core.trace m := ⟨rfl, List.prefix_refl _⟩

theorem Grows.record {sp : SpaceCfg} {tr : List Event} {m : Machine} (h : Grows sp tr m)
    (e : Event) : Grows sp tr (m.record e) :=
  ⟨h.1, h.2.trans (List.prefix_append _ _)⟩

/-- A machine-level result whose machine, if any, is in memory space `sp` with a trace that
extends `tr`. -/
def EndsIn (sp : SpaceCfg) (tr : List Event) (r : Except Halt Machine) : Prop :=
  ∀ m', r = .ok m' → Grows sp tr m'

section
variable {sp : SpaceCfg} {tr : List Event}

theorem EndsIn.halt' (h : Halt) : EndsIn sp tr (.error h) := by intro _ e; cases e

theorem EndsIn.throw' (h : Halt) : EndsIn sp tr (throw h) := by intro _ e; cases e

theorem EndsIn.ok' {m : Machine} (h : Grows sp tr m) : EndsIn sp tr (.ok m) := by
  intro _ e; cases e; exact h

theorem EndsIn.exec_bind {m : Machine} {x : CM α} {f : α × Machine → Except Halt Machine}
    (hm : Grows sp tr m) (hx : KeepsFixed m.core.fixed x)
    (hf : ∀ a m', Grows sp tr m' → EndsIn sp tr (f (a, m'))) :
    EndsIn sp tr (m.exec x >>= f) := by
  intro m' e
  simp only [Machine.exec, bind, Except.bind] at e
  cases ex : x.run m.core with
  | error h => rw [ex] at e; cases e
  | ok p =>
    rw [ex] at e
    have hk : Core.fixed p.2 = m.core.fixed := hx m.core p rfl ex
    simp only [Core.fixed, Prod.mk.injEq] at hk
    exact hf p.1 _ ⟨hk.1.trans hm.1, hk.2 ▸ hm.2⟩ m' e

theorem EndsIn.throw_bind (h : Halt) (f : α → Except Halt Machine) :
    EndsIn sp tr (throw h >>= f) := by intro _ e; cases e

/-- A computation that doesn't touch the machine, then a continuation. -/
theorem EndsIn.bind' {x : Except Halt α} {f : α → Except Halt Machine}
    (hf : ∀ a, EndsIn sp tr (f a)) : EndsIn sp tr (x >>= f) := by
  intro m' e
  cases x with
  | error h => cases e
  | ok a => exact hf a m' e

theorem EndsIn.bindResults {m : Machine} (hm : Grows sp tr m) (loc : Option Loc)
    (rs : List Result) (vs : List RVal) : EndsIn sp tr (m.bindResults loc rs vs) :=
  exec_bind hm (keeps_checkResults loc rs vs) fun _ _ h => ok' h

end

/-- One step of `ends_in` that applies a lemma about a named step function. Extended below. -/
syntax "ends_lemma" : tactic
macro_rules | `(tactic| ends_lemma) => `(tactic| fail)

/-- Prove `EndsIn sp tr r` by following `r`'s structure. -/
macro "ends_in" : tactic => `(tactic| repeat' (first
  | exact Fir.EndsIn.halt' _
  | exact Fir.EndsIn.throw' _
  | exact Fir.EndsIn.throw_bind _ _
  | exact Fir.EndsIn.ok' (by assumption)
  | exact Fir.EndsIn.ok' (Fir.Grows.record (by assumption) _)
  | refine Fir.EndsIn.exec_bind (by assumption) (by keeps) (fun _ _ _ => ?_)
  | exact Fir.EndsIn.bindResults (by assumption) _ _ _
  | refine Fir.EndsIn.bind' (fun _ => ?_)
  | ends_lemma
  | dsimp only
  | split))

section
variable {sp : SpaceCfg} {tr : List Event}

theorem enterBody_grows {m : Machine} (hm : Grows sp tr m) (loc : Option Loc)
    (body : Region) (vs : List RVal) : EndsIn sp tr (enterBody m loc body vs) := by
  unfold enterBody; ends_in
macro_rules | `(tactic| ends_lemma) => `(tactic| exact enterBody_grows (by assumption) _ _ _)

theorem jump_grows {m : Machine} (hm : Grows sp tr m) (loc : Option Loc)
    (s : Succ) (vs : List RVal) : EndsIn sp tr (jump m loc s vs) := by
  unfold jump; ends_in
macro_rules | `(tactic| ends_lemma) => `(tactic| exact jump_grows (by assumption) _ _ _)

theorem throwExn_grows {m : Machine} (hm : Grows sp tr m) (loc : Option Loc) (v : RVal) :
    EndsIn sp tr (throwExn m loc v) := by
  unfold throwExn; ends_in
macro_rules | `(tactic| ends_lemma) => `(tactic| exact throwExn_grows (by assumption) _ _)

theorem terminate_grows {m : Machine} (hm : Grows sp tr m) (loc : Option Loc)
    (k : OpKind) (vs : List RVal) : EndsIn sp tr (terminate m loc k vs) := by
  unfold terminate; ends_in
macro_rules | `(tactic| ends_lemma) => `(tactic| exact terminate_grows (by assumption) _ _ _)

theorem execFlat_grows {m : Machine} (hm : Grows sp tr m) (kind : OpKind)
    (results : List Result) (args : List Operand) (loc : Option Loc) :
    EndsIn sp tr (execFlat m kind results args loc) := by
  unfold execFlat; ends_in
macro_rules
  | `(tactic| ends_lemma) => `(tactic| exact execFlat_grows (by assumption) _ _ _ _)

theorem execOp_grows {m : Machine} (hm : Grows sp tr m) (op : Op) :
    EndsIn sp tr (execOp m op) := by
  unfold execOp; ends_in
macro_rules | `(tactic| ends_lemma) => `(tactic| exact execOp_grows (by assumption) _)

end

theorem step_grows {m m' : Machine} (e : step m = .ok m') : Grows m.core.space m.core.trace m' := by
  have : EndsIn m.core.space m.core.trace (step m) := by
    have := Grows.refl m
    unfold step; ends_in
  exact this m' e

/-- **No step changes the memory space.** -/
theorem step_space {m m' : Machine} (e : step m = .ok m') : m'.core.space = m.core.space :=
  (step_grows e).1

/-- **No step removes or changes an event.** -/
theorem step_trace {m m' : Machine} (e : step m = .ok m') : m.core.trace <+: m'.core.trace :=
  (step_grows e).2

theorem runSteps_space {n : Nat} {m m' : Machine} (e : runSteps n m = .ok m') :
    m'.core.space = m.core.space := by
  induction n generalizing m with
  | zero => cases e; rfl
  | succ n ih =>
    simp only [runSteps] at e
    cases es : step m with
    | error h => rw [es] at e; cases e
    | ok m1 => rw [es] at e; exact (ih e).trans (step_space es)

theorem runSteps_trace {n : Nat} {m m' : Machine} (e : runSteps n m = .ok m') :
    m.core.trace <+: m'.core.trace := by
  induction n generalizing m with
  | zero => cases e; exact List.prefix_refl _
  | succ n ih =>
    simp only [runSteps] at e
    cases es : step m with
    | error h => rw [es] at e; cases e
    | ok m1 => rw [es] at e; exact (step_trace es).trans (ih e)

/-- A call starts in the module's memory space, with no events. -/
theorem init_fixed {oracle : Oracle} {world : World} {mod : Module} {f : Func}
    {args : List RVal} {m : Machine} (e : Machine.init oracle world mod f args = .ok m) :
    m.core.space = mod.space ∧ m.core.trace = [] := by
  simp only [Machine.init, bind, Except.bind] at e
  cases ec : (enterCall none f.params args).run (Core.initial oracle world mod) with
  | error h => rw [ec] at e; cases e
  | ok p =>
    rw [ec] at e
    cases e
    have := keeps_enterCall (sp := (Core.initial oracle world mod).fixed) none f.params args _ _ rfl ec
    simp only [Core.fixed, Prod.mk.injEq] at this
    exact ⟨this.1, this.2⟩

theorem init_space {oracle : Oracle} {world : World} {mod : Module} {f : Func}
    {args : List RVal} {m : Machine} (e : Machine.init oracle world mod f args = .ok m) :
    m.core.space = mod.space := (init_fixed e).1

end Fir
