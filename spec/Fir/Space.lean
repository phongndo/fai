import Fir.Sim

/-!
# The memory space is fixed for a run

No step changes the core's memory space (its pointer and address sizes): every core computation
updates other fields only, and the control layer changes only the stack. Proofs that need facts about the space, such as pointers taking at
least one byte, get them from the module once and keep them for the whole run.
-/

namespace Fir

/-- A core computation started on a core where `proj` is `v` ends on one where it is still `v`.
The combinators below build such proofs from a computation's structure, for any part of the core
that the computation's updates leave alone (with `proj := id`, for computations that only read
the core). -/
def Keeps (proj : Core → γ) (v : γ) (x : CM α) : Prop :=
  ∀ c r, proj c = v → x c = .ok r → proj r.2 = v

/-- A core computation started with memory space `sp` ends with memory space `sp`. -/
abbrev KeepsSpace (sp : SpaceCfg) (x : CM α) : Prop := Keeps Core.space sp x

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

theorem halt' (b : Behavior) (loc : Option Loc) (note : String) :
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
variable {sp : SpaceCfg}

theorem keeps_choose : KeepsSpace sp choose := by unfold choose; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible exact keeps_choose)

theorem keeps_freshId (used : Nat → Bool) (keys : List Nat) :
    KeepsSpace sp (freshId used keys) := by
  unfold freshId; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_freshId)

theorem keeps_freshTag (parent : Option Nat) : KeepsSpace sp (freshTag parent) := by
  unfold freshTag; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_freshTag)

theorem keeps_checkTypes (loc : Option Loc) : ∀ (rs : List Result) (vs : List RVal),
    KeepsSpace sp (checkTypes loc rs vs)
  | [], [] => by unfold checkTypes; keeps
  | r :: rs, v :: vs => by
    unfold checkTypes; keeps
    all_goals exact keeps_checkTypes loc rs vs
  | [], _ :: _ => by unfold checkTypes; keeps
  | _ :: _, [] => by unfold checkTypes; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_checkTypes)

theorem keeps_getAlloc (loc : Option Loc) (a : Nat) : KeepsSpace sp (getAlloc loc a) := by
  unfold getAlloc; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_getAlloc)

theorem keeps_setAlloc (a : Nat) (al : Alloc) : KeepsSpace sp (setAlloc a al) := by
  unfold setAlloc; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_setAlloc)

theorem keeps_realize (loc : Option Loc) (a : Nat) : KeepsSpace sp (realize loc a) := by
  unfold realize; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_realize)

theorem keeps_ptrAddr (loc : Option Loc) (p : Ptr) : KeepsSpace sp (ptrAddr loc p) := by
  unfold ptrAddr; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_ptrAddr)

theorem keeps_ptrExpose (loc : Option Loc) (p : Ptr) : KeepsSpace sp (ptrExpose loc p) := by
  unfold ptrExpose; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_ptrExpose)

theorem keeps_fromExposed (n : Nat) : KeepsSpace sp (fromExposed n) := by
  unfold fromExposed; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_fromExposed)

theorem keeps_resolve (loc : Option Loc) (p : Ptr) (n : Nat) : KeepsSpace sp (resolve loc p n) := by
  unfold resolve; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_resolve)

theorem keeps_access (loc : Option Loc) (p : Ptr) (n A : Nat) (w : Bool) :
    KeepsSpace sp (access loc p n A w) := by
  intro c r hc e
  simp only [access, bind, Except.bind, pure, Except.pure] at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e; exact hc
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_access)

theorem keeps_fragToBits (loc : Option Loc) (b : Byte) : KeepsSpace sp (fragToBits loc b) := by
  unfold fragToBits; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_fragToBits)

theorem keeps_decodeAs (loc : Option Loc) (T : Ty) (bs : List Byte) :
    KeepsSpace sp (decodeAs loc T bs) := by
  unfold decodeAs; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_decodeAs)

theorem keeps_loadC (loc : Option Loc) (T : Ty) (A : Nat) (p : Option Ptr) :
    KeepsSpace sp (loadC loc T A p) := by
  unfold loadC; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_loadC)

theorem keeps_storeC (loc : Option Loc) (T : Ty) (A : Nat) (v : RVal) (p : Option Ptr) :
    KeepsSpace sp (storeC loc T A v p) := by
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
    KeepsSpace sp (newAlloc loc size align kind) := by
  unfold newAlloc; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_newAlloc)

theorem keeps_releaseIds (ids : List Nat) : KeepsSpace sp (releaseIds ids) := by
  unfold releaseIds; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_releaseIds)

theorem keeps_freePtr (loc : Option Loc) (family : String) (p : Option Ptr) :
    KeepsSpace sp (freePtr loc family p) := by
  unfold freePtr; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_freePtr)

theorem keeps_ptrView (p : Ptr) : KeepsSpace sp (ptrView p) := by
  unfold ptrView; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_ptrView)

theorem keeps_cmpPtrs (loc : Option Loc) (pred : Pred) (p q : Ptr) :
    KeepsSpace sp (cmpPtrs loc pred p q) := by
  unfold cmpPtrs; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_cmpPtrs)

theorem keeps_factHolds (loc : Option Loc) (f : Fact) (v : RVal) :
    KeepsSpace sp (factHolds loc f v) := by
  unfold factHolds ptrFactHolds; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_factHolds)

theorem keeps_checkResults (loc : Option Loc) (rs : List Result) (vs : List RVal) :
    KeepsSpace sp (checkResults loc rs vs) := by
  unfold checkResults; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_checkResults)

theorem keeps_asInt (loc : Option Loc) (w : Nat) (v : RVal) : KeepsSpace sp (asInt loc w v) := by
  unfold asInt; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_asInt)

theorem keeps_asPtr (loc : Option Loc) (v : RVal) : KeepsSpace sp (asPtr loc v) := by
  unfold asPtr; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_asPtr)

theorem keeps_fromOut (loc : Option Loc) (o : OpOut w) : KeepsSpace sp (fromOut loc o) := by
  unfold fromOut; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_fromOut)

theorem keeps_offsetBy (loc : Option Loc) (inbounds : Bool) (p : Ptr) (n : Int) :
    KeepsSpace sp (offsetBy loc inbounds p n) := by
  unfold offsetBy; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_offsetBy)

theorem keeps_callTarget (loc : Option Loc) (callee : Callee) (vs : List RVal) :
    KeepsSpace sp (callTarget loc callee vs) := by
  unfold callTarget; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_callTarget)

theorem keeps_evalSimple (loc : Option Loc) (k : OpKind) (rs : List Result) (vs : List RVal) :
    KeepsSpace sp (evalSimple loc k rs vs) := by
  unfold evalSimple; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_evalSimple)

theorem keeps_simpleOp (loc : Option Loc) (k : OpKind) (rs : List Result) (vs : List RVal) :
    KeepsSpace sp (simpleOp loc k rs vs) := by
  unfold simpleOp; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_simpleOp)

theorem keeps_openScope (loc : Option Loc) (r : Result) (v : RVal) :
    KeepsSpace sp (openScope loc r v) := by
  unfold openScope; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_openScope)

theorem keeps_enterCall (loc : Option Loc) (params : List Result) (vs : List RVal) :
    KeepsSpace sp (enterCall loc params vs) := by
  unfold enterCall; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_enterCall)

theorem keeps_closeScopes (ids : List Nat) : KeepsSpace sp (closeScopes ids) := by
  unfold closeScopes; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keeps_closeScopes)

end

/-! ## Steps -/

/-- A machine-level result whose machine, if any, has memory space `sp`. -/
def EndsIn (sp : SpaceCfg) (r : Except Halt Machine) : Prop := ∀ m', r = .ok m' → m'.core.space = sp

theorem EndsIn.halt' {sp : SpaceCfg} (h : Halt) : EndsIn sp (.error h) := by intro _ e; cases e

theorem EndsIn.throw' {sp : SpaceCfg} (h : Halt) : EndsIn sp (throw h) := by intro _ e; cases e

theorem EndsIn.ok' {sp : SpaceCfg} {m : Machine} (h : m.core.space = sp) : EndsIn sp (.ok m) := by
  intro _ e; cases e; exact h

theorem EndsIn.exec_bind {sp : SpaceCfg} {m : Machine} {x : CM α} {f : α × Machine → Except Halt Machine}
    (hm : m.core.space = sp) (hx : KeepsSpace sp x)
    (hf : ∀ a m', m'.core.space = sp → EndsIn sp (f (a, m'))) :
    EndsIn sp (m.exec x >>= f) := by
  intro m' e
  simp only [Machine.exec, bind, Except.bind] at e
  cases ex : x.run m.core with
  | error h => rw [ex] at e; cases e
  | ok p =>
    rw [ex] at e
    exact hf p.1 _ (hx m.core p hm ex) m' e

theorem EndsIn.exec_pure {sp : SpaceCfg} {m : Machine} {x : CM α} (hm : m.core.space = sp)
    (hx : KeepsSpace sp x) : EndsIn sp (m.exec x >>= fun r => pure r.2) :=
  exec_bind hm hx fun _ _ h => ok' h

theorem EndsIn.throw_bind {sp : SpaceCfg} (h : Halt) (f : α → Except Halt Machine) :
    EndsIn sp (throw h >>= f) := by intro _ e; cases e

/-- A computation that doesn't touch the machine, then a continuation. -/
theorem EndsIn.bind' {sp : SpaceCfg} {x : Except Halt α} {f : α → Except Halt Machine}
    (hf : ∀ a, EndsIn sp (f a)) : EndsIn sp (x >>= f) := by
  intro m' e
  cases x with
  | error h => cases e
  | ok a => exact hf a m' e

theorem EndsIn.bindResults {sp : SpaceCfg} {m : Machine} (hm : m.core.space = sp) (loc : Option Loc)
    (rs : List Result) (vs : List RVal) : EndsIn sp (m.bindResults loc rs vs) :=
  exec_bind hm (keeps_checkResults loc rs vs) fun _ _ h => ok' h

/-- One step of `ends_in` that applies a lemma about a named step function. Extended below. -/
syntax "ends_lemma" : tactic
macro_rules | `(tactic| ends_lemma) => `(tactic| fail)

/-- Prove `EndsIn sp r` by following `r`'s structure. -/
macro "ends_in" : tactic => `(tactic| repeat' (first
  | exact Fir.EndsIn.halt' _
  | exact Fir.EndsIn.throw' _
  | exact Fir.EndsIn.throw_bind _ _
  | exact Fir.EndsIn.ok' (by assumption)
  | refine Fir.EndsIn.exec_bind (by first | rfl | assumption) (by keeps) (fun _ _ _ => ?_)
  | exact Fir.EndsIn.bindResults (by first | rfl | assumption) _ _ _
  | refine Fir.EndsIn.bind' (fun _ => ?_)
  | ends_lemma
  | dsimp only
  | split))

theorem enterBody_space {sp : SpaceCfg} {m : Machine} (hm : m.core.space = sp) (loc : Option Loc)
    (body : Region) (vs : List RVal) : EndsIn sp (enterBody m loc body vs) := by
  unfold enterBody; ends_in
macro_rules | `(tactic| ends_lemma) => `(tactic| exact enterBody_space (by assumption) _ _ _)

theorem jump_space {sp : SpaceCfg} {m : Machine} (hm : m.core.space = sp) (loc : Option Loc)
    (s : Succ) (vs : List RVal) : EndsIn sp (jump m loc s vs) := by
  unfold jump; ends_in
macro_rules | `(tactic| ends_lemma) => `(tactic| exact jump_space (by assumption) _ _ _)

theorem terminate_space {sp : SpaceCfg} {m : Machine} (hm : m.core.space = sp) (loc : Option Loc)
    (k : OpKind) (vs : List RVal) : EndsIn sp (terminate m loc k vs) := by
  unfold terminate; ends_in
macro_rules | `(tactic| ends_lemma) => `(tactic| exact terminate_space (by assumption) _ _ _)

theorem execFlat_space {sp : SpaceCfg} {m : Machine} (hm : m.core.space = sp) (kind : OpKind)
    (results : List Result) (args : List Operand) (loc : Option Loc) :
    EndsIn sp (execFlat m kind results args loc) := by
  unfold execFlat; ends_in
macro_rules
  | `(tactic| ends_lemma) => `(tactic| exact execFlat_space (by first | rfl | assumption) _ _ _ _)

theorem execOp_space {sp : SpaceCfg} {m : Machine} (hm : m.core.space = sp) (op : Op) :
    EndsIn sp (execOp m op) := by
  unfold execOp; ends_in
macro_rules | `(tactic| ends_lemma) => `(tactic| exact execOp_space (by first | rfl | assumption) _)

/-- **No step changes the memory space.** -/
theorem step_space {m m' : Machine} (e : step m = .ok m') : m'.core.space = m.core.space := by
  have : EndsIn m.core.space (step m) := by unfold step; ends_in
  exact this m' e

theorem runSteps_space {n : Nat} {m m' : Machine} (e : runSteps n m = .ok m') :
    m'.core.space = m.core.space := by
  induction n generalizing m with
  | zero => cases e; rfl
  | succ n ih =>
    simp only [runSteps] at e
    cases es : step m with
    | error h => rw [es] at e; cases e
    | ok m1 => rw [es] at e; exact (ih e).trans (step_space es)

/-- A call starts in the module's memory space. -/
theorem init_space {oracle : Nat → Int} {mod : Module} {f : Func} {args : List RVal} {m : Machine}
    (e : Machine.init oracle mod f args = .ok m) : m.core.space = mod.space := by
  simp only [Machine.init, bind, Except.bind] at e
  cases ec : (enterCall none f.params args).run (Core.initial oracle mod) with
  | error h => rw [ec] at e; cases e
  | ok p =>
    rw [ec] at e
    cases e
    exact keeps_enterCall none f.params args _ _ rfl ec

end Fir
