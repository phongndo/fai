import Fir.Fwd

/-!
# Copy propagation

After `%y = copy %x`, later uses of `%y` can read `%x` instead:

```
%y: T = copy %x
%z: T = int.add.wrap %y, %y       // becomes  int.add.wrap %x, %x
func.ret %y                       // becomes  func.ret %x
```

`CopyProp.refines` proves the rewrite correct at any number of places in a function, at any
depth. It covers the ops that follow the copy in the same block, up to and including a
terminator, as long as none of them has regions or calls a function, and none binds `%x` or
`%y`. The copy itself stays: removing a copy whose result is no longer used is dead code
elimination, a separate rewrite.

Both machines run the same ops on the same core, so they stay in lockstep with equal cores. The
new fact is an invariant on the environment: after the copy, `%x` and `%y` hold the same value,
and the ops crossed don't rebind either, so reading one is reading the other.
-/

namespace Fir.CopyProp

/-! ## The environment -/

/-- A core computation that doesn't change the environment. -/
abbrev KeepsEnv (e : Env) (x : CM α) : Prop := Keeps Core.env e x

section
variable {e : Env}

theorem keepsEnv_choose : KeepsEnv e choose := by unfold choose; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible exact keepsEnv_choose)

theorem keepsEnv_freshId (used : Nat → Bool) (keys : List Nat) :
    KeepsEnv e (freshId used keys) := by
  unfold freshId; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_freshId)

theorem keepsEnv_freshTag (parent : Option Nat) : KeepsEnv e (freshTag parent) := by
  unfold freshTag; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_freshTag)

theorem keepsEnv_getAlloc (loc : Option Loc) (a : Nat) : KeepsEnv e (getAlloc loc a) := by
  unfold getAlloc; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_getAlloc)

theorem keepsEnv_setAlloc (a : Nat) (al : Alloc) : KeepsEnv e (setAlloc a al) := by
  unfold setAlloc; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_setAlloc)

theorem keepsEnv_realize (loc : Option Loc) (a : Nat) : KeepsEnv e (realize loc a) := by
  unfold realize; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_realize)

theorem keepsEnv_ptrAddr (loc : Option Loc) (p : Ptr) : KeepsEnv e (ptrAddr loc p) := by
  unfold ptrAddr; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_ptrAddr)

theorem keepsEnv_ptrExpose (loc : Option Loc) (p : Ptr) : KeepsEnv e (ptrExpose loc p) := by
  unfold ptrExpose; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_ptrExpose)

theorem keepsEnv_fromExposed (n : Nat) : KeepsEnv e (fromExposed n) := by
  unfold fromExposed; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_fromExposed)

theorem keepsEnv_resolve (loc : Option Loc) (p : Ptr) (n : Nat) : KeepsEnv e (resolve loc p n) := by
  unfold resolve; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_resolve)

theorem keepsEnv_access (loc : Option Loc) (p : Ptr) (n A : Nat) (w : Bool) :
    KeepsEnv e (access loc p n A w) := by
  intro c r hc e
  simp only [access, bind, Except.bind, pure, Except.pure] at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e; exact hc
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_access)

theorem keepsEnv_fragToBits (loc : Option Loc) (b : Byte) : KeepsEnv e (fragToBits loc b) := by
  unfold fragToBits; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_fragToBits)

theorem keepsEnv_decodeAs (loc : Option Loc) (T : Ty) (bs : List Byte) :
    KeepsEnv e (decodeAs loc T bs) := by
  unfold decodeAs; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_decodeAs)

theorem keepsEnv_loadC (loc : Option Loc) (T : Ty) (A : Nat) (p : Option Ptr) :
    KeepsEnv e (loadC loc T A p) := by
  unfold loadC; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_loadC)

theorem keepsEnv_storeC (loc : Option Loc) (T : Ty) (A : Nat) (v : RVal) (p : Option Ptr) :
    KeepsEnv e (storeC loc T A v p) := by
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
      | ok q => rw [ha] at e; cases e; exact keepsEnv_access loc p _ A true c q hc ha
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_storeC)

theorem keepsEnv_newAlloc (loc : Option Loc) (size align : Nat) (kind : AllocKind) :
    KeepsEnv e (newAlloc loc size align kind) := by
  unfold newAlloc; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_newAlloc)

theorem keepsEnv_freePtr (loc : Option Loc) (family : String) (p : Option Ptr) :
    KeepsEnv e (freePtr loc family p) := by
  unfold freePtr; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_freePtr)

theorem keepsEnv_ptrView (p : Ptr) : KeepsEnv e (ptrView p) := by
  unfold ptrView; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_ptrView)

theorem keepsEnv_cmpPtrs (loc : Option Loc) (pred : Pred) (p q : Ptr) :
    KeepsEnv e (cmpPtrs loc pred p q) := by
  unfold cmpPtrs; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_cmpPtrs)

theorem keepsEnv_factHolds (loc : Option Loc) (f : Fact) (v : RVal) :
    KeepsEnv e (factHolds loc f v) := by
  unfold factHolds ptrFactHolds; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_factHolds)

theorem keepsEnv_asInt (loc : Option Loc) (w : Nat) (v : RVal) : KeepsEnv e (asInt loc w v) := by
  unfold asInt; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_asInt)

theorem keepsEnv_asPtr (loc : Option Loc) (v : RVal) : KeepsEnv e (asPtr loc v) := by
  unfold asPtr; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_asPtr)

theorem keepsEnv_fromOut (loc : Option Loc) (o : OpOut w) : KeepsEnv e (fromOut loc o) := by
  unfold fromOut; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_fromOut)

theorem keepsEnv_evalSimple (loc : Option Loc) (k : OpKind) (rs : List Result) (vs : List RVal) :
    KeepsEnv e (evalSimple loc k rs vs) := by
  unfold evalSimple; keeps
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_evalSimple)

theorem keepsEnv_evalOperand (loc : Option Loc) (o : Operand) : KeepsEnv e (evalOperand loc o) := by
  intro c r hc e
  simp only [evalOperand] at e
  cases h : operandIn c.env loc o with
  | error => rw [h] at e; cases e
  | ok v => rw [h] at e; cases e; exact hc
macro_rules | `(tactic| keeps_lemma) => `(tactic| with_reducible apply keepsEnv_evalOperand)

end

/-- A run of `x` that succeeds runs `x`, then `f` on what it gives. -/
theorem bind_ok {x : CM α} {f : α → CM β} {c : Core} {r : β × Core}
    (e : (x >>= f) c = .ok r) : ∃ a c', x c = .ok (a, c') ∧ f a c' = .ok r := by
  simp only [bind, StateT.bind, Except.bind] at e
  cases ex : x c with
  | error h => rw [ex] at e; cases e
  | ok p => rw [ex] at e; exact ⟨p.1, p.2, rfl, e⟩

/-- Binding results changes only their names. -/
theorem bindAll_other {loc : Option Loc} {n : String} :
    ∀ {rs : List Result} {vs : List RVal} {c c1 : Core}, bindAll loc rs vs c = .ok ((), c1) →
      (∀ r ∈ rs, r.name ≠ n) → c1.env[n]? = c.env[n]?
  | [], [], _, _, e, _ => by cases e; rfl
  | r :: rs, v :: vs, c, c1, e, h => by
    unfold bindAll at e
    dsimp only at e
    split at e
    case isFalse => obtain ⟨_, _, e1, _⟩ := bind_ok e; cases e1
    obtain ⟨_, c'', e3, e4⟩ := bind_ok e
    cases e3
    rw [bindAll_other e4 fun r' hr' => h r' (by simp [hr'])]
    simp [Std.HashMap.getElem?_insert, h r (by simp)]
  | [], _ :: _, _, _, e, _ => by cases e
  | _ :: _, [], _, _, e, _ => by cases e

theorem bindAll_self {loc : Option Loc} {r : Result} {v : RVal} {c c1 : Core}
    (e : bindAll loc [r] [v] c = .ok ((), c1)) : c1.env[r.name]? = some v := by
  unfold bindAll at e
  dsimp only at e
  split at e
  case isFalse => obtain ⟨_, _, e1, _⟩ := bind_ok e; cases e1
  obtain ⟨_, c'', e3, e4⟩ := bind_ok e
  cases e3
  unfold bindAll at e4
  cases e4
  simp

theorem bindResults_bindAll {loc : Option Loc} {rs : List Result} {vs : List RVal} {c c1 : Core}
    (e : bindResults loc rs vs c = .ok ((), c1)) :
    ∃ c', bindAll loc rs vs c = .ok ((), c') ∧ c1.env = c'.env := by
  unfold bindResults at e
  obtain ⟨_, c', e1, e2⟩ := bind_ok e
  refine ⟨c', e1, ?_⟩
  exact (by keeps : KeepsEnv c'.env _) c' _ rfl e2

/-- A simple op changes the environment only at its results. -/
theorem simpleOp_other {loc : Option Loc} {k : OpKind} {res : List Result} {args : List Operand}
    {c c1 : Core} {n : String} (e : simpleOp loc k res args c = .ok ((), c1))
    (h : ∀ r ∈ res, r.name ≠ n) : c1.env[n]? = c.env[n]? := by
  unfold simpleOp at e
  obtain ⟨vs, c2, e1, e2⟩ := bind_ok e
  obtain ⟨out, c3, e3, e4⟩ := bind_ok e2
  have h2 : c2.env = c.env := Keeps.mapM' (fun o => keepsEnv_evalOperand loc o) c _ rfl e1
  have h3 : c3.env = c2.env := keepsEnv_evalSimple loc k res vs c2 _ rfl e3
  obtain ⟨c', e5, h5⟩ := bindResults_bindAll e4
  rw [h5, bindAll_other e5 h, h3, h2]

/-! ## Substitution -/

/-- Read `%x` where an operand reads `%y`. -/
def substOperand (x y : String) : Operand → Operand
  | .var n => .var (if n = y then x else n)
  | o => o

/-- Read `%x` where an op's operands read `%y`. Regions are left alone. -/
def substOp (x y : String) : Op → Op
  | .mk k res args rs loc => .mk k res (args.map (substOperand x y)) rs loc

/-- `%x` and `%y` are both defined, with the same value. -/
def Agree (env : Env) (x y : String) : Prop := ∃ v, env[x]? = some v ∧ env[y]? = some v

theorem operandIn_subst {env : Env} {x y : String} (h : Agree env x y) (loc : Option Loc)
    (o : Operand) : operandIn env loc (substOperand x y o) = operandIn env loc o := by
  cases o with
  | var n =>
    by_cases hn : n = y
    · subst hn
      obtain ⟨v, hx, hy⟩ := h
      simp [substOperand, operandIn, hx, hy]
    · simp [substOperand, hn]
  | hole => rfl

theorem mapM_subst {c : Core} {x y : String} (h : Agree c.env x y) (loc : Option Loc) :
    ∀ args : List Operand,
      (args.map (substOperand x y)).mapM (evalOperand loc) c = args.mapM (evalOperand loc) c
  | [] => rfl
  | o :: args => by
    simp only [List.map_cons, List.mapM_cons, bind, StateT.bind, evalOperand,
      operandIn_subst h loc o]
    cases operandIn c.env loc o with
    | error => rfl
    | ok v =>
      simp only [Except.map, Except.ok_bind]
      rw [mapM_subst h loc args]

theorem simpleOp_subst {c : Core} {x y : String} (h : Agree c.env x y) (loc : Option Loc)
    (k : OpKind) (res : List Result) (args : List Operand) :
    simpleOp loc k res (args.map (substOperand x y)) c = simpleOp loc k res args c := by
  simp only [simpleOp, bind, StateT.bind]
  rw [mapM_subst h loc args]


theorem exec_mapM_subst {m : Machine} {x y : String} (h : Agree m.core.env x y) (loc : Option Loc)
    (args : List Operand) :
    m.exec ((args.map (substOperand x y)).mapM (evalOperand loc)) =
      m.exec (args.mapM (evalOperand loc)) := by
  simp only [Machine.exec, StateT.run, mapM_subst h loc args]

/-! ## The rewrite -/

/-- An op the substitution may cross: it has no regions, calls no function, and binds neither
`%x` nor `%y`. -/
def Flat (x y : String) (o : Op) : Prop :=
  ∃ k res args loc, o = .mk k res args [] loc ∧ k.callee? = none ∧
    ∀ r ∈ res, r.name ≠ x ∧ r.name ≠ y

/-- `%y: T = copy %x`. -/
def copyOp (x y : String) (T : Ty) (facts : List TrustedFact) (loc : Option Loc) : Op :=
  .mk .copy [⟨y, T, facts⟩] [.var x] [] loc

/-- The rewrite: after `%y = copy %x`, the ops `ss` read `%x` where they read `%y`. -/
def L (pt ps : List Op) : Prop :=
  ∃ x y T facts loc ss, x ≠ y ∧ (∀ o ∈ ss, Flat x y o) ∧
    ps = copyOp x y T facts loc :: ss ∧ pt = copyOp x y T facts loc :: ss.map (substOp x y)

/-- After the copy: the target is about to run the substituted ops, the source the original
ones, and `%x` and `%y` agree. -/
def Mid (mt ms : Machine) : Prop :=
  mt.core = ms.core ∧ ∃ x y ss t s ids rt rs, (∀ o ∈ ss, Flat x y o) ∧
    mt.stack = .block (ss.map (substOp x y) ++ t) ids :: rt ∧
    ms.stack = .block (ss ++ s) ids :: rs ∧ OpsRel L t s ∧ Forall2 (FrameRel L) rt rs ∧
    Agree ms.core.env x y

/-- Related states: in lockstep, or inside a substituted run of ops. -/
def R (mt ms : Machine) : Prop := MRel L mt ms ∨ Mid mt ms

/-! ## Steps -/

/-- Running the copy makes `%x` and `%y` agree. -/
theorem copy_agree {loc : Option Loc} {x y : String} {T : Ty} {facts : List TrustedFact}
    {c c1 : Core} (hxy : x ≠ y)
    (e : simpleOp loc .copy [⟨y, T, facts⟩] [.var x] c = .ok ((), c1)) : Agree c1.env x y := by
  rw [Fwd.simpleOp_one] at e
  cases hx : operandIn c.env loc (.var x) with
  | error h => rw [hx] at e; cases e
  | ok v =>
    rw [hx] at e
    simp only [Except.bind, Fwd.evalSimple_copy] at e
    obtain ⟨c', e1, h1⟩ := bindResults_bindAll e
    have hv : c.env[x]? = some v := by
      simp only [operandIn] at hx
      split at hx
      · cases hx; assumption
      · cases hx
    refine ⟨v, ?_, ?_⟩
    · rw [h1, bindAll_other e1 (by simpa using fun h => hxy h.symm), hv]
    · rw [h1]; exact bindAll_self e1

/-- One target step matched by one source step that runs the same core computation. -/
theorem step_same' {mt ms : Machine} {x : Except Halt (α × Core)} {ft fs : α → Core → Machine}
    (ht : step mt = x.bind fun p => .ok (ft p.1 p.2))
    (hs : step ms = x.bind fun p => .ok (fs p.1 p.2)) (hshape : ms.shape = mt.shape)
    (hR : ∀ a core, x = .ok (a, core) → R (ft a core) (fs a core)) : StepMatch R mt ms := by
  cases x with
  | ok p =>
    refine ⟨fun mt' e => ?_, fun h e => ?_⟩
    · rw [ht] at e
      cases e
      refine .inr ⟨0, fs p.1 p.2, by rw [runSteps_one, hs]; rfl, hR p.1 p.2 rfl, ?_⟩
      intro j mj hj ej
      obtain rfl : j = 0 := by omega
      simp only [runSteps, Except.ok.injEq] at ej
      subst ej
      exact hshape
    · rw [ht] at e; cases e
  | error h' =>
    refine ⟨fun mt' e => ?_, fun h e => ?_⟩
    · rw [ht] at e; cases e
    · rw [ht] at e
      cases e
      by_cases hamb : h'.behavior = .ambiguous
      · exact .inl ⟨1, h', by rw [runSteps_one, hs]; rfl, .inr hamb⟩
      · exact .inr ⟨1, h', by rw [runSteps_one, hs]; rfl, Behavior.Refines.refl _ hamb⟩

/-- At a rewritten spot, both run the copy, and land in the substituted run of ops. -/
theorem step_copy {mt ms : Machine} {x y : String} {T : Ty} {facts : List TrustedFact}
    {loc : Option Loc} {ss t s : List Op} {ids : List Nat} {rt rs : List Frame}
    (hc : mt.core = ms.core) (hxy : x ≠ y) (hflat : ∀ o ∈ ss, Flat x y o) (hts : OpsRel L t s)
    (hrest : Forall2 (FrameRel L) rt rs)
    (ht : mt.stack = .block (copyOp x y T facts loc :: (ss.map (substOp x y) ++ t)) ids :: rt)
    (hs : ms.stack = .block (copyOp x y T facts loc :: (ss ++ s)) ids :: rs) :
    StepMatch R mt ms := by
  refine step_same' (x := simpleOp loc .copy [⟨y, T, facts⟩] [.var x] ms.core)
    (ft := fun _ core => { core, stack := .block (ss.map (substOp x y) ++ t) ids :: rt })
    (fs := fun _ core => { core, stack := .block (ss ++ s) ids :: rs }) ?_ ?_ ?_ ?_
  · simp only [step, ht, copyOp, execOp_simple _ .copy _ _ _ rfl rfl rfl, hc]
    cases simpleOp loc .copy [⟨y, T, facts⟩] [.var x] ms.core <;> rfl
  · simp only [step, hs, copyOp, execOp_simple _ .copy _ _ _ rfl rfl rfl]
    cases simpleOp loc .copy [⟨y, T, facts⟩] [.var x] ms.core <;> rfl
  · simp only [Machine.shape, ht, hs]
    exact (shape_cons rfl hrest).symm
  · intro _ core e
    exact .inr ⟨rfl, x, y, ss, t, s, ids, rt, rs, hflat, rfl, rfl, hts, hrest, copy_agree hxy e⟩

/-- Inside the substituted run: both run the next op, reading the same values. -/
theorem step_mid {cm : Core} {x y : String} {o : Op} {ss t s : List Op} {ids : List Nat}
    {rt rs : List Frame} (hflat : ∀ o' ∈ o :: ss, Flat x y o') (hts : OpsRel L t s)
    (hrest : Forall2 (FrameRel L) rt rs) (hag : Agree cm.env x y) :
    StepMatch R ⟨cm, .block (substOp x y o :: (ss.map (substOp x y) ++ t)) ids :: rt⟩
      ⟨cm, .block (o :: (ss ++ s)) ids :: rs⟩ := by
  obtain ⟨k, res, args, loc, rfl, hcallee, hres⟩ := hflat o (by simp)
  have hflat' : ∀ o' ∈ ss, Flat x y o' := fun o' h => hflat o' (by simp [h])
  let mt : Machine :=
    ⟨cm, .block (substOp x y (.mk k res args [] loc) :: (ss.map (substOp x y) ++ t)) ids :: rt⟩
  let ms : Machine := ⟨cm, .block (.mk k res args [] loc :: (ss ++ s)) ids :: rs⟩
  have hshape : ms.shape = mt.shape := by
    simp only [Machine.shape, mt, ms]
    exact (shape_cons rfl hrest).symm
  have hagT := hag
  -- The machines with the op popped.
  let xt : Machine := { core := cm, stack := .block (ss.map (substOp x y) ++ t) ids :: rt }
  let xs : Machine := { core := cm, stack := .block (ss ++ s) ids :: rs }
  have stepT : step mt = execFlat xt k res (args.map (substOperand x y)) loc := by
    simp only [step, execOp]; rfl
  have stepS : step ms = execFlat xs k res args loc := by
    simp only [step, execOp]; rfl
  -- Whatever binds only `res` keeps `%x` and `%y` agreeing.
  have keep : ∀ c1 : Core, (∀ n, (∀ r ∈ res, r.name ≠ n) → c1.env[n]? = cm.env[n]?) →
      Agree c1.env x y := by
    intro c1 h
    obtain ⟨v, hx, hy⟩ := hag
    exact ⟨v, (h x fun r hr => (hres r hr).1).trans hx, (h y fun r hr => (hres r hr).2).trans hy⟩
  cases hsa : k.stackAlloc? with
  | some sa =>
    obtain ⟨size, align⟩ := sa
    let idOf (p : Ptr) : Nat := match p with | .rel a .. => a | _ => 0
    refine step_same' (x := (newAlloc loc size align .stack >>= fun p =>
        bindResults loc res [.ptr (some p)] >>= fun _ => pure p) cm)
      (ft := fun p core => { core, stack := .block (ss.map (substOp x y) ++ t) (idOf p :: ids) :: rt })
      (fs := fun p core => { core, stack := .block (ss ++ s) (idOf p :: ids) :: rs }) ?_ ?_ hshape ?_
    · rw [stepT]
      simp only [execFlat, hcallee, hsa, Machine.exec, StateT.run, xt]
      cases (newAlloc loc size align .stack >>= fun p =>
        bindResults loc res [.ptr (some p)] >>= fun _ => pure p) cm <;> rfl
    · rw [stepS]
      simp only [execFlat, hcallee, hsa, Machine.exec, StateT.run, xs]
      cases (newAlloc loc size align .stack >>= fun p =>
        bindResults loc res [.ptr (some p)] >>= fun _ => pure p) cm <;> rfl
    · intro p core e
      refine .inr ⟨rfl, x, y, ss, t, s, idOf p :: ids, rt, rs, hflat', rfl, rfl, hts, hrest, ?_⟩
      obtain ⟨p', c2, e1, e2⟩ := bind_ok e
      obtain ⟨_, c3, e3, e4⟩ := bind_ok e2
      cases e4
      have h2 : c2.env = cm.env := keepsEnv_newAlloc loc size align .stack cm _ rfl e1
      obtain ⟨c', e5, h5⟩ := bindResults_bindAll e3
      exact keep core fun n hn => by rw [h5, bindAll_other e5 hn, h2]
  | none =>
  cases hterm : k.isTerminator with
  | true =>
    have lock : Lockstep L (step mt) (step ms) := by
      rw [stepT, stepS]
      simp only [execFlat, hcallee, hsa, hterm, ite_true, xt, xs]
      rw [exec_mapM_subst (m := ⟨cm, _⟩) hagT]
      refine lockstep_exec rfl fun vs core => ?_
      simp only [blockIds, List.append_nil]
      refine lockstep_exec rfl fun _ core' => ?_
      exact terminate_eq (mt := ⟨core', rt⟩) (ms := ⟨core', rs⟩) (MRel.mk' rfl hrest) loc k vs
    exact (StepMatch.of_lockstep' hshape lock).mono fun _ _ _ _ h => .inl h
  | false =>
    refine step_same' (x := simpleOp loc k res args cm)
      (ft := fun _ core => { core, stack := .block (ss.map (substOp x y) ++ t) ids :: rt })
      (fs := fun _ core => { core, stack := .block (ss ++ s) ids :: rs }) ?_ ?_ hshape ?_
    · rw [stepT]
      simp only [execFlat, hcallee, hsa, hterm, Bool.false_eq_true, ite_false, Machine.exec,
        StateT.run, xt, simpleOp_subst hag]
      cases simpleOp loc k res args cm <;> rfl
    · rw [stepS]
      simp only [execFlat, hcallee, hsa, hterm, Bool.false_eq_true, ite_false, Machine.exec,
        StateT.run, xs]
      cases simpleOp loc k res args cm <;> rfl
    · intro _ core e
      exact .inr ⟨rfl, x, y, ss, t, s, ids, rt, rs, hflat', rfl, rfl, hts, hrest,
        keep core fun n hn => simpleOp_other e hn⟩


theorem opsRel_cons {ot : Op} {t s0 : List Op} (h : OpsRel L (ot :: t) s0) :
    (∃ os s, s0 = os :: s ∧ OpRel L ot os ∧ OpsRel L t s) ∨
    (∃ x y T facts loc ss t' s', ot = copyOp x y T facts loc ∧ t = ss.map (substOp x y) ++ t' ∧
      s0 = copyOp x y T facts loc :: (ss ++ s') ∧ x ≠ y ∧ (∀ o ∈ ss, Flat x y o) ∧
      OpsRel L t' s') := by
  generalize hx : ot :: t = x at h
  cases h with
  | refl => subst hx; exact .inl ⟨_, _, rfl, .refl _, .refl _⟩
  | cons ho hr =>
    injection hx with h1 h2
    subst h1 h2
    exact .inl ⟨_, _, rfl, ho, hr⟩
  | rw hl hr =>
    obtain ⟨x, y, T, facts, loc, ss, hxy, hflat, rfl, rfl⟩ := hl
    simp only [List.cons_append, List.cons.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact .inr ⟨x, y, T, facts, loc, ss, _, _, rfl, rfl, rfl, hxy, hflat, hr⟩

theorem opsRel_nil {s0 : List Op} (h : OpsRel L [] s0) : s0 = [] := by
  generalize hx : ([] : List Op) = x at h
  cases h with
  | refl => rfl
  | cons => cases hx
  | rw hl _ =>
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := hl
    cases hx

/-- From states in lockstep: a lockstep step, or the copy at a rewritten spot. -/
theorem sim_mrel {mt ms : Machine} (hc : mt.core = ms.core)
    (hst : Forall2 (FrameRel L) mt.stack ms.stack) : StepMatch R mt ms := by
  have lock : (∀ ot t ids rt, mt.stack = .block (ot :: t) ids :: rt →
        ∃ os s rs, ms.stack = .block (os :: s) ids :: rs ∧ OpRel L ot os ∧ OpsRel L t s) →
      (∀ ids rt, mt.stack = .block [] ids :: rt → ∃ rs, ms.stack = .block [] ids :: rs) →
      StepMatch R mt ms := fun hh hn =>
    (StepMatch.of_lockstep ⟨hc, hst⟩ (step_eq ⟨hc, hst⟩ hh hn)).mono fun _ _ _ _ h => .inl h
  cases ht : mt.stack with
  | nil =>
    exact lock (fun _ _ _ _ e => by rw [ht] at e; cases e) (fun _ _ e => by rw [ht] at e; cases e)
  | cons f rt =>
    cases hs : ms.stack with
    | nil => rw [ht, hs] at hst; exact hst.elim
    | cons f' rs =>
      have hst' := hst
      rw [ht, hs] at hst'
      obtain ⟨hf, hrest⟩ := hst'
      cases hf with
      | refl f =>
        refine lock (fun ot t ids rt' e => ?_) (fun ids rt' e => ?_)
        · rw [ht, List.cons.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          exact ⟨ot, t, rs, hs, .refl _, .refl _⟩
        · rw [ht, List.cons.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          exact ⟨rs, hs⟩
      | block hops =>
        rename_i t0 s0 ids
        cases t0 with
        | nil =>
          obtain rfl := opsRel_nil hops
          refine lock (fun ot t ids' rt' e => ?_) (fun ids' rt' e => ?_)
          · rw [ht] at e; simp at e
          · rw [ht, List.cons.injEq, Frame.block.injEq] at e
            obtain ⟨⟨-, rfl⟩, rfl⟩ := e
            exact ⟨rs, hs⟩
        | cons ot t =>
          rcases opsRel_cons hops with ⟨os, s, rfl, ho, hts⟩ |
            ⟨x, y, T, facts, loc, ss, t', s', rfl, rfl, rfl, hxy, hflat, hts⟩
          · refine lock (fun ot' t' ids' rt' e => ?_) (fun ids' rt' e => ?_)
            · rw [ht, List.cons.injEq, Frame.block.injEq, List.cons.injEq] at e
              obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := e
              exact ⟨os, s, rs, hs, ho, hts⟩
            · rw [ht] at e; simp at e
          · exact step_copy hc hxy hflat hts hrest ht hs
      | loop hb =>
        refine lock (fun _ _ _ _ e => ?_) (fun _ _ e => ?_) <;> (rw [ht] at e; simp at e)

theorem sim : Simulation R := by
  intro mt ms hR
  rcases hR with ⟨hc, hst⟩ | ⟨hc, x, y, ss, t, s, ids, rt, rs, hflat, ht, hs, hts, hrest, hag⟩
  · exact sim_mrel hc hst
  cases ss with
  | nil =>
    refine sim_mrel hc ?_
    rw [ht, hs]
    exact ⟨.block hts, hrest⟩
  | cons o ss =>
    obtain ⟨cmt, stt⟩ := mt
    obtain ⟨cms, sts⟩ := ms
    dsimp only at hc ht hs hag
    subst hc ht hs
    simp only [List.map_cons, List.cons_append]
    exact step_mid hflat hts hrest hag

theorem init_match {mod : Module} {tgt src : Func} (hparams : tgt.params = src.params)
    (hrets : tgt.rets = src.rets) (hops : OpsRel L tgt.body.ops src.body.ops)
    (oracle : Nat → Int) (args : List RVal) :
    InitMatch R (Machine.init oracle mod tgt args) (Machine.init oracle mod src args) := by
  simp only [Machine.init, hparams, hrets, bind, Except.bind]
  cases (enterCall none src.params args).run (Core.initial oracle mod) with
  | error h =>
    by_cases hamb : h.behavior = .ambiguous
    · exact .inl ⟨h, rfl, .inr hamb⟩
    · exact .inr (.inr ⟨h, h, rfl, rfl, Behavior.Refines.refl _ hamb⟩)
  | ok r =>
    exact .inr (.inl ⟨_, _, rfl, rfl, .inl (MRel.mk' rfl
      (Forall2.cons' (.block hops) (Forall2.cons' (.refl _) trivial)))⟩)

/-- **Copy propagation is correct.** Making, anywhere in a function, the ops right after
`%y = copy %x` in the same block read `%x` where they read `%y` gives a function that refines the
original, for every argument and every oracle. The ops rewritten must have no regions, call no
function, and bind neither `%x` nor `%y`; the run may end with a terminator. -/
theorem refines {mod : Module} {tgt src : Func} (hparams : tgt.params = src.params)
    (hrets : tgt.rets = src.rets) (hops : OpsRel L tgt.body.ops src.body.ops)
    (dec : src.Decided mod) : tgt.Refines mod src :=
  Simulation.refines sim (fun oracle args => ⟨oracle, init_match hparams hrets hops oracle args⟩)
    dec

/-! ## Look-alikes that are wrong -/

/-- Reading `%x` for `%y` is wrong once the two hold different values, as they do after an op
rebinds `%x`. This is why the ops crossed may bind neither. -/
theorem subst_after_rebind_wrong :
    ¬ ∀ (env : Env) (loc : Option Loc),
      operandIn env loc (substOperand "x" "y" (.var "y")) = operandIn env loc (.var "y") := by
  intro h
  have := h (((∅ : Env).insert "x" (.int 8 .poison)).insert "y" (.int 8 (.bits 1))) none
  simp [substOperand, operandIn, Std.HashMap.getElem_insert,
    pure, Except.pure] at this

end Fir.CopyProp
