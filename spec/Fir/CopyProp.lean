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
new fact is an invariant on the source's environment: after the copy, looking up `%x` and `%y`
gives the same value, and the ops crossed don't rebind either, so reading one is reading the
other.
-/

namespace Fir.CopyProp

/-! ## Lookups after binding -/

/-- Binding names in the top block changes lookups of those names only. -/
theorem lookup_bindAll {n : String} {o : List Op} {ids : List Nat} {env : Env} {fs : List Frame}
    {rs : List Result} {vs : List RVal} (h : ∀ r ∈ rs, r.name ≠ n) :
    lookup n (.block o ids (env.bindAll rs vs) :: fs) = lookup n (.block o ids env :: fs) := by
  simp only [lookup, Env.getElem?_bindAll env rs vs h]

theorem lookup_bindTop {n : String} {o : List Op} {ids : List Nat} {env : Env} {fs : List Frame}
    {rs : List Result} {vs : List RVal} (h : ∀ r ∈ rs, r.name ≠ n) :
    lookup n (bindTop rs vs (.block o ids env :: fs)) = lookup n (.block o ids env :: fs) :=
  lookup_bindAll h

theorem lookup_addAllocId {n : String} {o : List Op} {ids : List Nat} {env : Env}
    {fs : List Frame} (a : Nat) :
    lookup n (addAllocId a (.block o ids env :: fs)) = lookup n (.block o ids env :: fs) := rfl

/-! ## Substitution -/

/-- Read `%x` where an operand reads `%y`. -/
def substOperand (x y : String) : Operand → Operand
  | .var n => .var (if n = y then x else n)
  | o => o

/-- Read `%x` where an op's operands read `%y`. Regions are left alone. -/
def substOp (x y : String) : Op → Op
  | .mk k res args rs loc => .mk k res (args.map (substOperand x y)) rs loc

/-- Looking up `%x` and `%y` in `fs` gives the same value. -/
def Agree (fs : List Frame) (x y : String) : Prop :=
  ∃ v, lookup x fs = some v ∧ lookup y fs = some v

/-- An operand reading `%x` for `%y` on the target has the value the original has on the source,
when the stacks' lookups agree on what the target reads and `%x` and `%y` agree on the source. -/
theorem operandIn_subst {ft fs : List Frame} {x y : String} (hag : Agree fs x y)
    (hl : ∀ n, (substOperand x y a).reads n = true → lookup n ft = lookup n fs) (loc : Option Loc) :
    operandIn ft loc (substOperand x y a) = operandIn fs loc a := by
  cases a with
  | var n =>
    by_cases hn : n = y
    · subst hn
      obtain ⟨v, hx, hy⟩ := hag
      have := hl x (by simp [substOperand, Operand.reads])
      simp [substOperand, operandIn, this, hx, hy]
    · have := hl n (by simp [substOperand, Operand.reads, hn])
      simp [substOperand, operandIn, hn, this]
  | hole => rfl

theorem operands_subst {ft fs : List Frame} {x y : String} (hag : Agree fs x y) (loc : Option Loc) :
    ∀ {args : List Operand},
      (∀ n, (args.map (substOperand x y)).any (Operand.reads n) = true →
        lookup n ft = lookup n fs) →
      operands ft loc (args.map (substOperand x y)) = operands fs loc args
  | [], _ => rfl
  | a :: args, hl => by
    have h1 := operandIn_subst (a := a) hag (fun n hn => hl n (by simp [hn])) loc
    have h2 := operands_subst hag loc (args := args) (fun n hn => hl n (by
      simp only [List.map_cons, List.any_cons, Bool.or_eq_true]; exact .inr hn))
    simp only [operands, List.map_cons, List.mapM_cons] at h2 ⊢
    rw [h1, h2]

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
def L (pt ps _ : List Op) : Prop :=
  ∃ x y T facts loc ss, x ≠ y ∧ (∀ o ∈ ss, Flat x y o) ∧
    ps = copyOp x y T facts loc :: ss ∧ pt = copyOp x y T facts loc :: ss.map (substOp x y)

/-- After the copy: the target is about to run the substituted ops, the source the original
ones, and `%x` and `%y` agree on the source. Apart from that, the top blocks are related as in
lockstep. -/
def Mid (mt ms : Machine) : Prop :=
  mt.core = ms.core ∧ ∃ D Db x y ss t s ids et es ft fs, (∀ o ∈ ss, Flat x y o) ∧
    mt.stack = .block (ss.map (substOp x y) ++ t) ids et :: ft ∧
    ms.stack = .block (ss ++ s) ids es :: fs ∧ OpsRel L t s ∧ StackRel L Db ft fs ∧
    (∀ n, Db n → D n) ∧ EnvAgree D et es ∧ NoReads D (ss.map (substOp x y) ++ t) ∧
    Agree ms.stack x y

/-- Related states: in lockstep, or inside a substituted run of ops. -/
def R (mt ms : Machine) : Prop := MRel L mt ms ∨ Mid mt ms

/-! ## Steps -/

/-- Lookups on two stacks whose top blocks' environments agree outside `D`, with related frames
below, agree outside `D`, whatever code the blocks hold. -/
theorem lookup_agree {D Db : String → Prop} {ot os : List Op} {ids : List Nat} {et es : Env}
    {ft fs : List Frame} (hb : StackRel L Db ft fs) (hDb : ∀ n, Db n → D n)
    (hag : EnvAgree D et es) {n : String} (hn : ¬ D n) :
    lookup n (.block ot ids et :: ft) = lookup n (.block os ids es :: fs) := by
  rw [lookup_ops n ot [], lookup_ops n os []]
  exact (StackRel.block hb hDb (.refl []) hag (fun _ _ => rfl)).lookup hn

/-- At a rewritten spot, both run the copy, and land in the substituted run of ops. -/
theorem step_copy {mt ms : Machine} {x y : String} {T : Ty} {facts : List TrustedFact}
    {loc : Option Loc} {ss t s : List Op} {ids : List Nat} {et es : Env} {ft fs : List Frame}
    {D Db : String → Prop} (hc : mt.core = ms.core) (hxy : x ≠ y)
    (hflat : ∀ o ∈ ss, Flat x y o) (hts : OpsRel L t s) (hb : StackRel L Db ft fs)
    (hDb : ∀ n, Db n → D n) (hag : EnvAgree D et es)
    (hnr : NoReads D (copyOp x y T facts loc :: (ss.map (substOp x y) ++ t)))
    (ht : mt.stack = .block (copyOp x y T facts loc :: (ss.map (substOp x y) ++ t)) ids et :: ft)
    (hs : ms.stack = .block (copyOp x y T facts loc :: (ss ++ s)) ids es :: fs) :
    StepMatch R mt ms := by
  obtain ⟨c, stt⟩ := mt
  obtain ⟨cs, sts⟩ := ms
  dsimp only at hc ht hs
  subst hc ht hs
  obtain ⟨hrc, hnr'⟩ := NoReads.cons hnr
  have hx : ¬ D x := fun h => by have := hrc x h; simp [copyOp, Op.reads, Operand.reads] at this
  let S : List Frame := .block (ss ++ s) ids es :: fs
  refine step_same
    (x := (operands S loc [.var x]).bind fun vs => simpleOp loc .copy [⟨y, T, facts⟩] vs c)
    (ft := fun outs core => ⟨core, bindTop [⟨y, T, facts⟩] outs
      (.block (ss.map (substOp x y) ++ t) ids et :: ft)⟩)
    (fs := fun outs core => ⟨core, bindTop [⟨y, T, facts⟩] outs S⟩) ?_ ?_ ?_ ?_
  · rw [copyOp, step_simple rfl rfl rfl, operands_one, operands_one]
    simp only [operandIn]
    rw [lookup_agree (os := ss ++ s) hb hDb hag hx]
  · rw [copyOp, step_simple rfl rfl rfl]
  · simp only [Machine.shape]
    exact (shape_cons rfl hb).symm
  · intro outs core e
    rw [operands_one] at e
    cases hv : operandIn S loc (.var x) with
    | error h => rw [hv] at e; cases e
    | ok v =>
    rw [hv] at e
    simp only [Except.bind, Fwd.simpleOp_eq, Fwd.evalSimple_copy] at e
    cases hcr : checkResults loc [⟨y, T, facts⟩] [v] c with
    | error h => rw [hcr] at e; cases e
    | ok q =>
    rw [hcr] at e
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have hlx : lookup x S = some v := by
      simp only [operandIn] at hv
      split at hv
      · cases hv; assumption
      · cases hv
    refine .inr ⟨rfl, D, Db, x, y, ss, t, s, ids, _, _, ft, fs, hflat, rfl, rfl, hts, hb, hDb,
      hag.bindAll _ _, hnr', v, ?_, ?_⟩
    · show lookup x (bindTop _ _ S) = some v
      rw [lookup_bindTop (by simpa using fun h => hxy h.symm)]
      exact hlx
    · simp [S, bindTop, lookup, Env.bindAll]

/-- Inside the substituted run: both run the next op, reading the same values. -/
theorem step_mid {cm : Core} {x y : String} {o : Op} {ss t s : List Op} {ids : List Nat}
    {et es : Env} {ft fs : List Frame} {D Db : String → Prop}
    (hflat : ∀ o' ∈ o :: ss, Flat x y o') (hts : OpsRel L t s) (hb : StackRel L Db ft fs)
    (hDb : ∀ n, Db n → D n) (hag : EnvAgree D et es)
    (hnr : NoReads D (substOp x y o :: (ss.map (substOp x y) ++ t)))
    (hxy : Agree (.block (o :: (ss ++ s)) ids es :: fs) x y) :
    StepMatch R ⟨cm, .block (substOp x y o :: (ss.map (substOp x y) ++ t)) ids et :: ft⟩
      ⟨cm, .block (o :: (ss ++ s)) ids es :: fs⟩ := by
  obtain ⟨k, res, args, loc, rfl, hcallee, hres⟩ := hflat o (by simp)
  have hflat' : ∀ o' ∈ ss, Flat x y o' := fun o' h => hflat o' (by simp [h])
  obtain ⟨hro, hnr'⟩ := NoReads.cons hnr
  have hargs := (Op.reads_mk hro).1
  -- The machines with the op popped.
  let T0 : List Frame := .block (ss.map (substOp x y) ++ t) ids et :: ft
  let S0 : List Frame := .block (ss ++ s) ids es :: fs
  have hag0 : Agree S0 x y := by
    obtain ⟨v, h1, h2⟩ := hxy; exact ⟨v, by rw [← h1]; rfl, by rw [← h2]; rfl⟩
  have hops : operands T0 loc (args.map (substOperand x y)) = operands S0 loc args := by
    refine operands_subst hag0 loc fun n hn => lookup_agree hb hDb hag fun hd => ?_
    have := hargs n hd
    simp_all
  have hshape : (Machine.mk cm (.block (.mk k res args [] loc :: (ss ++ s)) ids es :: fs)).shape =
      (Machine.mk cm (.block (substOp x y (.mk k res args [] loc) ::
        (ss.map (substOp x y) ++ t)) ids et :: ft)).shape := by
    simp only [Machine.shape]
    exact (shape_cons rfl hb).symm
  -- What binds only `res` keeps `%x` and `%y` agreeing.
  have keep : ∀ (f : List Frame → List Frame),
      (∀ n, (∀ r ∈ res, r.name ≠ n) → lookup n (f S0) = lookup n S0) → Agree (f S0) x y := by
    intro f hf
    obtain ⟨v, h1, h2⟩ := hag0
    exact ⟨v, by rw [hf x fun r hr => (hres r hr).1, h1], by rw [hf y fun r hr => (hres r hr).2, h2]⟩
  -- The new top blocks are related as in lockstep.
  have mid : ∀ (f : List Frame → List Frame) ids' et' es',
      f T0 = .block (ss.map (substOp x y) ++ t) ids' et' :: ft →
      f S0 = .block (ss ++ s) ids' es' :: fs → EnvAgree D et' es' →
      (∀ n, (∀ r ∈ res, r.name ≠ n) → lookup n (f S0) = lookup n S0) →
      ∀ core, R ⟨core, f T0⟩ ⟨core, f S0⟩ := by
    intro f ids' et' es' e1 e2 hag' hf core
    exact .inr ⟨rfl, D, Db, x, y, ss, t, s, ids', et', es', ft, fs, hflat', e1, e2, hts, hb, hDb,
      hag', hnr', keep f hf⟩
  have stepT : step ⟨cm, .block (substOp x y (.mk k res args [] loc) ::
      (ss.map (substOp x y) ++ t)) ids et :: ft⟩ =
      execFlat ⟨cm, T0⟩ k res (args.map (substOperand x y)) loc := rfl
  have stepS : step ⟨cm, .block (.mk k res args [] loc :: (ss ++ s)) ids es :: fs⟩ =
      execFlat ⟨cm, S0⟩ k res args loc := rfl
  cases hsa : k.stackAlloc? with
  | some sa =>
    generalize hd : sa cm.space = dims
    obtain ⟨size, align⟩ := dims
    let idOf (p : Ptr) : Nat := match p with | .rel a .. => a | _ => 0
    refine step_same (x := (newAlloc loc size align .stack >>= fun p =>
        checkResults loc res [.ptr (some p)] >>= fun _ => pure p) cm)
      (ft := fun p core => ⟨core, bindTop res [.ptr (some p)] (addAllocId (idOf p) T0)⟩)
      (fs := fun p core => ⟨core, bindTop res [.ptr (some p)] (addAllocId (idOf p) S0)⟩)
      ?_ ?_ hshape ?_
    · rw [stepT]
      simp only [execFlat, hcallee, hsa, hd, Machine.exec, StateT.run]
      cases (newAlloc loc size align .stack >>= fun p =>
        checkResults loc res [.ptr (some p)] >>= fun _ => pure p) cm <;> rfl
    · rw [stepS]
      simp only [execFlat, hcallee, hsa, hd, Machine.exec, StateT.run]
      cases (newAlloc loc size align .stack >>= fun p =>
        checkResults loc res [.ptr (some p)] >>= fun _ => pure p) cm <;> rfl
    · intro p core _
      exact mid (fun fs => bindTop res [.ptr (some p)] (addAllocId (idOf p) fs)) _ _ _ rfl rfl
        ((hag.bindAll _ _)) (fun n hn => by
          simp only [S0, addAllocId, lookup_bindTop hn]; rfl) core
  | none =>
  cases hterm : k.isTerminator with
  | true =>
    have lock : Lockstep L
        (execFlat ⟨cm, T0⟩ k res (args.map (substOperand x y)) loc)
        (execFlat ⟨cm, S0⟩ k res args loc) := by
      simp only [execFlat, hcallee, hsa, hterm, ite_true, hops]
      refine lockstep_bind fun vs => ?_
      simp only [T0, S0, blockIds, List.append_nil]
      refine lockstep_exec rfl fun _ core => ?_
      exact terminate_eq hb loc k vs
    rw [← stepT, ← stepS] at lock
    exact (StepMatch.of_lockstep hshape lock).mono fun _ _ _ _ h => .inl h
  | false =>
    refine step_same
      (x := (operands S0 loc args).bind fun vs => simpleOp loc k res vs cm)
      (ft := fun outs core => ⟨core, bindTop res outs T0⟩)
      (fs := fun outs core => ⟨core, bindTop res outs S0⟩) ?_ ?_ hshape ?_
    · rw [show substOp x y (.mk k res args [] loc) = .mk k res (args.map (substOperand x y)) [] loc
        from rfl, step_simple hcallee hsa hterm, hops]
    · rw [step_simple hcallee hsa hterm]
    · intro outs core _
      exact mid (bindTop res outs) _ _ _ rfl rfl (hag.bindAll _ _)
        (fun n hn => lookup_bindTop hn) core

theorem sim : Simulation R := by
  intro mt ms hR
  rcases hR with hR | ⟨hc, D, Db, x, y, ss, t, s, ids, et, es, ft, fs, hflat, ht, hs, hts, hb, hDb,
    hag, hnr, hxy⟩
  · refine StepMatch.of_mrel hR (fun _ _ _ _ h => .inl h) ?_
    intro D Db pt ps t s ids et es ft fs hl hts hb hDb hag hnr ht hs
    obtain ⟨x, y, T, facts, loc, ss, hxy, hflat, rfl, rfl⟩ := hl
    simp only [List.cons_append] at hnr ht hs
    exact step_copy hR.1 hxy hflat hts hb hDb hag hnr ht hs
  obtain ⟨cmt, stt⟩ := mt
  obtain ⟨cms, sts⟩ := ms
  dsimp only at hc ht hs hxy
  subst hc ht hs
  cases ss with
  | nil =>
    refine StepMatch.of_mrel ⟨rfl, D, .block hb hDb hts hag hnr⟩ (fun _ _ _ _ h => .inl h) ?_
    intro D Db pt ps t' s' ids' et' es' ft' fs' hl hts' hb' hDb' hag' hnr' ht' hs'
    obtain ⟨x, y, T, facts, loc, ss, hxy, hflat, rfl, rfl⟩ := hl
    simp only [List.cons_append, List.nil_append] at hnr' ht' hs' ⊢
    rw [ht', hs'] at *
    exact step_copy rfl hxy hflat hts' hb' hDb' hag' hnr' rfl rfl
  | cons o ss =>
    simp only [List.map_cons, List.cons_append] at hnr hxy ⊢
    exact step_mid hflat hts hb hDb hag hnr hxy

/-- **Copy propagation is correct.** Making, anywhere in a function, the ops right after
`%y = copy %x` in the same block read `%x` where they read `%y` gives a function that refines the
original, for every argument and every oracle. The ops rewritten must have no regions, call no
function, and bind neither `%x` nor `%y`; the run may end with a terminator. -/
theorem refines {mod : Module} {tgt src : Func} (hparams : tgt.params = src.params)
    (hrets : tgt.rets = src.rets) (hops : OpsRel L tgt.body.ops src.body.ops)
    (dec : src.Decided mod) : tgt.Refines mod src :=
  Simulation.refines sim
    (fun oracle args => ⟨oracle, InitMatch.of_lockstep
      (init_lockstep hparams hrets hops oracle args) fun _ _ h => .inl h⟩) dec

/-! ## Look-alikes that are wrong -/

/-- Reading `%x` for `%y` is wrong once the two hold different values, as they do after an op
rebinds `%x`. This is why the ops crossed may bind neither. -/
theorem subst_after_rebind_wrong :
    ¬ ∀ (fs : List Frame) (loc : Option Loc),
      operandIn fs loc (substOperand "x" "y" (.var "y")) = operandIn fs loc (.var "y") := by
  intro h
  have := h [.block [] [] (((∅ : Env).insert "x" (.int 8 .poison)).insert "y" (.int 8 (.bits 1)))]
    none
  simp [substOperand, operandIn, lookup, Std.HashMap.getElem_insert, pure, Except.pure] at this

end Fir.CopyProp
