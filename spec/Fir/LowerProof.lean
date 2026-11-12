import Fir.Lower
import Fir.LowerBits
import Fir.Parse
import Fir.Print
import Fir.SimStutter
import Fir.Dce

/-!
# The expansion pass is correct

`Expand.refines`: the expansion pass of the lowering (`Lower.expand`: checked arithmetic,
`ptr.field`, and `ptr.index` as core ops) gives a function that refines the original, for every
function whose names don't clash with the pass's temporaries (`%.e0`, `%.e1`, …) and whose
expanded ops take variables (not holes) as operands.

The proof uses the stuttering simulation (`SimulationS.refines`) over the lockstep relation of
`Fir.CodeRel`: the target replaces one source op by several, and each source op becomes the run
of its expansion. Where the target reaches an expansion, the source runs the op in one step: if
that fails, it fails by getting stuck or by UB (a broken fact), so the source escapes; otherwise
the target runs the expansion's ops one by one (`RunsPure`), each a computation that leaves the
core alone, while the source waits (the target stutters, its measure the ops left), and the
last one lands where the source landed. The temporaries are hidden names of the block (as dead
code elimination hides deleted results): no later code reads them.

What each expansion computes is in `Fir.LowerBits`.
-/

namespace Fir.Lower.Proof

open LowerBits

/-! ## Names -/

theorem toString_inj {a b : Nat} (h : toString a = toString b) : a = b := by
  have := congrArg String.toList h
  rw [Nat.toString_eq_ofList_toDigits, Nat.toString_eq_ofList_toDigits, String.toList_ofList,
    String.toList_ofList] at this
  have h2 := congrArg (fun l => Nat.ofDigitChars 10 l 0) this
  simpa [Nat.ofDigitChars_ten_toDigits] using h2

theorem tempName_inj {pre : String} {a b : Nat} (h : tempName pre a = tempName pre b) : a = b := by
  unfold tempName at h
  have := congrArg String.toList h
  simp only [String.toList_append, List.append_assoc] at this
  exact toString_inj (by
    have := List.append_cancel_left this
    have := List.append_cancel_left this
    exact String.toList_inj.mp this)

/-! ## Running pure ops -/

/-- Running the ops `E` from the top block, one per step, each a simple op with one result that
computes on core `c` without changing it: the block's environment goes from `env` to `env'`. -/
inductive RunsPure (c : Core) (ids : List Nat) (fs : List Frame) : List Op → Env → Env → Prop
  | nil {env} : RunsPure c ids fs [] env env
  | cons {k res args loc E env env' vs v} :
      k.callee? = none → k.stackAlloc? = none → k.isTerminator = false →
      operands (.block E ids env :: fs) loc args = .ok vs →
      simpleOp loc k [res] vs c = .ok ([v], c) →
      RunsPure c ids fs E (env.insert res.name v) env' →
      RunsPure c ids fs (.mk k [res] args [] loc :: E) env env'

theorem RunsPure.run {c : Core} {ids : List Nat} {fs : List Frame} :
    ∀ {E : List Op} {env env' : Env}, RunsPure c ids fs E env env' → ∀ t,
      runSteps E.length ⟨c, .block (E ++ t) ids env :: fs⟩ = .ok ⟨c, .block t ids env' :: fs⟩
  | _, _, _, .nil, t => rfl
  | _, _, _, .cons (k := k) (res := res) (args := args) (loc := loc) (E := E) (env := env)
      h1 h2 h3 hops hop hrest, t => by
    show runSteps (E.length + 1) _ = _
    rw [Nat.add_comm, runSteps_add, runSteps_one, List.cons_append, step_simple h1 h2 h3,
      operands_ops _ E, hops]
    simp only [Except.bind, hop]
    simp only [bindTop, Env.bindAll]
    exact RunsPure.run hrest t

/-! ## Checking results one at a time -/

/-- The fact loop of one result. -/
def pairBody (loc : Option Loc) : Result × RVal → PUnit → CM (ForInStep PUnit) := fun x _ =>
  match x with
  | (r, v) => do
    forIn r.facts PUnit.unit fun f _ => do
      let b ← factHolds loc f.fact v
      if b = true then pure (ForInStep.yield PUnit.unit)
      else do
        ub UBKind.fact loc (toString "%" ++ toString r.name ++ toString " breaks a fact")
        pure (ForInStep.yield PUnit.unit)
    pure (ForInStep.yield PUnit.unit)

theorem checkResults_eq (loc : Option Loc) (rs : List Result) (vs : List RVal) :
    checkResults loc rs vs = (do checkTypes loc rs vs; forIn (rs.zip vs) PUnit.unit (pairBody loc); pure ()) := rfl

theorem pairBody_ro (loc : Option Loc) (x : Result × RVal) : Dce.ReadOnly (pairBody loc x PUnit.unit) := by
  obtain ⟨r, v⟩ := x
  unfold pairBody
  refine Dce.ReadOnly.bind' (Dce.ReadOnly.forIn' fun _ _ => ?_) fun _ => Dce.ReadOnly.pure' _
  refine Dce.ReadOnly.bind' (Dce.readOnly_factHolds _ _ _) fun _ => ?_
  exact Dce.ReadOnly.ite' (Dce.ReadOnly.pure' _) (Dce.ReadOnly.bind' (Dce.ReadOnly.ub' _ _ _) fun _ => Dce.ReadOnly.pure' _)

theorem pairBody_yield (loc : Option Loc) (x : Result × RVal) (c : Core) {s c'}
    (h : pairBody loc x PUnit.unit c = .ok (s, c')) : s = .yield PUnit.unit ∧ c' = c := by
  rcases pairBody_ro loc x c with ⟨e, he, _⟩ | ⟨a, he⟩
  · rw [he] at h; cases h
  · rw [he] at h
    cases h
    refine ⟨?_, rfl⟩
    obtain ⟨r, v⟩ := x
    simp only [pairBody, bind, StateT.bind, Except.bind] at he
    split at he
    · cases he
    · simp only [pure, StateT.pure, Except.pure] at he
      cases he; rfl

theorem checkResults_cons {loc : Option Loc} {r : Result} {rs : List Result} {v : RVal}
    {vs : List RVal} {c c' : Core} {u : Unit}
    (h : checkResults loc (r :: rs) (v :: vs) c = .ok (u, c')) :
    checkResults loc [r] [v] c = .ok ((), c) ∧ checkResults loc rs vs c = .ok ((), c) := by
  rw [checkResults_eq] at h ⊢
  rw [checkResults_eq]
  simp only [checkTypes, List.zip_cons_cons, List.zip_nil_right, List.forIn_cons, List.forIn_nil,
    bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at h ⊢
  have hro : ∀ c, (∃ e, checkTypes loc rs vs c = .error e) ∨ checkTypes loc rs vs c = .ok ((), c) := by
    intro c
    rcases Dce.readOnly_checkTypes loc rs vs c with ⟨e, he, _⟩ | ⟨a, he⟩
    · exact .inl ⟨e, he⟩
    · exact .inr he
  have hloop : ∀ c, (∃ e, forIn (rs.zip vs) PUnit.unit (pairBody loc) c = .error e) ∨
      ∃ a, forIn (rs.zip vs) PUnit.unit (pairBody loc) c = .ok (a, c) := by
    intro c
    rcases Dce.ReadOnly.forIn' (l := rs.zip vs) (init := PUnit.unit) (f := pairBody loc)
      (fun x _ => pairBody_ro loc x) c with ⟨e, he, _⟩ | ⟨a, he⟩
    · exact .inl ⟨e, he⟩
    · exact .inr ⟨a, he⟩
  by_cases hty : v.hasTy r.ty = true
  · simp only [hty, ite_true] at h ⊢
    rcases hro c with ⟨e, he⟩ | he
    · rw [he] at h; cases h
    rw [he] at h
    dsimp only at h
    cases hp : pairBody loc (r, v) PUnit.unit c with
    | error e => rw [hp] at h; cases h
    | ok q =>
      rw [hp] at h
      obtain ⟨hs, hc⟩ := pairBody_yield loc (r, v) c hp
      obtain ⟨s, c2⟩ := q
      dsimp only at hs hc h
      subst hs
      subst c2
      dsimp only at h
      refine ⟨by simp [StateT.pure, pure, Except.pure, hp], ?_⟩
      rw [he]
      dsimp only
      rcases hloop c with ⟨e, he'⟩ | ⟨a, he'⟩
      · rw [he'] at h; cases h
      · rw [he']
  · simp only [hty, Bool.false_eq_true, ite_false, halt, throw, throwThe, MonadExceptOf.throw,
      StateT.bind] at h
    cases h

/-- Every state along a pure run keeps the core, and the current block's place. -/
theorem RunsPure.mid {c : Core} {ids : List Nat} {fs : List Frame} :
    ∀ {E : List Op} {env env' : Env}, RunsPure c ids fs E env env' → ∀ t i, i ≤ E.length →
      ∃ envi, runSteps i ⟨c, .block (E ++ t) ids env :: fs⟩ = .ok ⟨c, .block (E.drop i ++ t) ids envi :: fs⟩
  | _, _, _, .nil, t, i, hi => by
    obtain rfl : i = 0 := by simpa using hi
    exact ⟨_, rfl⟩
  | _, _, _, .cons (k := k) (res := res) (args := args) (loc := loc) (E := E) (env := env)
      h1 h2 h3 hops hop hrest, t, i, hi => by
    cases i with
    | zero => exact ⟨env, rfl⟩
    | succ i =>
      obtain ⟨envi, ei⟩ := RunsPure.mid hrest t i (by simpa using hi)
      refine ⟨envi, ?_⟩
      have hs : ∀ x : Machine, runSteps (i + 1) x = (runSteps 1 x).bind (runSteps i) := fun x => by
        rw [Nat.add_comm]; exact runSteps_add 1 i x
      rw [hs, runSteps_one, List.cons_append, step_simple h1 h2 h3, operands_ops _ E, hops]
      simp only [Except.bind, hop, bindTop, Env.bindAll, List.drop_succ_cons]
      exact ei

/-! ## Ops on known values -/

section
variable (loc : Option Loc) (c : Core)

theorem checkResults_plain (n : String) (T : Ty) (v : RVal) (h : v.hasTy T = true) :
    checkResults loc [{ name := n, ty := T }] [v] c = .ok ((), c) := by
  simp only [checkResults, checkTypes, h]
  rfl

theorem simpleOp_of {k : OpKind} {rs : List Result} {vs outs : List RVal}
    (he : evalSimple loc k rs vs c = .ok (outs, c)) (hc : checkResults loc rs outs c = .ok ((), c)) :
    simpleOp loc k rs vs c = .ok (outs, c) := by
  rw [Fwd.simpleOp_eq, he]
  simp only [Except.bind, hc]

theorem asInt_ok {w : Nat} {v : RVal} {x : Val w} {c c' : Core} (h : asInt loc w v c = .ok (x, c')) :
    v = .int w x ∧ c' = c := by
  unfold asInt at h
  split at h
  · rename_i w' v'
    split at h
    · rename_i hw
      subst hw
      cases h
      exact ⟨rfl, rfl⟩
    · cases h
  · cases h

/-- The checked-arithmetic results on `w`-bit operands. -/
def ovfOuts (op : ArithOp) (signed : Bool) : Val w → Val w → List RVal
  | .bits x, .bits y =>
    [.int w (.bits (Sem.wrapOp op x y)), .int 1 (.bits (BitVec.ofBool (Sem.overflow signed op x y)))]
  | _, _ => [.int w .poison, .int 1 .poison]

/-- What a successful checked-arithmetic op saw and computed. -/
theorem overflow_src {op : ArithOp} {signed : Bool} {r ov : Result} {va vb : RVal}
    {outs : List RVal} {c' : Core}
    (h : simpleOp loc (.overflow op signed) [r, ov] [va, vb] c = .ok (outs, c')) :
    c' = c ∧ ∃ xa xb, va = .int r.ty.width xa ∧ vb = .int r.ty.width xb ∧
      outs = ovfOuts op signed xa xb ∧ checkResults loc [r, ov] outs c = .ok ((), c) := by
  rw [Fwd.simpleOp_eq] at h
  cases he : evalSimple loc (.overflow op signed) [r, ov] [va, vb] c with
  | error e => rw [he] at h; cases h
  | ok p =>
    rw [he] at h
    simp only [Except.bind] at h
    have hk := Dce.readOnly_checkResults loc [r, ov] p.1 p.2
    simp only [evalSimple, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      Except.bind, pure, Except.pure] at he
    cases ha : asInt loc r.ty.width va c with
    | error e => rw [ha] at he; cases he
    | ok qa =>
      rw [ha] at he
      dsimp only at he
      obtain ⟨hva, hca⟩ := asInt_ok loc ha
      cases hb : asInt loc r.ty.width vb qa.2 with
      | error e => rw [hb] at he; cases he
      | ok qb =>
        rw [hb] at he
        dsimp only at he
        obtain ⟨hvb, hcb⟩ := asInt_ok loc hb
        obtain ⟨xa, ca⟩ := qa
        obtain ⟨xb, cb⟩ := qb
        dsimp only at hva hca hvb hcb he
        rw [hcb, hca] at he
        have hp : p = (ovfOuts op signed xa xb, c) := by
          cases xa <;> cases xb <;> (simp only [pure, StateT.pure, Except.pure] at he; cases he; rfl)
        subst hp
        dsimp only at hk h
        rcases hk with ⟨e, he', _⟩ | ⟨u, he'⟩
        · rw [he'] at h; cases h
        · rw [he'] at h
          cases h
          exact ⟨rfl, xa, xb, hva, hvb, rfl, he'⟩

end

/-! ## Lookups -/

theorem lookup_insert {n m : String} {v : RVal} {E : List Op} {ids : List Nat} {env : Env}
    {fs : List Frame} :
    lookup n (.block E ids (env.insert m v) :: fs) =
      if m = n then some v else lookup n (.block E ids env :: fs) := by
  simp only [lookup, Std.HashMap.getElem?_insert, beq_iff_eq]
  by_cases h : m = n
  · simp [h]
  · simp only [h, ite_false]

theorem operandIn_insert {n m : String} {v : RVal} {E : List Op} {ids : List Nat} {env : Env}
    {fs : List Frame} {loc : Option Loc} :
    operandIn (.block E ids (env.insert m v) :: fs) loc (.var n) =
      if m = n then .ok v else operandIn (.block E ids env :: fs) loc (.var n) := by
  simp only [operandIn, lookup_insert]
  by_cases h : m = n
  · simp [h]; rfl
  · simp only [h, ite_false]

theorem operandIn_insert_self {n : String} {v : RVal} {E : List Op} {ids : List Nat} {env : Env}
    {fs : List Frame} {loc : Option Loc} :
    operandIn (.block E ids (env.insert n v) :: fs) loc (.var n) = .ok v := by
  rw [operandIn_insert, ite_eq_left_iff.mpr (fun h => absurd rfl h)]

theorem operandIn_insert_ne {n m : String} {v : RVal} {E : List Op} {ids : List Nat} {env : Env}
    {fs : List Frame} {loc : Option Loc} (h : m ≠ n) :
    operandIn (.block E ids (env.insert m v) :: fs) loc (.var n) =
      operandIn (.block E ids env :: fs) loc (.var n) := by
  rw [operandIn_insert, ite_eq_right_iff.mpr (fun h' => absurd h' h)]

theorem operandIn_code {n : String} {E E' : List Op} {ids : List Nat} {env : Env}
    {fs : List Frame} {loc : Option Loc} :
    operandIn (.block E ids env :: fs) loc (.var n) = operandIn (.block E' ids env :: fs) loc (.var n) :=
  rfl

/-! ## The simple ops expansions use -/

def extVal (signed : Bool) (W : Nat) (x : Val w) : Val W :=
  if signed then Sem.sext W x else Sem.zext W x

section
variable (loc : Option Loc) (c : Core)

theorem hasTy_int (w : Nat) (x : Val w) : (RVal.int w x).hasTy (.int w) = true := by
  simp [RVal.hasTy]

theorem asInt_int (w : Nat) (x : Val w) : asInt loc w (.int w x) c = .ok (x, c) := by
  simp [asInt]; rfl

theorem asInt_int' (w : Nat) (x : Val w) : asInt loc w (.int w x) = (pure x : CM (Val w)) := by
  funext c; exact asInt_int loc c w x

theorem op_ext (signed : Bool) (n : String) (W : Nat) (x : Val w) :
    simpleOp loc (extOp signed) [res n (.int W)] [.int w x] c =
      .ok ([.int W (extVal signed W x)], c) := by
  cases signed
  · exact simpleOp_of loc c rfl (checkResults_plain loc c _ _ _ (hasTy_int _ _))
  · exact simpleOp_of loc c rfl (checkResults_plain loc c _ _ _ (hasTy_int _ _))

/-- `int.add.wrap` and friends never fail. -/
def wrapVal (op : ArithOp) : Val W → Val W → Val W
  | .bits x, .bits y => .bits (Sem.wrapOp op x y)
  | _, _ => .poison

theorem op_wrap (op : ArithOp) (n : String) (x y : Val W) :
    simpleOp loc (.arith op .wrap) [res n (.int W)] [.int W x, .int W y] c =
      .ok ([.int W (wrapVal op x y)], c) := by
  refine simpleOp_of loc c ?_ (checkResults_plain loc c _ _ _ (hasTy_int _ _))
  simp only [evalSimple, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, pure, Except.pure, StateT.pure, res, Ty.width, asInt_int]
  cases x <;> cases y <;> rfl

theorem op_trunc (mode : TruncMode) (r : Result) (x : Val W)
    (hc : checkResults loc [r] [.int r.ty.width (Sem.trunc mode r.ty.width x)] c = .ok ((), c)) :
    simpleOp loc (.trunc mode) [r] [.int W x] c =
      .ok ([.int r.ty.width (Sem.trunc mode r.ty.width x)], c) :=
  simpleOp_of loc c rfl hc

theorem op_cmp (p : Pred) (r : Result) (x y : Val W)
    (hc : checkResults loc [r] [.int 1 (Sem.cmp p x y)] c = .ok ((), c)) :
    simpleOp loc (.cmp p) [r] [.int W x, .int W y] c = .ok ([.int 1 (Sem.cmp p x y)], c) := by
  refine simpleOp_of loc c ?_ hc
  simp only [evalSimple, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, pure, Except.pure, StateT.pure, asInt_int]

theorem op_const (n : String) (W : Nat) (k : Int) :
    simpleOp loc (.const k) [res n (.int W)] [] c = .ok ([.int W (Sem.const W k)], c) :=
  simpleOp_of loc c rfl (checkResults_plain loc c _ _ _ (hasTy_int _ _))

end

/-! ## Checked arithmetic -/

/-- The checked-arithmetic expansion, as `expandFlat` writes it. -/
def ovfOps (op : ArithOp) (signed : Bool) (r ov : Result) (a b : String) (loc : Option Loc)
    (t0 t1 t2 t3 : String) : List Op :=
  let W := LowerBits.wide op r.ty.width
  [.mk (extOp signed) [res t0 (.int W)] [.var a] [] loc,
    .mk (extOp signed) [res t1 (.int W)] [.var b] [] loc,
    .mk (.arith op .wrap) [res t2 (.int W)] [.var t0, .var t1] [] loc,
    .mk (.trunc .wrap) [r] [.var t2] [] loc,
    .mk (extOp signed) [res t3 (.int W)] [.var r.name] [] loc,
    .mk (.cmp .ne) [ov] [.var t2, .var t3] [] loc]

theorem extVal_bits (signed : Bool) (W : Nat) (x : BitVec w) :
    extVal signed W (.bits x) = .bits (LowerBits.ext signed W x) := by
  cases signed <;> rfl

theorem ovfOuts_eq (op : ArithOp) (signed : Bool) (xa xb : Val w) :
    let W := LowerBits.wide op w
    let t2 := wrapVal op (extVal signed W xa) (extVal signed W xb)
    let vr := Sem.trunc .wrap w t2
    ovfOuts op signed xa xb = [.int w vr, .int 1 (Sem.cmp .ne t2 (extVal signed W vr))] := by
  intro W t2 vr
  cases xa with
  | poison => cases xb <;> cases signed <;> rfl
  | bits x =>
    cases xb with
    | poison => cases signed <;> rfl
    | bits y =>
      simp only [t2, vr, W, extVal_bits, wrapVal, Sem.trunc, Sem.cmp, Sem.cmpBits, ovfOuts]
      rw [wrap_ext op signed x y (le_wide op w)]
      have hf := flag_ext op signed x y (fits_wide op w)
      rw [wrap_ext op signed x y (le_wide op w)] at hf
      rw [hf]

/-- **The checked-arithmetic expansion runs** where the source op succeeds, binding its results to
what the source binds them to, and its temporaries. -/
theorem ovf_runs {c : Core} {ids : List Nat} {fs : List Frame} {env : Env} {loc : Option Loc}
    {op : ArithOp} {signed : Bool} {r ov : Result} {a b t0 t1 t2 t3 : String}
    {xa xb : Val r.ty.width}
    (ha : operandIn (.block [] ids env :: fs) loc (.var a) = .ok (.int r.ty.width xa))
    (hb : operandIn (.block [] ids env :: fs) loc (.var b) = .ok (.int r.ty.width xb))
    (h0b : t0 ≠ b) (h01 : t0 ≠ t1) (hr2 : r.name ≠ t2) (h32 : t3 ≠ t2)
    (hcr : checkResults loc [r] [(ovfOuts op signed xa xb).headD (.ptr none)] c = .ok ((), c))
    (hco : checkResults loc [ov] [(ovfOuts op signed xa xb).getD 1 (.ptr none)] c = .ok ((), c)) :
    ∃ v0 v1 v2 v3, RunsPure c ids fs (ovfOps op signed r ov a b loc t0 t1 t2 t3) env
      ((((((env.insert t0 v0).insert t1 v1).insert t2 v2).insert r.name
        ((ovfOuts op signed xa xb).headD (.ptr none))).insert t3 v3).insert ov.name
        ((ovfOuts op signed xa xb).getD 1 (.ptr none))) := by
  have heq := ovfOuts_eq op signed xa xb
  simp only at heq
  rw [heq] at hcr hco ⊢
  simp only [List.headD, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some] at hcr hco ⊢
  refine ⟨.int (LowerBits.wide op r.ty.width) (extVal signed _ xa),
    .int (LowerBits.wide op r.ty.width) (extVal signed _ xb),
    .int (LowerBits.wide op r.ty.width) (wrapVal op (extVal signed _ xa) (extVal signed _ xb)),
    .int (LowerBits.wide op r.ty.width) (extVal signed (LowerBits.wide op r.ty.width)
    (Sem.trunc .wrap r.ty.width (wrapVal op (extVal signed (LowerBits.wide op r.ty.width) xa)
      (extVal signed (LowerBits.wide op r.ty.width) xb)))), ?_⟩
  unfold ovfOps
  refine .cons (by cases signed <;> rfl) (by cases signed <;> rfl) (by cases signed <;> rfl) ?_ (op_ext loc c signed t0 _ xa) ?_
  · rw [operands_one, operandIn_code (E' := []), ha]; rfl
  refine .cons (by cases signed <;> rfl) (by cases signed <;> rfl) (by cases signed <;> rfl) ?_ (op_ext loc c signed t1 _ xb) ?_
  · dsimp only [res]
    rw [operands_one, operandIn_insert_ne h0b, operandIn_code (E' := []), hb]; rfl
  refine .cons rfl rfl rfl ?_ (op_wrap loc c op t2 (extVal signed (LowerBits.wide op r.ty.width) xa)
    (extVal signed (LowerBits.wide op r.ty.width) xb)) ?_
  · dsimp only [res]
    rw [operands_pair, operandIn_insert_ne h01.symm, operandIn_insert_self,
      operandIn_insert_self]; rfl
  refine .cons rfl rfl rfl ?_ (op_trunc loc c .wrap r (wrapVal op
    (extVal signed (LowerBits.wide op r.ty.width) xa) (extVal signed (LowerBits.wide op r.ty.width) xb))
    hcr) ?_
  · dsimp only [res]
    rw [operands_one, operandIn_insert_self]; rfl
  refine .cons (by cases signed <;> rfl) (by cases signed <;> rfl) (by cases signed <;> rfl) ?_
    (op_ext loc c signed t3 (LowerBits.wide op r.ty.width) (Sem.trunc .wrap r.ty.width (wrapVal op
      (extVal signed (LowerBits.wide op r.ty.width) xa)
      (extVal signed (LowerBits.wide op r.ty.width) xb)))) ?_
  · rw [operands_one, operandIn_insert_self]; rfl
  refine .cons rfl rfl rfl ?_ (op_cmp loc c .ne ov (wrapVal op
      (extVal signed (LowerBits.wide op r.ty.width) xa) (extVal signed (LowerBits.wide op r.ty.width) xb))
    (extVal signed (LowerBits.wide op r.ty.width) (Sem.trunc .wrap r.ty.width (wrapVal op
      (extVal signed (LowerBits.wide op r.ty.width) xa)
      (extVal signed (LowerBits.wide op r.ty.width) xb)))) ?_) .nil
  · dsimp only [res]
    rw [operands_pair, operandIn_insert_ne h32, operandIn_insert_ne hr2, operandIn_insert_self,
      operandIn_insert_self]
    simp only [extVal]
    cases signed <;> rfl
  · simpa [extVal] using hco

theorem ovfOuts_pair (op : ArithOp) (signed : Bool) (xa xb : Val w) :
    ovfOuts op signed xa xb =
      [(ovfOuts op signed xa xb).headD (.ptr none), (ovfOuts op signed xa xb).getD 1 (.ptr none)] := by
  cases xa <;> cases xb <;> rfl

theorem readOnly_asInt (loc : Option Loc) (w : Nat) (v : RVal) : Dce.ReadOnly (asInt loc w v) := by
  unfold asInt
  split
  · split
    · exact Dce.ReadOnly.pure' _
    · exact Dce.ReadOnly.stuck _ _ _
  · exact Dce.ReadOnly.stuck _ _ _

theorem readOnly_ovf (loc : Option Loc) (op : ArithOp) (signed : Bool) (r ov : Result)
    (vs : List RVal) : Dce.ReadOnly (evalSimple loc (.overflow op signed) [r, ov] vs) := by
  match vs with
  | [va, vb] =>
    intro c
    simp only [evalSimple, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      Except.bind, pure, Except.pure]
    rcases readOnly_asInt loc r.ty.width va c with ⟨h, e, hh⟩ | ⟨x, e⟩
    · exact .inl ⟨h, by rw [e], hh⟩
    rw [e]
    rcases readOnly_asInt loc r.ty.width vb c with ⟨h, e', hh⟩ | ⟨y, e'⟩
    · exact .inl ⟨h, by simp only [e'], hh⟩
    simp only [e']
    cases x <;> cases y <;> exact .inr ⟨_, rfl⟩
  | [] | [_] | _ :: _ :: _ :: _ => exact fun c => .inl ⟨_, rfl, trivial⟩

/-! ## Addresses -/

section
variable (loc : Option Loc) (c : Core)

/-- `ptr.offset` by the constant field offset is `ptr.field`. -/
theorem field_eq (inb : Bool) (T : Ty) (i : Nat) (r : Result) (pv : RVal)
    (hoff : ((T.fieldOffset? c.space i).getD 0 : Int) < 2 ^ (c.space.addrBits - 1)) :
    evalSimple loc (.ptrOffset inb) [r]
        [pv, .int c.space.addrBits (Sem.const c.space.addrBits ((T.fieldOffset? c.space i).getD 0))] c =
      evalSimple loc (.ptrField inb T i) [r] [pv] c := by
  simp only [evalSimple, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, pure, Except.pure, Sem.const]
  cases pv with
  | ptr q =>
    cases q with
    | none => rfl
    | some q =>
      simp only [asPtr, pure, StateT.pure, Except.pure, StateT.bind, asInt_int]
      have hto : (BitVec.ofInt c.space.addrBits ((T.fieldOffset? c.space i).getD 0 : Int)).toInt =
          ((T.fieldOffset? c.space i).getD 0 : Int) := by
        rcases Nat.eq_zero_or_pos c.space.addrBits with h0 | hpos
        · have h1 : ((T.fieldOffset? c.space i).getD 0 : Int) < 1 := by
            have := hoff; rw [h0] at this; simpa using this
          have : (T.fieldOffset? c.space i).getD 0 = 0 := by omega
          rw [this]; simp
        · have : (0 : Int) ≤ 2 ^ (c.space.addrBits - 1) := Int.pow_nonneg (by decide)
          exact toInt_ofInt_small hpos (by omega) hoff
      simp only [bind, Except.bind, StateT.bind, hto]
      rfl
  | _ => rfl

/-- `ptr.offset.wrap` by the wrapped product is `ptr.index.wrap`. -/
theorem indexW_eq (T : Ty) (r : Result) (pv : RVal) (x : Val c.space.addrBits) :
    evalSimple loc (.ptrOffset false) [r] [pv, .int c.space.addrBits
        (wrapVal .mul x (Sem.const c.space.addrBits (T.stride c.space)))] c =
      evalSimple loc (.ptrIndex false T) [r] [pv, .int c.space.addrBits x] c := by
  simp only [evalSimple, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, pure, Except.pure, asInt_int, Sem.const]
  cases pv with
  | ptr q =>
    cases q with
    | none => cases x <;> rfl
    | some q =>
      cases x with
      | poison => simp only [wrapVal, asInt_int']; rfl
      | bits a =>
        simp only [asPtr, pure, StateT.pure, Except.pure, StateT.bind, Except.bind, asInt_int',
          wrapVal, Sem.wrapOp, Bool.false_and, Bool.false_eq_true, ite_false, bind]
        rw [index_wrap]
  | _ => cases x <;> rfl

/-- `ptr.offset.inbounds` by the product at twice the width, truncated with `.nsw`, is
`ptr.index.inbounds`, for strides that fit the address size. -/
theorem indexI_eq (T : Ty) (r : Result) (pv : RVal) (x : Val c.space.addrBits)
    (hst : T.stride c.space < 2 ^ c.space.addrBits) :
    evalSimple loc (.ptrOffset true) [r] [pv, .int c.space.addrBits
        (Sem.trunc .nsw c.space.addrBits (wrapVal .mul (extVal true (2 * c.space.addrBits) x)
          (Sem.const (2 * c.space.addrBits) (T.stride c.space))))] c =
      evalSimple loc (.ptrIndex true T) [r] [pv, .int c.space.addrBits x] c := by
  simp only [evalSimple, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, pure, Except.pure, asInt_int, Sem.const]
  cases pv with
  | ptr q =>
    cases q with
    | none => cases x <;> rfl
    | some q =>
      cases x with
      | poison => simp only [wrapVal, extVal, Sem.sext, Sem.trunc, asInt_int', ite_true]; rfl
      | bits a =>
        obtain ⟨hiff, hval⟩ := index_inbounds a hst
        simp only [asPtr, pure, StateT.pure, Except.pure, StateT.bind, Except.bind, asInt_int',
          wrapVal, Sem.wrapOp, extVal, ite_true, Sem.sext, Sem.trunc, Bool.true_and, bind]
        by_cases hfit : (BitVec.ofInt c.space.addrBits (a.toInt * (T.stride c.space : Nat))).toInt =
            a.toInt * (T.stride c.space : Nat)
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (hiff.mpr hfit))]
          simp only [hval, hfit, bne_self_eq_false, Bool.false_eq_true, ite_false]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hfit (hiff.mp h)))]
          simp only [bne_iff_ne, ne_eq, hfit, not_false_eq_true, ite_true]
  | _ => cases x <;> rfl

end

theorem readOnly_offsetBy (loc : Option Loc) (inb : Bool) (p : Ptr) (n : Int) :
    Dce.ReadOnly (offsetBy loc inb p n) := by
  unfold offsetBy
  refine Dce.ReadOnly.bind' Dce.ReadOnly.get' fun c => ?_
  refine Dce.ReadOnly.ite' (Dce.ReadOnly.pure' _) ?_
  split
  · exact Dce.ReadOnly.bind' (Dce.readOnly_getAlloc _ _) fun _ => Dce.ReadOnly.pure' _
  · exact Dce.ReadOnly.ite' (Dce.ReadOnly.pure' _) (Dce.ReadOnly.pure' _)

theorem readOnly_asPtr (loc : Option Loc) (v : RVal) : Dce.ReadOnly (asPtr loc v) := by
  unfold asPtr
  split
  · exact Dce.ReadOnly.pure' _
  · exact Dce.ReadOnly.stuck _ _ _

theorem readOnly_field (loc : Option Loc) (inb : Bool) (T : Ty) (i : Nat) (r : Result)
    (vs : List RVal) : Dce.ReadOnly (evalSimple loc (.ptrField inb T i) [r] vs) := by
  match vs with
  | [pv] =>
    intro c
    simp only [evalSimple, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      Except.bind, pure, Except.pure]
    rcases readOnly_asPtr loc pv c with ⟨h, e, hh⟩ | ⟨q, e⟩
    · exact .inl ⟨h, by rw [e], hh⟩
    rw [e]
    dsimp only
    cases q with
    | none => exact .inr ⟨_, rfl⟩
    | some q =>
      rcases readOnly_offsetBy loc inb q ((T.fieldOffset? c.space i).getD 0) c with
        ⟨h, e', hh⟩ | ⟨x, e'⟩
      · exact .inl ⟨h, by simp only [StateT.bind, e', bind, Except.bind], hh⟩
      · exact .inr ⟨_, by simp only [StateT.bind, e', bind, Except.bind]; rfl⟩
  | [] | _ :: _ :: _ => exact fun c => .inl ⟨_, rfl, trivial⟩

theorem readOnly_index (loc : Option Loc) (inb : Bool) (T : Ty) (r : Result) (vs : List RVal) :
    Dce.ReadOnly (evalSimple loc (.ptrIndex inb T) [r] vs) := by
  match vs with
  | [pv, iv] =>
    intro c
    simp only [evalSimple, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      Except.bind, pure, Except.pure]
    rcases readOnly_asInt loc c.space.addrBits iv c with ⟨h, e, hh⟩ | ⟨x, e⟩
    · exact .inl ⟨h, by rw [e], hh⟩
    rw [e]
    dsimp only
    rcases readOnly_asPtr loc pv c with ⟨h, e', hh⟩ | ⟨q, e'⟩
    · exact .inl ⟨h, by simp only [e'], hh⟩
    simp only [e']
    cases q with
    | none => exact .inr ⟨_, rfl⟩
    | some q =>
      cases x with
      | poison => exact .inr ⟨_, rfl⟩
      | bits a =>
        dsimp only
        split
        · exact .inr ⟨_, rfl⟩
        · rcases readOnly_offsetBy loc inb q
              (BitVec.ofInt c.space.addrBits (a.toInt * ↑(T.stride c.space))).toInt c with
            ⟨h, e'', hh⟩ | ⟨y, e''⟩
          · exact .inl ⟨h, by simp only [StateT.bind, e'', bind, Except.bind], hh⟩
          · exact .inr ⟨_, by simp only [StateT.bind, e'', bind, Except.bind]; rfl⟩
  | [] | [_] | _ :: _ :: _ :: _ => exact fun c => .inl ⟨_, rfl, trivial⟩

/-- A successful `ptr.index` saw an address-sized index. -/
theorem index_src {loc : Option Loc} {inb : Bool} {T : Ty} {r : Result} {pv iv : RVal}
    {c : Core} {outs : List RVal} {c' : Core}
    (h : simpleOp loc (.ptrIndex inb T) [r] [pv, iv] c = .ok (outs, c')) :
    ∃ x, iv = .int c.space.addrBits x := by
  rw [Fwd.simpleOp_eq] at h
  cases he : evalSimple loc (.ptrIndex inb T) [r] [pv, iv] c with
  | error e => rw [he] at h; cases h
  | ok p =>
    simp only [evalSimple, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      Except.bind, pure, Except.pure] at he
    cases ha : asInt loc c.space.addrBits iv c with
    | error e => rw [ha] at he; cases he
    | ok q => exact ⟨q.1, (asInt_ok loc ha).1⟩

theorem simpleOp_congr {loc : Option Loc} {k k' : OpKind} {rs : List Result} {vs vs' : List RVal}
    {c : Core} (h : evalSimple loc k rs vs c = evalSimple loc k' rs vs' c) :
    simpleOp loc k rs vs c = simpleOp loc k' rs vs' c := by
  rw [Fwd.simpleOp_eq, Fwd.simpleOp_eq, h]

/-! ## The rewrite -/

/-- The expansion `E` of `o`, with temporaries `ts`, as `expandFlat` writes it: temporaries that
are distinct, and differ from every name `o` reads or binds. -/
inductive Exp (sp : SpaceCfg) : Op → List Op → List String → Prop
  | ovf {op signed r ov a b loc t0 t1 t2 t3} :
      [t0, t1, t2, t3].Nodup →
      (∀ x ∈ [t0, t1, t2, t3], x ≠ a ∧ x ≠ b ∧ x ≠ r.name ∧ x ≠ ov.name) →
      Exp sp (.mk (.overflow op signed) [r, ov] [.var a, .var b] [] loc)
        (ovfOps op signed r ov a b loc t0 t1 t2 t3) [t0, t1, t2, t3]
  | field {inb T i r p loc t0} :
      ((T.fieldOffset? sp i).getD 0 : Int) < 2 ^ (sp.addrBits - 1) → t0 ≠ p → t0 ≠ r.name →
      Exp sp (.mk (.ptrField inb T i) [r] [.var p] [] loc)
        [.mk (.const ((T.fieldOffset? sp i).getD 0)) [res t0 (.int sp.addrBits)] [] [] loc,
          .mk (.ptrOffset inb) [r] [.var p, .var t0] [] loc] [t0]
  | indexW {T r p i loc t0 t1} :
      t0 ≠ t1 → (∀ x ∈ [t0, t1], x ≠ p ∧ x ≠ i ∧ x ≠ r.name) →
      Exp sp (.mk (.ptrIndex false T) [r] [.var p, .var i] [] loc)
        [.mk (.const (T.stride sp)) [res t0 (.int sp.addrBits)] [] [] loc,
          .mk (.arith .mul .wrap) [res t1 (.int sp.addrBits)] [.var i, .var t0] [] loc,
          .mk (.ptrOffset false) [r] [.var p, .var t1] [] loc] [t0, t1]
  | indexI {T r p i loc t0 t1 t2 t3} :
      T.stride sp < 2 ^ sp.addrBits → [t0, t1, t2, t3].Nodup →
      (∀ x ∈ [t0, t1, t2, t3], x ≠ p ∧ x ≠ i ∧ x ≠ r.name) →
      Exp sp (.mk (.ptrIndex true T) [r] [.var p, .var i] [] loc)
        [.mk .sext [res t0 (.int (2 * sp.addrBits))] [.var i] [] loc,
          .mk (.const (T.stride sp)) [res t1 (.int (2 * sp.addrBits))] [] [] loc,
          .mk (.arith .mul .wrap) [res t2 (.int (2 * sp.addrBits))] [.var t0, .var t1] [] loc,
          .mk (.trunc .nsw) [res t3 (.int sp.addrBits)] [.var t2] [] loc,
          .mk (.ptrOffset true) [r] [.var p, .var t3] [] loc] [t0, t1, t2, t3]

/-- The rewrite: the target has the expansion of a source op, and the rest of the target's
region reads none of its temporaries. -/
def L (sp : SpaceCfg) (pt ps t : List Op) : Prop :=
  ∃ o ts, ps = [o] ∧ Exp sp o pt ts ∧ ∀ n ∈ ts, opsReads n t = false

/-- An expansion reads what its source op reads. -/
theorem Exp.reads {sp : SpaceCfg} {o : Op} {E : List Op} {ts : List String} (h : Exp sp o E ts)
    {n : String} (hn : o.reads n = true) : opsReads n E = true := by
  cases h <;>
  · simp only [ovfOps, opsReads, Op.reads, regionsReads, List.any_cons, List.any_nil,
      Operand.reads, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hn ⊢
    grind

/-- An expansion has at least two ops. -/
theorem Exp.length_pos {sp : SpaceCfg} {o : Op} {E : List Op} {ts : List String}
    (h : Exp sp o E ts) : 2 ≤ E.length := by
  cases h <;> simp [ovfOps]

/-- The source op of an expansion is a simple op on variables. -/
theorem Exp.simple {sp : SpaceCfg} {o : Op} {E : List Op} {ts : List String} (h : Exp sp o E ts) :
    ∃ k res args loc, o = .mk k res args [] loc ∧ k.callee? = none ∧ k.stackAlloc? = none ∧
      k.isTerminator = false ∧ (∀ a ∈ args, ∃ n, a = .var n) ∧
      ∀ vs, Dce.ReadOnly (evalSimple loc k res vs) := by
  cases h with
  | ovf => exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, by simp, readOnly_ovf _ _ _ _ _⟩
  | field => exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, by simp, readOnly_field _ _ _ _ _⟩
  | indexW => exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, by simp, readOnly_index _ _ _ _⟩
  | indexI => exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, by simp, readOnly_index _ _ _ _⟩

/-- Binding results with values agreeing outside hidden names, plus temporaries in the target. -/
theorem envAgree_bind {D : String → Prop} {et es : Env} (hag : EnvAgree D et es)
    (ts : List String) {etF : Env} (hF : ∀ n, n ∉ ts → etF[n]? = et[n]?) :
    EnvAgree (fun n => D n ∨ n ∈ ts) etF es := by
  intro n hn
  simp only [not_or] at hn
  rw [hF n hn.2, hag n hn.1]

/-- An expansion that runs to the end: where the source's step lands, and every state on the way
keeps the source's core and its shape. -/
def Runs (sp : SpaceCfg) (n : Nat) (mt ms : Machine) : Prop :=
  ∃ ms' mt', step ms = .ok ms' ∧ runSteps n mt = .ok mt' ∧ MRel (L sp) mt' ms' ∧
    ∀ i mi, i < n → runSteps i mt = .ok mi → mi.core = ms.core ∧ mi.shape = ms.shape

/-- At a checked-arithmetic expansion: the source runs the op in one step and fails by getting
stuck or by UB, or the target runs the whole expansion to a state related to where the source
went. -/
theorem site_ovf {sp : SpaceCfg} {c : Core} {D Db : String → Prop} {op : ArithOp}
    {signed : Bool} {r ov : Result} {a b : String} {loc : Option Loc} {t0 t1 t2 t3 : String}
    {t s : List Op} {ids : List Nat} {et es : Env} {ft fs : List Frame}
    (hnd : [t0, t1, t2, t3].Nodup)
    (hne : ∀ x ∈ [t0, t1, t2, t3], x ≠ a ∧ x ≠ b ∧ x ≠ r.name ∧ x ≠ ov.name)
    (hfresh : ∀ n ∈ [t0, t1, t2, t3], opsReads n t = false)
    (hts : OpsRel (L sp) t s) (hb : StackRel (L sp) Db ft fs) (hDb : ∀ n, Db n → D n)
    (hag : EnvAgree D et es) (hnr : NoReads D (ovfOps op signed r ov a b loc t0 t1 t2 t3 ++ t)) :
    (∃ h, step ⟨c, .block (.mk (.overflow op signed) [r, ov] [.var a, .var b] [] loc :: s) ids es
        :: fs⟩ = .error h ∧ h.outcome.Absorbing) ∨
    Runs sp (ovfOps op signed r ov a b loc t0 t1 t2 t3).length
      ⟨c, .block (ovfOps op signed r ov a b loc t0 t1 t2 t3 ++ t) ids et :: ft⟩
      ⟨c, .block (.mk (.overflow op signed) [r, ov] [.var a, .var b] [] loc :: s) ids es :: fs⟩ := by
  have hnrE := hnr.append_left
  have hnrt := hnr.append_right
  have hst : StackRel (L sp) D (.block t ids et :: ft) (.block s ids es :: fs) :=
    .block hb hDb hts hag hnrt
  -- The operands aren't hidden: the expansion reads them.
  have hvis : ∀ x, (Op.mk (.overflow op signed) [r, ov] [.var a, .var b] [] loc).reads x = true →
      ¬ D x := fun x hx hd => by
    have := Exp.reads (Exp.ovf (sp := sp) (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) hnd hne) hx
    rw [hnrE x hd] at this; cases this
  have ha : ¬ D a := hvis a (by simp [Op.reads, Operand.reads])
  have hbv : ¬ D b := hvis b (by simp [Op.reads, Operand.reads])
  simp only [Runs]
  rw [step_simple rfl rfl rfl, operands_pair]
  cases hva : operandIn (.block s ids es :: fs) loc (.var a) with
  | error h => exact .inl ⟨h, rfl, operandIn_var_error hva⟩
  | ok va =>
  cases hvb : operandIn (.block s ids es :: fs) loc (.var b) with
  | error h => exact .inl ⟨h, rfl, operandIn_var_error hvb⟩
  | ok vb =>
  simp only [Except.bind]
  cases hop : simpleOp loc (.overflow op signed) [r, ov] [va, vb] c with
  | error h =>
    refine .inl ⟨h, rfl, ?_⟩
    rcases Dce.readOnly_simpleOp (readOnly_ovf loc op signed r ov [va, vb]) c with
      ⟨h', e, hh⟩ | ⟨_, e⟩
    · rw [hop] at e; cases e; exact hh
    · rw [hop] at e; cases e
  | ok p =>
  obtain ⟨outs, c'⟩ := p
  obtain ⟨rfl, xa, xb, rfl, rfl, rfl, hcr⟩ := overflow_src loc c hop
  right
  obtain ⟨hcr1, hcr2⟩ := checkResults_cons (by rw [ovfOuts_pair] at hcr; exact hcr)
  have hcr2' := (checkResults_cons hcr2).1
  have hunread : ∀ x, ¬ D x → ∀ n, D n → (Operand.var x).reads n = false := by
    intro x hx n hn
    simp only [Operand.reads, beq_eq_false_iff_ne, ne_eq]
    rintro rfl
    exact hx hn
  have hta : operandIn (.block [] ids et :: ft) loc (.var a) = .ok (.int r.ty.width xa) := by
    rw [operandIn_code (E' := t), hst.operandIn loc (hunread a ha), hva]
  have htb : operandIn (.block [] ids et :: ft) loc (.var b) = .ok (.int r.ty.width xb) := by
    rw [operandIn_code (E' := t), hst.operandIn loc (hunread b hbv), hvb]
  have hx := fun x (hx : x ∈ [t0, t1, t2, t3]) => hne x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨v0, v1, v2, v3, hrun⟩ := ovf_runs hta htb hx.1.2.1 hnd.1.1
    (Ne.symm hx.2.2.1.2.2.1) (Ne.symm hnd.2.2.1) hcr1 hcr2'
  refine ⟨_, _, rfl, RunsPure.run hrun t, ⟨rfl, fun n => D n ∨ n ∈ [t0, t1, t2, t3], ?_⟩, ?_⟩
  rotate_left
  · intro i mi hi ei
    obtain ⟨envi, e⟩ := RunsPure.mid hrun t i (Nat.le_of_lt hi)
    rw [e, Except.ok.injEq] at ei
    subst ei
    exact ⟨rfl, shape_cons rfl hb⟩
  rw [ovfOuts_pair]
  simp only [bindTop, Env.bindAll]
  refine .block hb (fun n h => .inl (hDb n h)) hts ?_ ?_
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨hD, h0, h1, h2, h3⟩ := hn
    have := ((hag.insert r.name ((ovfOuts op signed xa xb).headD (.ptr none))).insert ov.name
      ((ovfOuts op signed xa xb).getD 1 (.ptr none))) n hD
    rw [← this]
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm h0, Ne.symm h1, Ne.symm h2,
      Ne.symm h3, ite_false, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
  · intro n hn
    rcases hn with hD | ht
    · exact hnrt n hD
    · exact hfresh n ht

/-- A successful check of results has one value per result. -/
theorem checkTypes_length {loc : Option Loc} : ∀ {rs : List Result} {vs : List RVal} {c c' : Core}
    {u : Unit}, checkTypes loc rs vs c = .ok (u, c') → rs.length = vs.length
  | [], [], _, _, _, _ => rfl
  | r :: rs, v :: vs, c, c', u, h => by
    unfold checkTypes at h
    simp only [List.length_cons, Nat.add_right_cancel_iff]
    split at h
    · exact checkTypes_length h
    · simp only [halt, throw, throwThe, MonadExceptOf.throw] at h
      cases h
  | [], _ :: _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, h => by cases h

theorem simpleOp_one {loc : Option Loc} {k : OpKind} {r : Result} {vs outs : List RVal}
    {c c' : Core} (h : simpleOp loc k [r] vs c = .ok (outs, c')) : ∃ v, outs = [v] := by
  rw [Fwd.simpleOp_eq] at h
  cases he : evalSimple loc k [r] vs c with
  | error e => rw [he] at h; cases h
  | ok p =>
    obtain ⟨o1, c1⟩ := p
    rw [he] at h
    simp only [Except.bind] at h
    cases hc : checkResults loc [r] o1 c1 with
    | error e => rw [hc] at h; cases h
    | ok q =>
      rw [hc] at h
      cases h
      rcases Dce.readOnly_checkTypes loc [r] outs c1 with ⟨e, ht, _⟩ | ⟨a, ht⟩
      · rw [checkResults_eq] at hc
        simp only [bind, StateT.bind, ht, Except.bind] at hc
        cases hc
      · have := checkTypes_length ht
        match outs, this with
        | [v], _ => exact ⟨v, rfl⟩

/-- At an expansion of a simple op: the source runs the op in one step and fails by getting
stuck or by UB, or the target runs the whole expansion to a state related to where the source
went, if the expansion's ops compute what the op does (`hrun`). -/
theorem site_gen {sp : SpaceCfg} {c : Core} {D Db : String → Prop} {k : OpKind}
    {res : List Result} {args : List Operand} {loc : Option Loc} {E : List Op}
    {ts : List String} {t s : List Op} {ids : List Nat} {et es : Env} {ft fs : List Frame}
    (hk1 : k.callee? = none) (hk2 : k.stackAlloc? = none) (hk3 : k.isTerminator = false)
    (hvars : ∀ a ∈ args, ∃ n, a = .var n) (hro : ∀ vs, Dce.ReadOnly (evalSimple loc k res vs))
    (hreads : ∀ n, (Op.mk k res args [] loc).reads n = true → opsReads n E = true)
    (hfresh : ∀ n ∈ ts, opsReads n t = false)
    (hts : OpsRel (L sp) t s) (hb : StackRel (L sp) Db ft fs) (hDb : ∀ n, Db n → D n)
    (hag : EnvAgree D et es) (hnr : NoReads D (E ++ t))
    (hrun : (∀ n, (Op.mk k res args [] loc).reads n = true →
          operandIn (.block [] ids et :: ft) loc (.var n) =
            operandIn (.block s ids es :: fs) loc (.var n)) →
        ∀ vs outs, operands (.block s ids es :: fs) loc args = .ok vs →
          simpleOp loc k res vs c = .ok (outs, c) →
          ∃ etF, RunsPure c ids ft E et etF ∧ ∀ n, n ∉ ts → etF[n]? = (et.bindAll res outs)[n]?) :
    (∃ h, step ⟨c, .block (.mk k res args [] loc :: s) ids es :: fs⟩ = .error h ∧
        h.outcome.Absorbing) ∨
    Runs sp E.length ⟨c, .block (E ++ t) ids et :: ft⟩
      ⟨c, .block (.mk k res args [] loc :: s) ids es :: fs⟩ := by
  have hnrE := hnr.append_left
  have hnrt := hnr.append_right
  have hst : StackRel (L sp) D (.block t ids et :: ft) (.block s ids es :: fs) :=
    .block hb hDb hts hag hnrt
  have hlook : ∀ n, (Op.mk k res args [] loc).reads n = true →
      operandIn (.block [] ids et :: ft) loc (.var n) = operandIn (.block s ids es :: fs) loc (.var n) := by
    intro n hn
    have hD : ¬ D n := fun hd => by
      have := hreads n hn
      rw [hnrE n hd] at this; cases this
    rw [operandIn_code (E' := t)]
    refine hst.operandIn loc fun m hm => ?_
    simp only [Operand.reads, beq_eq_false_iff_ne, ne_eq]
    rintro rfl
    exact hD hm
  simp only [Runs]
  rw [step_simple hk1 hk2 hk3]
  cases hops : operands (.block s ids es :: fs) loc args with
  | error h => exact .inl ⟨h, rfl, Dce.operands_vars_error hvars hops⟩
  | ok vs =>
  simp only [Except.bind]
  cases hop : simpleOp loc k res vs c with
  | error h =>
    refine .inl ⟨h, rfl, ?_⟩
    rcases Dce.readOnly_simpleOp (hro vs) c with ⟨h', e, hh⟩ | ⟨_, e⟩
    · rw [hop] at e; cases e; exact hh
    · rw [hop] at e; cases e
  | ok p =>
  obtain ⟨outs, c'⟩ := p
  have hc' : c' = c := by
    rcases Dce.readOnly_simpleOp (hro vs) c with ⟨h', e, _⟩ | ⟨_, e⟩
    · rw [hop] at e; cases e
    · rw [hop] at e; cases e; rfl
  subst hc'
  right
  obtain ⟨etF, hrun', hF⟩ := hrun hlook vs outs hops hop
  refine ⟨_, _, rfl, RunsPure.run hrun' t, ⟨rfl, fun n => D n ∨ n ∈ ts, ?_⟩, ?_⟩
  rotate_left
  · intro i mi hi ei
    obtain ⟨envi, e⟩ := RunsPure.mid hrun' t i (Nat.le_of_lt hi)
    rw [e, Except.ok.injEq] at ei
    subst ei
    exact ⟨rfl, shape_cons rfl hb⟩
  simp only [bindTop]
  refine .block hb (fun n h => .inl (hDb n h)) hts ?_ ?_
  · intro n hn
    simp only [not_or] at hn
    rw [hF n hn.2]
    exact hag.bindAll res outs n hn.1
  · intro n hn
    rcases hn with hD | ht
    · exact hnrt n hD
    · exact hfresh n ht

/-! ## Address expansions run -/

theorem lookup_of_reads {o : Op} {ids : List Nat} {et es : Env} {ft fs : List Frame} {s : List Op}
    {loc : Option Loc} (hlook : ∀ n, o.reads n = true →
      operandIn (.block [] ids et :: ft) loc (.var n) = operandIn (.block s ids es :: fs) loc (.var n))
    {n : String} (hn : o.reads n = true) {E : List Op} :
    operandIn (.block E ids et :: ft) loc (.var n) = operandIn (.block s ids es :: fs) loc (.var n) := by
  rw [operandIn_code (E' := [])]; exact hlook n hn

theorem field_hrun {sp : SpaceCfg} {c : Core} {ids : List Nat} {et es : Env} {ft fs : List Frame}
    {s : List Op} {inb : Bool} {T : Ty} {i : Nat} {r : Result} {p : String} {loc : Option Loc}
    {t0 : String} (hsp : c.space = sp)
    (hoff : ((T.fieldOffset? sp i).getD 0 : Int) < 2 ^ (sp.addrBits - 1)) (h0 : t0 ≠ p)
    (_h1 : t0 ≠ r.name)
    (hlook : ∀ n, (Op.mk (.ptrField inb T i) [r] [.var p] [] loc).reads n = true →
      operandIn (.block [] ids et :: ft) loc (.var n) = operandIn (.block s ids es :: fs) loc (.var n))
    (vs outs : List RVal) (hops : operands (.block s ids es :: fs) loc [.var p] = .ok vs)
    (hop : simpleOp loc (.ptrField inb T i) [r] vs c = .ok (outs, c)) :
    ∃ etF, RunsPure c ids ft
      [.mk (.const ((T.fieldOffset? sp i).getD 0)) [res t0 (.int sp.addrBits)] [] [] loc,
        .mk (.ptrOffset inb) [r] [.var p, .var t0] [] loc] et etF ∧
      ∀ n, n ∉ [t0] → etF[n]? = (et.bindAll [r] outs)[n]? := by
  subst hsp
  rw [operands_one] at hops
  cases hpv : operandIn (.block s ids es :: fs) loc (.var p) with
  | error e => rw [hpv] at hops; cases hops
  | ok pv =>
  rw [hpv] at hops
  cases hops
  obtain ⟨v, rfl⟩ := simpleOp_one hop
  refine ⟨_, .cons rfl rfl rfl rfl (op_const loc c t0 _ _) (.cons (v := v)
    (vs := [pv, .int c.space.addrBits (Sem.const c.space.addrBits ((T.fieldOffset? c.space i).getD 0))])
    rfl rfl rfl ?_ ?_ .nil), ?_⟩
  · dsimp only [res]
    rw [operands_pair, operandIn_insert_ne h0, lookup_of_reads hlook (by simp [Op.reads, Operand.reads]),
      hpv, operandIn_insert_self]; rfl
  · rw [simpleOp_congr (field_eq loc c inb T i r pv hoff)]; exact hop
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    simp only [Env.bindAll, Std.HashMap.getElem?_insert, beq_iff_eq, res, Ne.symm hn, ite_false]

theorem indexW_hrun {sp : SpaceCfg} {c : Core} {ids : List Nat} {et es : Env} {ft fs : List Frame}
    {s : List Op} {T : Ty} {r : Result} {p i : String} {loc : Option Loc} {t0 t1 : String}
    (hsp : c.space = sp) (_h01 : t0 ≠ t1) (hne : ∀ x ∈ [t0, t1], x ≠ p ∧ x ≠ i ∧ x ≠ r.name)
    (hlook : ∀ n, (Op.mk (.ptrIndex false T) [r] [.var p, .var i] [] loc).reads n = true →
      operandIn (.block [] ids et :: ft) loc (.var n) = operandIn (.block s ids es :: fs) loc (.var n))
    (vs outs : List RVal) (hops : operands (.block s ids es :: fs) loc [.var p, .var i] = .ok vs)
    (hop : simpleOp loc (.ptrIndex false T) [r] vs c = .ok (outs, c)) :
    ∃ etF, RunsPure c ids ft
      [.mk (.const (T.stride sp)) [res t0 (.int sp.addrBits)] [] [] loc,
        .mk (.arith .mul .wrap) [res t1 (.int sp.addrBits)] [.var i, .var t0] [] loc,
        .mk (.ptrOffset false) [r] [.var p, .var t1] [] loc] et etF ∧
      ∀ n, n ∉ [t0, t1] → etF[n]? = (et.bindAll [r] outs)[n]? := by
  subst hsp
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hne
  rw [operands_pair] at hops
  cases hpv : operandIn (.block s ids es :: fs) loc (.var p) with
  | error e => rw [hpv] at hops; cases hops
  | ok pv =>
  cases hiv : operandIn (.block s ids es :: fs) loc (.var i) with
  | error e => rw [hpv, hiv] at hops; cases hops
  | ok iv =>
  rw [hpv, hiv] at hops
  cases hops
  obtain ⟨v, rfl⟩ := simpleOp_one hop
  obtain ⟨x, rfl⟩ := index_src hop
  refine ⟨_, .cons rfl rfl rfl rfl (op_const loc c t0 _ _)
    (.cons rfl rfl rfl ?_ (op_wrap loc c .mul t1 x (Sem.const c.space.addrBits (T.stride c.space)))
    (.cons (v := v) (vs := [pv, .int c.space.addrBits
      (wrapVal .mul x (Sem.const c.space.addrBits (T.stride c.space)))]) rfl rfl rfl ?_ ?_ .nil)), ?_⟩
  · dsimp only [res]
    rw [operands_pair, operandIn_insert_ne hne.1.2.1,
      lookup_of_reads hlook (by simp [Op.reads, Operand.reads]), hiv, operandIn_insert_self]; rfl
  · dsimp only [res]
    rw [operands_pair, operandIn_insert_ne hne.2.1, operandIn_insert_ne hne.1.1,
      lookup_of_reads hlook (by simp [Op.reads, Operand.reads]), hpv, operandIn_insert_self]; rfl
  · rw [simpleOp_congr (indexW_eq loc c T r pv x)]; exact hop
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp only [Env.bindAll, Std.HashMap.getElem?_insert, beq_iff_eq, res, Ne.symm hn.1,
      Ne.symm hn.2, ite_false]

theorem indexI_hrun {sp : SpaceCfg} {c : Core} {ids : List Nat} {et es : Env} {ft fs : List Frame}
    {s : List Op} {T : Ty} {r : Result} {p i : String} {loc : Option Loc} {t0 t1 t2 t3 : String}
    (hsp : c.space = sp) (hst : T.stride sp < 2 ^ sp.addrBits) (hnd : [t0, t1, t2, t3].Nodup)
    (hne : ∀ x ∈ [t0, t1, t2, t3], x ≠ p ∧ x ≠ i ∧ x ≠ r.name)
    (hlook : ∀ n, (Op.mk (.ptrIndex true T) [r] [.var p, .var i] [] loc).reads n = true →
      operandIn (.block [] ids et :: ft) loc (.var n) = operandIn (.block s ids es :: fs) loc (.var n))
    (vs outs : List RVal) (hops : operands (.block s ids es :: fs) loc [.var p, .var i] = .ok vs)
    (hop : simpleOp loc (.ptrIndex true T) [r] vs c = .ok (outs, c)) :
    ∃ etF, RunsPure c ids ft
      [.mk .sext [res t0 (.int (2 * sp.addrBits))] [.var i] [] loc,
        .mk (.const (T.stride sp)) [res t1 (.int (2 * sp.addrBits))] [] [] loc,
        .mk (.arith .mul .wrap) [res t2 (.int (2 * sp.addrBits))] [.var t0, .var t1] [] loc,
        .mk (.trunc .nsw) [res t3 (.int sp.addrBits)] [.var t2] [] loc,
        .mk (.ptrOffset true) [r] [.var p, .var t3] [] loc] et etF ∧
      ∀ n, n ∉ [t0, t1, t2, t3] → etF[n]? = (et.bindAll [r] outs)[n]? := by
  subst hsp
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hne
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  rw [operands_pair] at hops
  cases hpv : operandIn (.block s ids es :: fs) loc (.var p) with
  | error e => rw [hpv] at hops; cases hops
  | ok pv =>
  cases hiv : operandIn (.block s ids es :: fs) loc (.var i) with
  | error e => rw [hpv, hiv] at hops; cases hops
  | ok iv =>
  rw [hpv, hiv] at hops
  cases hops
  obtain ⟨v, rfl⟩ := simpleOp_one hop
  obtain ⟨x, rfl⟩ := index_src hop
  refine ⟨_, .cons rfl rfl rfl ?_ (op_ext loc c true t0 _ x)
    (.cons rfl rfl rfl rfl (op_const loc c t1 _ _)
    (.cons rfl rfl rfl ?_ (op_wrap loc c .mul t2 (extVal true (2 * c.space.addrBits) x)
      (Sem.const (2 * c.space.addrBits) (T.stride c.space)))
    (.cons rfl rfl rfl ?_ (op_trunc loc c .nsw (res t3 (.int c.space.addrBits))
      (wrapVal .mul (extVal true (2 * c.space.addrBits) x)
        (Sem.const (2 * c.space.addrBits) (T.stride c.space)))
      (checkResults_plain loc c _ _ _ (hasTy_int _ _)))
    (.cons (v := v) (vs := [pv, .int c.space.addrBits (Sem.trunc .nsw c.space.addrBits
      (wrapVal .mul (extVal true (2 * c.space.addrBits) x)
        (Sem.const (2 * c.space.addrBits) (T.stride c.space))))]) rfl rfl rfl ?_ ?_ .nil)))), ?_⟩
  · rw [operands_one, lookup_of_reads hlook (by simp [Op.reads, Operand.reads]), hiv]; rfl
  · dsimp only [res]
    rw [operands_pair, operandIn_insert_ne (Ne.symm hnd.1.1), operandIn_insert_self,
      operandIn_insert_self]; rfl
  · dsimp only [res]
    rw [operands_one, operandIn_insert_self]; rfl
  · dsimp only [res]
    rw [operands_pair, operandIn_insert_ne hne.2.2.2.1, operandIn_insert_ne hne.2.2.1.1,
      operandIn_insert_ne hne.2.1.1, operandIn_insert_ne hne.1.1,
      lookup_of_reads hlook (by simp [Op.reads, Operand.reads]), hpv, operandIn_insert_self]; rfl
  · rw [simpleOp_congr (indexI_eq loc c T r pv x hst)]; exact hop
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp only [Env.bindAll, Std.HashMap.getElem?_insert, beq_iff_eq, res, Ne.symm hn.1,
      Ne.symm hn.2.1, Ne.symm hn.2.2.1, Ne.symm hn.2.2.2, ite_false]

/-! ## The simulation -/

/-- Related states: in lockstep (indexed by the target's block, which bounds how far an expansion
there can run), or partway through an expansion with `n` ops left. -/
def R (sp : SpaceCfg) (n : Nat) (mt ms : Machine) : Prop :=
  ms.core.space = sp ∧ ((MRel (L sp) mt ms ∧ n = Dce.topLen mt) ∨ (0 < n ∧ Runs sp n mt ms))

theorem R.trace {sp : SpaceCfg} {n : Nat} {mt ms : Machine} (h : R sp n mt ms) :
    Events.Refines mt.core.trace ms.core.trace := by
  rcases h.2 with ⟨⟨hc, _⟩, _⟩ | ⟨hn, _, _, _, _, _, hmid⟩
  · rw [hc]; exact Events.Refines.refl _
  · rw [(hmid 0 mt hn rfl).1]; exact Events.Refines.refl _

/-- Partway through an expansion: stutter, or take the source's one step at the end. -/
theorem runs_step {sp : SpaceCfg} {n : Nat} {mt ms : Machine} (hsp : ms.core.space = sp)
    (hn : 0 < n) (h : Runs sp n mt ms) : StepMatchS (R sp) n mt ms := by
  obtain ⟨ms', mt', es, en, hR', hmid⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_comm, runSteps_add, runSteps_one] at en
  cases e1 : step mt with
  | error h => rw [e1] at en; cases en
  | ok mt1 =>
  rw [e1, Except.ok_bind] at en
  refine ⟨fun mt'' e => ?_, fun h e => by rw [e1] at e; cases e⟩
  rw [e1, Except.ok.injEq] at e
  subst e
  cases k with
  | zero =>
    simp only [runSteps, Except.ok.injEq] at en
    subst en
    refine .inr (.inr ⟨0, ms', by rw [runSteps_one]; exact es, ⟨_, ?_, .inl ⟨hR', rfl⟩⟩, ?_⟩)
    · rw [step_space es]; exact hsp
    · intro j mj hj ej
      obtain rfl : j = 0 := by omega
      simp only [runSteps, Except.ok.injEq] at ej
      subst ej
      exact (hmid 0 mt (by omega) rfl).2.symm
  | succ k =>
    refine .inr (.inl ⟨k + 1, by omega, hsp, .inr ⟨by omega, ms', mt', es, en, hR', ?_⟩⟩)
    intro i mi hi ei
    have e : runSteps (i + 1) mt = .ok mi := by
      rw [Nat.add_comm, runSteps_add, runSteps_one, e1, Except.ok_bind]; exact ei
    exact hmid (i + 1) mi (by omega) e

/-- At an expansion that runs to the end: the target's first step starts it. -/
theorem start_step {sp : SpaceCfg} {mt ms : Machine} {n : Nat} (hsp : ms.core.space = sp)
    (h : Runs sp n mt ms) (h2 : 2 ≤ n) (m : Nat) (hm : n ≤ m) : StepMatchS (R sp) m mt ms := by
  obtain ⟨ms', mt', es, en, hR', hmid⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_comm, runSteps_add, runSteps_one] at en
  cases e1 : step mt with
  | error h => rw [e1] at en; cases en
  | ok mt1 =>
  rw [e1, Except.ok_bind] at en
  refine ⟨fun mt'' e => ?_, fun h e => by rw [e1] at e; cases e⟩
  rw [e1, Except.ok.injEq] at e
  subst e
  refine .inr (.inl ⟨k, by omega, hsp, .inr ⟨by omega, ms', mt', es, en, hR', ?_⟩⟩)
  intro i mi hi ei
  have e : runSteps (i + 1) mt = .ok mi := by
    rw [Nat.add_comm, runSteps_add, runSteps_one, e1, Except.ok_bind]; exact ei
  exact hmid (i + 1) mi (by omega) e

theorem sim (sp : SpaceCfg) : SimulationS (R sp) := by
  intro n mt ms ⟨hsp, h⟩
  rcases h with ⟨hR, rfl⟩ | ⟨hn, hruns⟩
  · obtain ⟨hc, D, hst⟩ := hR
    obtain ⟨ct, stt⟩ := mt
    obtain ⟨cs, sts⟩ := ms
    dsimp only at hc hst hsp ⊢
    subst hc
    have hshape : (Machine.mk ct sts).shape = (Machine.mk ct stt).shape := hst.shape.symm
    have lift : ∀ mt' k ms', runSteps (k + 1) ⟨ct, sts⟩ = .ok ms' → MRel (L sp) mt' ms' →
        ∃ n, R sp n mt' ms' :=
      fun mt' k ms' e h => ⟨_, by rw [runSteps_space e]; exact hsp, .inl ⟨h, rfl⟩⟩
    cases hst with
    | @block D Db t0 s0 ids et es ft fs hb hDb ho hag hnr =>
      rcases ho.head with hh | hh | ⟨pt, ps, t, s, rfl, rfl, hl, hts⟩
      · exact StepMatch.stutter ((StepMatch.of_lockstep hshape (Events.Refines.refl _)
          (step_eq hb hDb hag hnr (.inl hh))).mono lift)
      · exact StepMatch.stutter ((StepMatch.of_lockstep hshape (Events.Refines.refl _)
          (step_eq hb hDb hag hnr (.inr hh))).mono lift)
      · obtain ⟨o, ts, rfl, hE, hfresh⟩ := hl
        cases hE with
        | ovf hnd hne =>
          rcases site_ovf hnd hne hfresh hts hb hDb hag hnr with ⟨h, e, hab⟩ | hruns
          · have esc := Escapes.one (tt := ct.trace) (by rw [runSteps_one]; exact e) (.inl hab)
              (Events.Refines.refl _)
            exact ⟨fun _ _ => .inl esc, fun _ _ => .inl esc⟩
          · exact start_step hsp hruns (by simp [ovfOps]) _ (by simp [Dce.topLen, ovfOps])
        | field hoff h0 h1 =>
          rcases site_gen rfl rfl rfl (by simp) (readOnly_field _ _ _ _ _)
              (fun n hn => Exp.reads (Exp.field hoff h0 h1) hn) hfresh hts hb hDb hag hnr
              (fun hlook vs outs hops hop => field_hrun hsp hoff h0 h1 hlook vs outs hops hop) with
            ⟨h, e, hab⟩ | hruns
          · have esc := Escapes.one (tt := ct.trace) (by rw [runSteps_one]; exact e) (.inl hab)
              (Events.Refines.refl _)
            exact ⟨fun _ _ => .inl esc, fun _ _ => .inl esc⟩
          · exact start_step hsp hruns (by simp) _ (by simp [Dce.topLen])
        | indexW h01 hne =>
          rcases site_gen rfl rfl rfl (by simp) (readOnly_index _ _ _ _)
              (fun n hn => Exp.reads (Exp.indexW h01 hne) hn) hfresh hts hb hDb hag hnr
              (fun hlook vs outs hops hop => indexW_hrun hsp h01 hne hlook vs outs hops hop) with
            ⟨h, e, hab⟩ | hruns
          · have esc := Escapes.one (tt := ct.trace) (by rw [runSteps_one]; exact e) (.inl hab)
              (Events.Refines.refl _)
            exact ⟨fun _ _ => .inl esc, fun _ _ => .inl esc⟩
          · exact start_step hsp hruns (by simp) _ (by simp [Dce.topLen])
        | indexI hst hnd hne =>
          rcases site_gen rfl rfl rfl (by simp) (readOnly_index _ _ _ _)
              (fun n hn => Exp.reads (Exp.indexI hst hnd hne) hn) hfresh hts hb hDb hag hnr
              (fun hlook vs outs hops hop => indexI_hrun hsp hst hnd hne hlook vs outs hops hop) with
            ⟨h, e, hab⟩ | hruns
          · have esc := Escapes.one (tt := ct.trace) (by rw [runSteps_one]; exact e) (.inl hab)
              (Events.Refines.refl _)
            exact ⟨fun _ _ => .inl esc, fun _ _ => .inl esc⟩
          · exact start_step hsp hruns (by simp) _ (by simp [Dce.topLen])
    | nil => exact StepMatch.stutter ((StepMatch.of_lockstep hshape (Events.Refines.refl _) .halt).mono lift)
    | ifJoin => exact StepMatch.stutter ((StepMatch.of_lockstep hshape (Events.Refines.refl _) .halt).mono lift)
    | loop => exact StepMatch.stutter ((StepMatch.of_lockstep hshape (Events.Refines.refl _) .halt).mono lift)
    | call => exact StepMatch.stutter ((StepMatch.of_lockstep hshape (Events.Refines.refl _) .halt).mono lift)
    | blocks => exact StepMatch.stutter ((StepMatch.of_lockstep hshape (Events.Refines.refl _) .halt).mono lift)
  · exact runs_step hsp hn hruns

/-- Code related by expansions refines its source: the simulation theorem, with stuttering. -/
theorem refines_of_rel {mod : Module} {tgt src : Func} (hparams : tgt.params = src.params)
    (hrets : tgt.rets = src.rets) (hops : OpsRel (L mod.space) tgt.body.ops src.body.ops)
    (dec : src.Decided mod) : tgt.Refines mod src := by
  refine SimulationS.refines (sim mod.space) (fun _ _ _ h => h.trace) (fun oracle world args =>
    ⟨oracle, ?_⟩) dec
  have := init_lockstep (mod := mod) hparams hrets hops oracle world args
  rcases this with ⟨h, e1, e2⟩ | ⟨mt, ms, e1, e2, hR⟩
  · rw [e1, e2]
    by_cases hamb : h.outcome = .ambiguous
    · exact .inl ⟨h, rfl, .inr hamb⟩
    · exact .inr (.inr ⟨h, h, rfl, rfl, Outcome.Refines.refl _ hamb⟩)
  · rw [e1, e2]
    exact .inr (.inl ⟨mt, ms, rfl, rfl, _, init_space e2, .inl ⟨hR, rfl⟩⟩)

end Fir.Lower.Proof

namespace Fir.Lower.Proof

/-! ## The domain -/

/-- The ops the expansion pass rewrites. -/
def expands : OpKind → Bool
  | .overflow .. | .ptrField .. | .ptrIndex .. => true
  | _ => false

def Operand.isVar : Operand → Bool
  | .var _ => true
  | .hole .. => false

mutual
  /-- The ops the expansion pass rewrites have variables as operands, at any depth. -/
  def opVarArgs : Op → Bool
    | .mk k _ args regs _ => (!expands k || args.all Operand.isVar) && regionsVarArgs regs
  def regionsVarArgs : List Region → Bool
    | [] => true
    | .mk _ ops _ :: rs => opsVarArgs ops && regionsVarArgs rs
  def opsVarArgs : List Op → Bool
    | [] => true
    | o :: os => opVarArgs o && opsVarArgs os
end

mutual
  /-- Whether an op binds `%n`: as a result, or a parameter of a region in it, at any depth. -/
  def opBinds (n : String) : Op → Bool
    | .mk _ rs _ regs _ => rs.any (·.name == n) || regionsBinds n regs
  def regionsBinds (n : String) : List Region → Bool
    | [] => false
    | .mk ps ops _ :: rs => ps.any (·.name == n) || opsBinds n ops || regionsBinds n rs
  def opsBinds (n : String) : List Op → Bool
    | [] => false
    | o :: os => opBinds n o || opsBinds n os
end

/-- The names a temporary of the expansion pass may have: none of them is read or bound
anywhere in the code. -/
def NoTemps (ops : List Op) : Prop :=
  ∀ j, opsReads (tempName "e" j) ops = false ∧ opsBinds (tempName "e" j) ops = false

theorem fresh_run (pre : String) (k : Nat) : fresh pre k = .ok (tempName pre k, k + 1) := rfl

theorem tempName_ne {j k : Nat} (h : j ≠ k) : tempName "e" j ≠ tempName "e" k :=
  fun e => h (tempName_inj e)

/-- What `expandFlat` does to one op: nothing, or an expansion whose temporaries are numbered
from `k` up to `k1`. -/
theorem expandFlat_cases {sp : SpaceCfg} {o : Op} {k : Nat} {a : List Op} {k1 : Nat}
    (h : expandFlat sp o k = .ok (a, k1)) (hv : opVarArgs o = true)
    (hno : ∀ j, o.reads (tempName "e" j) = false ∧ opBinds (tempName "e" j) o = false) :
    (a = [o] ∧ k1 = k) ∨
    ∃ ts, Exp sp o a ts ∧ k ≤ k1 ∧ ∀ n ∈ ts, ∃ j, k ≤ j ∧ j < k1 ∧ n = tempName "e" j := by
  unfold expandFlat at h
  split at h
  · rename_i op signed r ov a' b' loc
    simp only [opVarArgs, expands, Bool.not_true, Bool.false_or, List.all_cons, List.all_nil,
      Bool.and_true, regionsVarArgs, Bool.and_eq_true] at hv
    obtain ⟨ha, hb⟩ := hv
    obtain ⟨na, rfl⟩ : ∃ n, a' = .var n := by
      cases a' with
      | var n => exact ⟨n, rfl⟩
      | hole => exact absurd ha (by simp [Operand.isVar])
    obtain ⟨nb, rfl⟩ : ∃ n, b' = .var n := by
      cases b' with
      | var n => exact ⟨n, rfl⟩
      | hole => exact absurd hb (by simp [Operand.isVar])
    simp only [bind, StateT.bind, fresh_run, pure, StateT.pure, Except.bind, Except.pure] at h
    cases h
    right
    refine ⟨_, .ovf ?_ ?_, by omega, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨tempName_ne (by omega), tempName_ne (by omega), tempName_ne (by omega)⟩,
        ⟨tempName_ne (by omega), tempName_ne (by omega)⟩, tempName_ne (by omega)⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨j, rfl⟩ : ∃ j, x = tempName "e" j := by
        rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
      obtain ⟨hr, hbd⟩ := hno j
      simp only [Op.reads, List.any_cons, List.any_nil, Operand.reads, regionsReads,
        Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hr
      simp only [opBinds, List.any_cons, List.any_nil, regionsBinds, Bool.or_false,
        Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hbd
      exact ⟨Ne.symm hr.1, Ne.symm hr.2, Ne.symm hbd.1, Ne.symm hbd.2⟩
    · intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl
      · exact ⟨k, by omega, by omega, rfl⟩
      · exact ⟨k + 1, by omega, by omega, rfl⟩
      · exact ⟨k + 2, by omega, by omega, rfl⟩
      · exact ⟨k + 3, by omega, by omega, rfl⟩
  · rename_i inb T i r p' loc
    simp only [opVarArgs, expands, Bool.not_true, Bool.false_or, List.all_cons, List.all_nil,
      Bool.and_true, regionsVarArgs] at hv
    obtain ⟨np, rfl⟩ : ∃ n, p' = .var n := by
      cases p' with
      | var n => exact ⟨n, rfl⟩
      | hole => exact absurd hv (by simp [Operand.isVar])
    by_cases hoff : (T.fieldOffset? sp i).getD 0 < 2 ^ (sp.addrBits - 1)
    · simp only [hoff, bind, pure,
        ] at h
      cases h
      right
      obtain ⟨hr, hbd⟩ := hno k
      simp only [Op.reads, List.any_cons, List.any_nil, Operand.reads, regionsReads,
        Bool.or_false, beq_eq_false_iff_ne, ne_eq] at hr
      simp only [opBinds, List.any_cons, List.any_nil, regionsBinds, Bool.or_false,
        beq_eq_false_iff_ne, ne_eq] at hbd
      refine ⟨_, .field (by exact_mod_cast hoff) (Ne.symm hr) (Ne.symm hbd), by omega, ?_⟩
      intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      exact ⟨k, by omega, by omega, hn⟩
    · simp only [hoff, bind, throw,
        throwThe, MonadExceptOf.throw] at h
      cases h
  · rename_i T r p' i' loc
    simp only [opVarArgs, expands, Bool.not_true, Bool.false_or, List.all_cons, List.all_nil,
      Bool.and_true, regionsVarArgs, Bool.and_eq_true] at hv
    obtain ⟨hp, hi⟩ := hv
    obtain ⟨np, rfl⟩ : ∃ n, p' = .var n := by
      cases p' with
      | var n => exact ⟨n, rfl⟩
      | hole => exact absurd hp (by simp [Operand.isVar])
    obtain ⟨ni, rfl⟩ : ∃ n, i' = .var n := by
      cases i' with
      | var n => exact ⟨n, rfl⟩
      | hole => exact absurd hi (by simp [Operand.isVar])
    by_cases hst : T.stride sp < 2 ^ sp.addrBits
    · simp only [hst, bind, pure,
        ] at h
      cases h
      right
      refine ⟨_, .indexI hst ?_ ?_, by omega, ?_⟩
      · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true, not_false_eq_true]
        exact ⟨⟨tempName_ne (by omega), tempName_ne (by omega), tempName_ne (by omega)⟩,
          ⟨tempName_ne (by omega), tempName_ne (by omega)⟩, tempName_ne (by omega)⟩
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨j, rfl⟩ : ∃ j, x = tempName "e" j := by
          rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
        obtain ⟨hr, hbd⟩ := hno j
        simp only [Op.reads, List.any_cons, List.any_nil, Operand.reads, regionsReads,
          Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hr
        simp only [opBinds, List.any_cons, List.any_nil, regionsBinds, Bool.or_false,
          beq_eq_false_iff_ne, ne_eq] at hbd
        exact ⟨Ne.symm hr.1, Ne.symm hr.2, Ne.symm hbd⟩
      · intro n hn
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl
        · exact ⟨k, by omega, by omega, rfl⟩
        · exact ⟨k + 1, by omega, by omega, rfl⟩
        · exact ⟨k + 2, by omega, by omega, rfl⟩
        · exact ⟨k + 3, by omega, by omega, rfl⟩
    · simp only [hst, bind, throw,
        throwThe, MonadExceptOf.throw] at h
      cases h
  · rename_i T r p' i' loc
    simp only [opVarArgs, expands, Bool.not_true, Bool.false_or, List.all_cons, List.all_nil,
      Bool.and_true, regionsVarArgs, Bool.and_eq_true] at hv
    obtain ⟨hp, hi⟩ := hv
    obtain ⟨np, rfl⟩ : ∃ n, p' = .var n := by
      cases p' with
      | var n => exact ⟨n, rfl⟩
      | hole => exact absurd hp (by simp [Operand.isVar])
    obtain ⟨ni, rfl⟩ : ∃ n, i' = .var n := by
      cases i' with
      | var n => exact ⟨n, rfl⟩
      | hole => exact absurd hi (by simp [Operand.isVar])
    simp only [bind, StateT.bind, fresh_run, pure, StateT.pure, Except.bind, Except.pure] at h
    cases h
    right
    refine ⟨_, .indexW (tempName_ne (by omega)) ?_, by omega, ?_⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨j, rfl⟩ : ∃ j, x = tempName "e" j := by
        rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩
      obtain ⟨hr, hbd⟩ := hno j
      simp only [Op.reads, List.any_cons, List.any_nil, Operand.reads, regionsReads,
        Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hr
      simp only [opBinds, List.any_cons, List.any_nil, regionsBinds, Bool.or_false,
        beq_eq_false_iff_ne, ne_eq] at hbd
      exact ⟨Ne.symm hr.1, Ne.symm hr.2, Ne.symm hbd⟩
    · intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl
      · exact ⟨k, by omega, by omega, rfl⟩
      · exact ⟨k + 1, by omega, by omega, rfl⟩
  · simp only [pure, StateT.pure, Except.pure] at h
    cases h
    exact .inl ⟨rfl, rfl⟩

/-- An expansion reads what its source op reads or binds, and its temporaries. -/
theorem Exp.reads_out {sp : SpaceCfg} {o : Op} {E : List Op} {ts : List String} (h : Exp sp o E ts)
    {n : String} (hn : opsReads n E = true) : o.reads n = true ∨ opBinds n o = true ∨ n ∈ ts := by
  cases h <;>
  · simp only [ovfOps, opsReads, Op.reads, regionsReads, List.any_cons, List.any_nil,
      Operand.reads, Bool.or_false, Bool.or_eq_true, beq_iff_eq, opBinds, regionsBinds,
      List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    grind

/-- What expanding gives, for an op, its region, and an op list. -/
def ExpOut (k k1 : Nat) (reads binds : String → Bool) (out : List Op) : Prop :=
  k ≤ k1 ∧ ∀ n, opsReads n out = true →
    reads n = true ∨ binds n = true ∨ ∃ j, k ≤ j ∧ j < k1 ∧ n = tempName "e" j

theorem temp_unread {k k1 k2 : Nat} {reads binds : String → Bool} {b : List Op}
    (hb : ∀ n, opsReads n b = true → reads n = true ∨ binds n = true ∨
      ∃ j, k1 ≤ j ∧ j < k2 ∧ n = tempName "e" j)
    (hno : ∀ j, reads (tempName "e" j) = false ∧ binds (tempName "e" j) = false)
    {n : String} (hn : ∃ j, k ≤ j ∧ j < k1 ∧ n = tempName "e" j) : opsReads n b = false := by
  obtain ⟨j, -, hj, rfl⟩ := hn
  cases hr : opsReads (tempName "e" j) b
  · rfl
  · rcases hb _ hr with h | h | ⟨j', hj', -, e⟩
    · rw [(hno j).1] at h; cases h
    · rw [(hno j).2] at h; cases h
    · have := tempName_inj e; omega

mutual
  theorem expandOp_rel (sp : SpaceCfg) : ∀ (o : Op) (k : Nat) (a : List Op) (k1 : Nat),
      expandOp sp o k = .ok (a, k1) → opVarArgs o = true →
      (∀ j, o.reads (tempName "e" j) = false ∧ opBinds (tempName "e" j) o = false) →
      ExpOut k k1 (o.reads) (fun n => opBinds n o) a ∧
      ((∃ o', a = [o'] ∧ OpRel (L sp) o' o) ∨
        ∃ ts, Exp sp o a ts ∧ ∀ n ∈ ts, ∃ j, k ≤ j ∧ j < k1 ∧ n = tempName "e" j)
    | .mk kind rs args [] loc, k, a, k1, h, hv, hno => by
      simp only [expandOp] at h
      rcases expandFlat_cases h hv hno with ⟨rfl, rfl⟩ | ⟨ts, hE, hk, hts⟩
      · refine ⟨⟨Nat.le_refl _, fun n hn => ?_⟩, .inl ⟨_, rfl, .refl _⟩⟩
        simp only [opsReads, Bool.or_false] at hn
        exact .inl hn
      · refine ⟨⟨hk, fun n hn => ?_⟩, .inr ⟨ts, hE, hts⟩⟩
        rcases hE.reads_out hn with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (hts n h))
    | .mk kind rs args (r :: regs) loc, k, a, k1, h, hv, hno => by
      simp only [expandOp, bind, StateT.bind, Except.bind] at h
      cases hr : expandRegions sp (r :: regs) k with
      | error e => rw [hr] at h; cases h
      | ok p =>
        obtain ⟨regs', k2⟩ := p
        rw [hr] at h
        simp only [pure, StateT.pure, Except.pure] at h
        cases h
        simp only [opVarArgs, Bool.and_eq_true] at hv
        have hno' : ∀ j, regionsReads (tempName "e" j) (r :: regs) = false ∧
            regionsBinds (tempName "e" j) (r :: regs) = false := fun j => by
          obtain ⟨h1, h2⟩ := hno j
          simp only [Op.reads, opBinds, Bool.or_eq_false_iff] at h1 h2
          exact ⟨h1.2, h2.2⟩
        obtain ⟨⟨hk, hreads⟩, hrel⟩ := expandRegions_rel sp (r :: regs) k regs' k1 hr hv.2 hno'
        refine ⟨⟨hk, fun n hn => ?_⟩, .inl ⟨_, rfl, .regions hrel⟩⟩
        simp only [opsReads, Op.reads, Bool.or_false, Bool.or_eq_true] at hn
        rcases hn with hn | hn
        · exact .inl (by simp [Op.reads, hn])
        · rcases hreads n hn with h | h | h
          · exact .inl (by simp [Op.reads, h])
          · exact .inr (.inl (by simp [opBinds, h]))
          · exact .inr (.inr h)
  theorem expandOps_rel (sp : SpaceCfg) : ∀ (ops : List Op) (k : Nat) (ops' : List Op) (k1 : Nat),
      expandOps sp ops k = .ok (ops', k1) → opsVarArgs ops = true → NoTemps ops →
      ExpOut k k1 (fun n => opsReads n ops) (fun n => opsBinds n ops) ops' ∧
        OpsRel (L sp) ops' ops
    | [], k, ops', k1, h, _, _ => by
      simp only [expandOps, pure, StateT.pure, Except.pure] at h
      cases h
      exact ⟨⟨Nat.le_refl _, fun n hn => by simp [opsReads] at hn⟩, .refl _⟩
    | o :: os, k, ops', k2, h, hv, hno => by
      simp only [expandOps, bind, StateT.bind, Except.bind] at h
      cases ho : expandOp sp o k with
      | error e => rw [ho] at h; cases h
      | ok p =>
      obtain ⟨a, k1⟩ := p
      rw [ho] at h
      dsimp only at h
      cases hos : expandOps sp os k1 with
      | error e => rw [hos] at h; cases h
      | ok q =>
      obtain ⟨b, k2'⟩ := q
      rw [hos] at h
      simp only [pure, StateT.pure, Except.pure] at h
      cases h
      simp only [opsVarArgs, Bool.and_eq_true] at hv
      have hno1 : ∀ j, o.reads (tempName "e" j) = false ∧ opBinds (tempName "e" j) o = false :=
        fun j => by
          obtain ⟨h1, h2⟩ := hno j
          simp only [opsReads, opsBinds, Bool.or_eq_false_iff] at h1 h2
          exact ⟨h1.1, h2.1⟩
      have hno2 : NoTemps os := fun j => by
        obtain ⟨h1, h2⟩ := hno j
        simp only [opsReads, opsBinds, Bool.or_eq_false_iff] at h1 h2
        exact ⟨h1.2, h2.2⟩
      obtain ⟨⟨hk1, hra⟩, hrel1⟩ := expandOp_rel sp o k a k1 ho hv.1 hno1
      obtain ⟨⟨hk2, hrb⟩, hrel2⟩ := expandOps_rel sp os k1 b k2 hos hv.2 hno2
      refine ⟨⟨by omega, fun n hn => ?_⟩, ?_⟩
      · rw [opsReads_append] at hn
        simp only [Bool.or_eq_true] at hn
        rcases hn with hn | hn
        · rcases hra n hn with h | h | ⟨j, hj, hj', e⟩
          · exact .inl (by simp [opsReads, h])
          · exact .inr (.inl (by simp [opsBinds, h]))
          · exact .inr (.inr ⟨j, hj, by omega, e⟩)
        · rcases hrb n hn with h | h | ⟨j, hj, hj', e⟩
          · exact .inl (by simp [opsReads, h])
          · exact .inr (.inl (by simp [opsBinds, h]))
          · exact .inr (.inr ⟨j, by omega, hj', e⟩)
      · rcases hrel1 with ⟨o', rfl, ho'⟩ | ⟨ts, hE, hts⟩
        · exact .cons ho' hrel2
        · exact .rw (pt := a) (ps := [o]) ⟨o, ts, rfl, hE, fun n hn =>
            temp_unread hrb hno2 (hts n hn)⟩ hrel2
  theorem expandRegions_rel (sp : SpaceCfg) : ∀ (regs : List Region) (k : Nat)
      (regs' : List Region) (k1 : Nat), expandRegions sp regs k = .ok (regs', k1) →
      regionsVarArgs regs = true →
      (∀ j, regionsReads (tempName "e" j) regs = false ∧ regionsBinds (tempName "e" j) regs = false) →
      (k ≤ k1 ∧ ∀ n, regionsReads n regs' = true → regionsReads n regs = true ∨
          regionsBinds n regs = true ∨ ∃ j, k ≤ j ∧ j < k1 ∧ n = tempName "e" j) ∧
        RegionsRel (L sp) regs' regs
    | [], k, regs', k1, h, _, _ => by
      simp only [expandRegions, pure, StateT.pure, Except.pure] at h
      cases h
      exact ⟨⟨Nat.le_refl _, fun n hn => by simp [regionsReads] at hn⟩, .nil⟩
    | .mk ps ops lbl :: rs, k, regs', k2, h, hv, hno => by
      simp only [expandRegions, bind, StateT.bind, Except.bind] at h
      cases ho : expandOps sp ops k with
      | error e => rw [ho] at h; cases h
      | ok p =>
      obtain ⟨ops', k1⟩ := p
      rw [ho] at h
      dsimp only at h
      cases hrs : expandRegions sp rs k1 with
      | error e => rw [hrs] at h; cases h
      | ok q =>
      obtain ⟨rs', k2'⟩ := q
      rw [hrs] at h
      simp only [pure, StateT.pure, Except.pure] at h
      cases h
      simp only [regionsVarArgs, Bool.and_eq_true] at hv
      have hno1 : NoTemps ops := fun j => by
        obtain ⟨h1, h2⟩ := hno j
        simp only [regionsReads, regionsBinds, Bool.or_eq_false_iff] at h1 h2
        exact ⟨h1.1, h2.1.2⟩
      have hno2 : ∀ j, regionsReads (tempName "e" j) rs = false ∧
          regionsBinds (tempName "e" j) rs = false := fun j => by
        obtain ⟨h1, h2⟩ := hno j
        simp only [regionsReads, regionsBinds, Bool.or_eq_false_iff] at h1 h2
        exact ⟨h1.2, h2.2⟩
      obtain ⟨⟨hk1, hra⟩, hrel1⟩ := expandOps_rel sp ops k ops' k1 ho hv.1 hno1
      obtain ⟨⟨hk2, hrb⟩, hrel2⟩ := expandRegions_rel sp rs k1 rs' k2 hrs hv.2 hno2
      refine ⟨⟨by omega, fun n hn => ?_⟩, .cons hrel1 hrel2⟩
      simp only [regionsReads, Bool.or_eq_true] at hn
      rcases hn with hn | hn
      · rcases hra n hn with h | h | ⟨j, hj, hj', e⟩
        · exact .inl (by simp [regionsReads, h])
        · exact .inr (.inl (by simp [regionsBinds, h]))
        · exact .inr (.inr ⟨j, hj, by omega, e⟩)
      · rcases hrb n hn with h | h | ⟨j, hj, hj', e⟩
        · exact .inl (by simp [regionsReads, h])
        · exact .inr (.inl (by simp [regionsBinds, h]))
        · exact .inr (.inr ⟨j, by omega, hj', e⟩)
end

/-- **The expansion pass is correct.** For a function none of whose names (read or bound, at any
depth) is a temporary of the pass (`%.e0`, `%.e1`, …) and whose checked arithmetic, `ptr.field`,
and `ptr.index` ops take variables as operands, the expanded function refines the original in
the module, for every argument, oracle, and monotone world. -/
theorem Expand.refines {mod : Module} {f g : Func} (h : expand mod.space f = .ok g)
    (hv : opsVarArgs f.body.ops = true) (hno : NoTemps f.body.ops) (dec : f.Decided mod) :
    g.Refines mod f := by
  simp only [expand, bind, Except.bind, StateT.run] at h
  cases he : expandOps mod.space f.body.ops 0 with
  | error e => rw [he] at h; cases h
  | ok p =>
    rw [he] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨-, hrel⟩ := expandOps_rel mod.space f.body.ops 0 p.1 p.2 he hv hno
    exact refines_of_rel rfl rfl hrel dec

end Fir.Lower.Proof

namespace Fir.Lower.Proof

/-- **The lowering is correct where scalarizing changes nothing**: for a function with no
aggregate, union, or slice values (scalarizing gives it back unchanged), in the expansion's domain,
the lowered function refines the original. Scalarizing itself is not proved yet. -/
theorem lowerFunc_refines {mod : Module} {f g : Func} (h : lowerFunc mod.space f = .ok g)
    (hs : scalarize mod.space f = .ok f) (hv : opsVarArgs f.body.ops = true)
    (hno : NoTemps f.body.ops) (dec : f.Decided mod) : g.Refines mod f := by
  simp only [lowerFunc, hs, bind, Except.bind, tryCatch, tryCatchThe, MonadExceptOf.tryCatch,
    Except.tryCatch] at h
  cases he : expand mod.space f with
  | error e => rw [he] at h; cases h
  | ok g' =>
    rw [he] at h
    simp only [Except.ok.injEq] at h
    subst h
    exact Expand.refines he hv hno dec

/-! A function of scalars with checked arithmetic and an element address, which scalarizing
leaves unchanged (as printed), so `lowerFunc_refines` covers its whole lowering. -/

private def scalarExample : String :=
  "func @f(%a: i32, %b: i32, %p: ptr) -> (i32, i1, ptr) {
  %r: i32, %o: i1 = int.mul.overflow.s %a, %b
  %i: i64 = int.sext %r
  %q: ptr = ptr.index.inbounds struct<C>{i8, i32} %p, %i
  func.ret %r, %o, %q
}"

#guard match parseModule scalarExample with
  | .ok m => match m.funcs with
    | [f] => match scalarize m.space f with
      | .ok g => g.render false == f.render false
      | .error _ => false
    | _ => false
  | .error _ => false

end Fir.Lower.Proof
