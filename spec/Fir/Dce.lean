import Fir.CopyProp

/-!
# Dead code elimination

An op whose results nothing reads can be deleted, if running it can't do anything else:

```
%y: T = copy %x          // deleted: no later op in the region reads %y
%z: T = int.add.wrap %a, %b
```

`Dce.refines` proves the rewrite correct at any number of places in a function, at any depth.
It covers every *pure* op (`Pure`): no regions, no call, no stack allocation, not a terminator,
operands that are variables, and a computation that leaves the core as it was and fails only by
UB or getting stuck (`ReadOnly`). `copy_pure` shows copies qualify; so do `const` and `poison`.
"Reads" is syntactic (`opsReads`): an operand anywhere in the ops after the deleted one in its
region, at any depth inside their regions. Calls need nothing special: a callee can't see the
caller's frames.

This is the first proof whose machines have different environments. After the source runs the
deleted op, its block binds the op's results and the target's doesn't. The lockstep relation
(`StackRel`) allows that: the results become hidden names of that block, which no target code
still to run reads, so every lookup the target makes gets the source's answer.

The target doesn't step while the source runs a deleted op, so each target step is matched by
the deleted ops before it (consecutive ones too), then the step itself; `sim_len` counts them
down by the length of the source's current block.

If the source fails at the deleted op (an undefined `%x`, a value of the wrong type, a broken
fact), that is UB or a malformed program, so the target may do anything.
-/

namespace Fir.Dce

/-! ## Computations that only read the core -/

/-- A core computation that leaves the core as it was, and fails only by UB or getting stuck. A
target may skip it. -/
def ReadOnly (x : CM α) : Prop :=
  ∀ c, (∃ h, x c = .error h ∧ h.outcome.Absorbing) ∨ ∃ a, x c = .ok (a, c)

namespace ReadOnly

theorem pure' (a : α) : ReadOnly (pure a : CM α) := fun _ => .inr ⟨a, rfl⟩

theorem get' : ReadOnly (get : CM Core) := fun c => .inr ⟨c, rfl⟩

theorem stuck (msg : String) (loc : Option Loc) (note : String) :
    ReadOnly (halt (.stuck msg) loc note : CM α) := fun _ => .inl ⟨_, rfl, trivial⟩

theorem ub' (k : UBKind) (loc : Option Loc) (note : String) :
    ReadOnly (ub k loc note : CM α) := fun _ => .inl ⟨_, rfl, trivial⟩

theorem bind' {x : CM α} {f : α → CM β} (hx : ReadOnly x) (hf : ∀ a, ReadOnly (f a)) :
    ReadOnly (x >>= f) := by
  intro c
  rcases hx c with ⟨h, e, hh⟩ | ⟨a, e⟩
  · exact .inl ⟨h, by simp only [bind, StateT.bind, Except.bind, e], hh⟩
  · have : (x >>= f) c = f a c := by simp only [bind, StateT.bind, Except.bind, e]
    rw [this]
    exact hf a c

theorem ite' {p : Prop} [Decidable p] {x y : CM α} (hx : ReadOnly x) (hy : ReadOnly y) :
    ReadOnly (if p then x else y) := by
  split <;> assumption

theorem forIn' {l : List α} {init : β} {f : α → β → CM (ForInStep β)}
    (hf : ∀ a b, ReadOnly (f a b)) : ReadOnly (forIn l init f) := by
  induction l generalizing init with
  | nil => exact pure' _
  | cons a l ih =>
    rw [List.forIn_cons]
    refine bind' (hf a init) fun s => ?_
    cases s with
    | done b => exact pure' _
    | yield b => exact ih

end ReadOnly

theorem readOnly_getAlloc (loc : Option Loc) (a : Nat) : ReadOnly (getAlloc loc a) := by
  intro c
  simp only [getAlloc, allocIn, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, pure, Except.pure]
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl ⟨_, rfl, trivial⟩

theorem readOnly_factHolds (loc : Option Loc) (f : Fact) (v : RVal) :
    ReadOnly (factHolds loc f v) := by
  unfold factHolds ptrFactHolds
  split
  · exact ReadOnly.pure' _
  · split
    · exact ReadOnly.pure' _
    · exact ReadOnly.bind' (readOnly_getAlloc _ _) fun _ => ReadOnly.pure' _
    · exact ReadOnly.pure' _
    · exact ReadOnly.pure' _
  · exact ReadOnly.pure' _

theorem readOnly_checkTypes (loc : Option Loc) : ∀ (rs : List Result) (vs : List RVal),
    ReadOnly (checkTypes loc rs vs)
  | [], [] => ReadOnly.pure' _
  | r :: rs, v :: vs => by
    unfold checkTypes
    dsimp only
    split
    · exact readOnly_checkTypes loc rs vs
    · exact ReadOnly.bind' (ReadOnly.stuck _ _ _) fun _ => readOnly_checkTypes loc rs vs
  | [], _ :: _ => ReadOnly.stuck _ _ _
  | _ :: _, [] => ReadOnly.stuck _ _ _

/-- Checking results only reads the core. -/
theorem readOnly_checkResults (loc : Option Loc) (rs : List Result) (vs : List RVal) :
    ReadOnly (checkResults loc rs vs) := by
  unfold checkResults
  refine ReadOnly.bind' (readOnly_checkTypes loc rs vs) fun _ => ?_
  refine ReadOnly.bind' (ReadOnly.forIn' fun _ _ => ?_) fun _ => ReadOnly.pure' _
  refine ReadOnly.bind' (ReadOnly.forIn' fun _ _ => ?_) fun _ => ReadOnly.pure' _
  refine ReadOnly.bind' (readOnly_factHolds _ _ _) fun _ => ?_
  exact ReadOnly.ite' (ReadOnly.pure' _) (ReadOnly.bind' (ReadOnly.ub' _ _ _) fun _ => ReadOnly.pure' _)

theorem readOnly_simpleOp {loc : Option Loc} {k : OpKind} {res : List Result} {vs : List RVal}
    (h : ReadOnly (evalSimple loc k res vs)) : ReadOnly (simpleOp loc k res vs) := by
  unfold simpleOp
  exact ReadOnly.bind' h fun outs =>
    ReadOnly.bind' (readOnly_checkResults _ _ _) fun _ => ReadOnly.pure' _

/-! ## The rewrite -/

/-- An op dead code elimination may delete when nothing reads its results: it has no regions,
calls no function, allocates no stack memory, isn't a terminator, has only variables as operands,
and computing it only reads the core. -/
def Pure (o : Op) : Prop :=
  ∃ k res args loc, o = .mk k res args [] loc ∧ k.callee? = none ∧ k.stackAlloc? = none ∧
    k.isTerminator = false ∧ (∀ a ∈ args, ∃ n, a = .var n) ∧
    ∀ vs, ReadOnly (evalSimple loc k res vs)

/-- The rewrite: the target has nothing where the source has a pure op whose results the rest of
the target's region doesn't read. -/
def L (pt ps t : List Op) : Prop :=
  ∃ o, pt = [] ∧ ps = [o] ∧ Pure o ∧ ∀ r ∈ o.results, opsReads r.name t = false

/-- **Copies are pure.** -/
theorem copy_pure (x y : String) (T : Ty) (facts : List TrustedFact) (loc : Option Loc) :
    Pure (CopyProp.copyOp x y T facts loc) := by
  refine ⟨.copy, _, _, loc, rfl, rfl, rfl, rfl, by simp, fun vs c => ?_⟩
  match vs with
  | [v] => exact .inr ⟨[v], rfl⟩
  | [] => exact .inl ⟨_, rfl, trivial⟩
  | _ :: _ :: _ => exact .inl ⟨_, rfl, trivial⟩

theorem const_pure (n : Int) (r : Result) (loc : Option Loc) :
    Pure (.mk (.const n) [r] [] [] loc) := by
  refine ⟨.const n, _, _, loc, rfl, rfl, rfl, rfl, by simp, fun vs c => ?_⟩
  match vs with
  | [] => exact .inr ⟨_, rfl⟩
  | _ :: _ => exact .inl ⟨_, rfl, trivial⟩

theorem poison_pure (r : Result) (loc : Option Loc) : Pure (.mk .poison [r] [] [] loc) := by
  refine ⟨.poison, _, _, loc, rfl, rfl, rfl, rfl, by simp, fun vs c => ?_⟩
  match vs with
  | [] =>
    obtain ⟨n, ty, facts⟩ := r
    cases ty <;> exact .inr ⟨_, rfl⟩
  | _ :: _ => exact .inl ⟨_, rfl, trivial⟩

/-! ## Steps -/

/-- Operands that are variables fail only by getting stuck. -/
theorem operands_vars_error {fs : List Frame} {loc : Option Loc} :
    ∀ {args : List Operand}, (∀ a ∈ args, ∃ n, a = .var n) → ∀ {h : Halt},
      operands fs loc args = .error h → h.outcome.Absorbing
  | [], _, _, e => by cases e
  | a :: args, hv, h, e => by
    obtain ⟨n, rfl⟩ := hv a (by simp)
    simp only [operands, List.mapM_cons] at e
    cases ha : operandIn fs loc (.var n) with
    | error h' =>
      rw [ha] at e; cases e; exact operandIn_var_error ha
    | ok v =>
      rw [ha] at e
      cases hr : List.mapM (operandIn fs loc) args with
      | error h' =>
        rw [hr] at e; cases e
        exact operands_vars_error (fun a h => hv a (by simp [h])) hr
      | ok vs => rw [hr] at e; cases e

/-- The size of the source's current block: how many ops it can still run ahead. -/
def topLen (m : Machine) : Nat :=
  match m.stack with
  | .block ops _ _ :: _ => ops.length
  | _ => 0

/-- At a deleted op: the source runs it and escapes, or binds its results where nothing the
target runs will read them, and the machines are related again. -/
theorem step_deleted {mt ms : Machine} {o : Op} {t s : List Op} {ids : List Nat} {et es : Env}
    {ft fs : List Frame} {D Db : String → Prop} (hc : mt.core = ms.core) (hp : Pure o)
    (hunread : ∀ r ∈ o.results, opsReads r.name t = false) (hts : OpsRel L t s)
    (hb : StackRel L Db ft fs) (hDb : ∀ n, Db n → D n) (hag : EnvAgree D et es)
    (hnr : NoReads D t) (ht : mt.stack = .block t ids et :: ft)
    (hs : ms.stack = .block (o :: s) ids es :: fs) :
    Escapes mt.core.trace ms ∨ ∃ ms1, step ms = .ok ms1 ∧ MRel L mt ms1 ∧ topLen ms1 = s.length := by
  obtain ⟨k, res, args, loc, rfl, h1, h2, h3, hvars, hro⟩ := hp
  obtain ⟨c, stt⟩ := mt
  obtain ⟨cs, sts⟩ := ms
  dsimp only at hc ht hs
  subst hc ht hs
  have e := step_simple (c := c) (k := k) (res := res) (args := args) (loc := loc) (t := s)
    (ids := ids) (env := es) (fs := fs) h1 h2 h3
  cases hv : operands (.block s ids es :: fs) loc args with
  | error h =>
    exact .inl (Escapes.one (by rw [runSteps_one, e, hv]; rfl) (.inl (operands_vars_error hvars hv))
      (Events.Refines.refl _))
  | ok vs =>
  rw [hv] at e
  rcases readOnly_simpleOp (hro vs) c with ⟨h, e1, hh⟩ | ⟨outs, e1⟩
  · exact .inl (Escapes.one (by rw [runSteps_one, e]; simp only [Except.bind, e1]) (.inl hh)
      (Events.Refines.refl _))
  · refine .inr ⟨⟨c, bindTop res outs (.block s ids es :: fs)⟩,
      by rw [e]; simp only [Except.bind, e1], ⟨rfl, fun n => D n ∨ ∃ r ∈ res, r.name = n, ?_⟩, rfl⟩
    refine .block hb (fun n h => .inl (hDb n h)) hts (fun n hn => ?_) (fun n hn => ?_)
    · simp only [not_or, not_exists, not_and] at hn
      rw [hag n hn.1, Env.getElem?_bindAll es res outs hn.2]
    · rcases hn with hn | ⟨r, hr, rfl⟩
      · exact hnr n hn
      · exact hunread r hr

theorem sim_len (n : Nat) : ∀ mt ms, topLen ms = n → MRel L mt ms → StepMatch (MRel L) mt ms := by
  induction n with
  | zero =>
    intro mt ms hn hR
    refine StepMatch.of_mrel hR (fun _ _ _ _ h => h) ?_
    intro D Db pt ps t s ids et es ft fs hl hts hb hDb hag hnr ht hs
    obtain ⟨o, rfl, rfl, -⟩ := hl
    simp [topLen, hs] at hn
  | succ n ih =>
    intro mt ms hn hR
    refine StepMatch.of_mrel hR (fun _ _ _ _ h => h) ?_
    intro D Db pt ps t s ids et es ft fs hl hts hb hDb hag hnr ht hs
    obtain ⟨o, rfl, rfl, hp, hunread⟩ := hl
    simp only [List.nil_append, List.cons_append] at hnr ht hs
    rcases step_deleted hR.1 hp hunread hts hb hDb hag hnr ht hs with hesc | ⟨ms1, e, hR1, hlen⟩
    · exact ⟨fun _ _ => .inl hesc, fun _ _ => .inl hesc⟩
    · have hlen' : topLen ms1 = n := by simp [topLen, hs] at hn; omega
      refine StepMatch.prepend e ?_ (ih mt ms1 hlen' hR1)
      simp only [Machine.shape, ht, hs]
      exact (shape_cons rfl hb).symm

theorem sim : Simulation (MRel L) := fun mt ms hR => sim_len _ mt ms rfl hR

/-- **Dead code elimination is correct.** Deleting, anywhere in a function, pure ops whose results
no later op in their region reads (at any depth) gives a function that refines the original, for
every argument and every oracle. "Later" is in the target: deleted ops don't count as readers, so
a chain of dead copies can go at once. -/
theorem refines {mod : Module} {tgt src : Func} (hparams : tgt.params = src.params)
    (hrets : tgt.rets = src.rets) (hops : OpsRel L tgt.body.ops src.body.ops)
    (dec : src.Decided mod) : tgt.Refines mod src :=
  Simulation.refines sim (fun _ _ h => by rw [h.1]; exact Events.Refines.refl _)
    (fun oracle world args => ⟨oracle, InitMatch.of_lockstep
      (init_lockstep hparams hrets hops oracle world args) fun _ _ h => h⟩) dec

theorem OpsRel.prefix {L : List Op → List Op → List Op → Prop} {t s : List Op} (h : OpsRel L t s) :
    ∀ pre : List Op, OpsRel L (pre ++ t) (pre ++ s)
  | [] => h
  | o :: pre => .cons (.refl o) (OpsRel.prefix h pre)

/-- **Deleting an unused copy is correct.** In a function whose body is `pre`, then
`%y = copy %x`, then `post`, where no op in `post` reads `%y` at any depth, deleting the copy gives
a function that refines the original. (`refines` covers copies in nested regions, and many at
once.) -/
theorem refines_copy {mod : Module} {tgt src : Func} {pre post : List Op} {x y : String} {T : Ty}
    {facts : List TrustedFact} {loc : Option Loc} (hparams : tgt.params = src.params)
    (hrets : tgt.rets = src.rets) (ht : tgt.body.ops = pre ++ post)
    (hs : src.body.ops = pre ++ CopyProp.copyOp x y T facts loc :: post)
    (hunread : opsReads y post = false) (dec : src.Decided mod) : tgt.Refines mod src := by
  refine refines hparams hrets ?_ dec
  rw [ht, hs]
  refine OpsRel.prefix ?_ pre
  have := OpsRel.rw (L := L) (pt := []) (ps := [CopyProp.copyOp x y T facts loc]) (t := post)
    (s := post) ⟨_, rfl, rfl, copy_pure x y T facts loc, by simpa [CopyProp.copyOp, Op.results]⟩
    (.refl post)
  simpa using this

/-- **Inside a block of `cf.blocks` too.** In a function whose body is `pre`, then a `cf.blocks`
whose first block holds `bpre`, `%y = copy %x`, and `bpost`, then `post`, where no op in `bpost`
reads `%y` at any depth, deleting the copy gives a function that refines the original. Jumps
need nothing special: `refines` covers code at any depth, blocks included. -/
theorem refines_copy_in_block {mod : Module} {tgt src : Func} {pre post bpre bpost : List Op}
    {rest : List Region} {p : Bool} {res : List Result} {ps : List Result} {lbl : Option String}
    {loc cloc : Option Loc} {x y : String} {T : Ty} {facts : List TrustedFact}
    (hparams : tgt.params = src.params) (hrets : tgt.rets = src.rets)
    (ht : tgt.body.ops =
      pre ++ .mk (.blocks p) res [] (.mk ps (bpre ++ bpost) lbl :: rest) loc :: post)
    (hs : src.body.ops = pre ++
      .mk (.blocks p) res []
        (.mk ps (bpre ++ CopyProp.copyOp x y T facts cloc :: bpost) lbl :: rest) loc :: post)
    (hunread : opsReads y bpost = false) (dec : src.Decided mod) : tgt.Refines mod src := by
  refine refines hparams hrets ?_ dec
  rw [ht, hs]
  refine OpsRel.prefix (.cons (.regions (.cons ?_ (RegionsRel.refl _))) (.refl _)) pre
  refine OpsRel.prefix ?_ bpre
  have := OpsRel.rw (L := L) (pt := []) (ps := [CopyProp.copyOp x y T facts cloc]) (t := bpost)
    (s := bpost) ⟨_, rfl, rfl, copy_pure x y T facts cloc, by simpa [CopyProp.copyOp, Op.results]⟩
    (.refl bpost)
  simpa using this

/-! ## Look-alikes that are wrong -/

/-- A copy whose result is read later can't be deleted: the target gets stuck where the source
reads the copy. This is why the rest of the region must not read the results. -/
theorem delete_read_copy_wrong :
    operandIn [.block [] [] ((∅ : Env).insert "x" (.int 8 (.bits 1)))] none (.var "y") ≠
      operandIn [.block [] [] (((∅ : Env).insert "x" (.int 8 (.bits 1))).insert "y"
        (.int 8 (.bits 1)))] none (.var "y") := by
  simp [operandIn, lookup, pure, Except.pure, halt, throw, throwThe, MonadExcept.throw]

end Fir.Dce
