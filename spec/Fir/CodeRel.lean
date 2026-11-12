import Fir.Sim

/-!
# Running related code in lockstep

Many rewrites change code without changing what the core computes: they delete or replace ops
whose effect is the same. Their proofs share one fact, proved here once. Two machines with the
same core, whose stacks hold the same code except where a rewrite applies, step together: each
step gives the same core again, or halts the same way, until the target reaches a rewritten
spot. A proof about such a rewrite only reasons about the rewritten spot itself.

`OpsRel L` relates target code to source code that is the same except that `L` relates some
target op sequences to source op sequences, at any depth (inside `cf.if` and `cf.loop` regions
and the blocks of `cf.blocks` too). `L` also sees the target ops that follow a rewritten
sequence in its region, so a rewrite can depend on what the rest of the region reads.

## Environments that differ

The two machines' environments need not be equal. `StackRel L D` relates frame stacks that hold
related code and whose block frames' environments agree on every name outside a set of
*hidden* names, which no target code that can still run there reads. `D` is what is hidden at the
top of the stack: it includes what each frame below hides, up to the nearest call frame (lookups
stop there, so a callee starts with nothing hidden). A lookup of a name outside `D` gives the same
answer on both stacks (`StackRel.lookup`), so lockstep steps read the same operands even when the
environments differ.

Rewrites that keep the environments equal (dead stores, forwarding, copy propagation) never hide a
name. Dead code elimination hides the results of deleted ops: the source binds them, the target
doesn't, and nothing the target runs afterwards reads them. mem2reg will add a relation between
the cores' memories, and hidden names that rewritten target code does read (the promoted values),
related to the source's memory rather than its environment.

`MRel L` relates machines with the same core whose stacks are related this way.
-/

namespace Fir

/-! ## Reads -/

/-- Whether an operand reads `%n`. -/
def Operand.reads (n : String) : Operand → Bool
  | .var m => m == n
  | .hole .. => false

mutual
/-- Whether an op reads `%n`: as an operand, or in any op inside its regions, at any depth. -/
def Op.reads (n : String) : Op → Bool
  | .mk _ _ args rs _ => args.any (Operand.reads n) || regionsReads n rs

/-- Whether any op in these regions reads `%n`, at any depth. -/
def regionsReads (n : String) : List Region → Bool
  | [] => false
  | .mk _ ops _ :: rs => opsReads n ops || regionsReads n rs

/-- Whether any op in `ops` reads `%n`, at any depth. -/
def opsReads (n : String) : List Op → Bool
  | [] => false
  | o :: os => o.reads n || opsReads n os
end

/-- No op in `ops` reads a name in `D`, at any depth. -/
def NoReads (D : String → Prop) (ops : List Op) : Prop := ∀ n, D n → opsReads n ops = false

theorem opsReads_append (n : String) : ∀ (a b : List Op),
    opsReads n (a ++ b) = (opsReads n a || opsReads n b)
  | [], _ => by simp [opsReads]
  | o :: a, b => by simp [opsReads, opsReads_append n a b, Bool.or_assoc]

theorem NoReads.cons {D : String → Prop} {o : Op} {t : List Op} (h : NoReads D (o :: t)) :
    (∀ n, D n → o.reads n = false) ∧ NoReads D t := by
  constructor <;> intro n hn <;> have := h n hn <;> simp_all [opsReads]

theorem NoReads.append_right {D : String → Prop} {a b : List Op} (h : NoReads D (a ++ b)) :
    NoReads D b := by
  intro n hn; have := h n hn; simp_all [opsReads_append]

theorem NoReads.append_left {D : String → Prop} {a b : List Op} (h : NoReads D (a ++ b)) :
    NoReads D a := by
  intro n hn; have := h n hn; simp_all [opsReads_append]

/-- An op that reads no name in `D` has operands that read none, and regions that read none. -/
theorem Op.reads_mk {D : String → Prop} {k res args rs loc}
    (h : ∀ n, D n → Op.reads n (.mk k res args rs loc) = false) :
    (∀ n, D n → args.any (Operand.reads n) = false) ∧ ∀ n, D n → regionsReads n rs = false := by
  constructor <;> intro n hn <;> have := h n hn <;> simp_all [Op.reads]

/-! ## Related code -/

mutual
/-- Two ops that are the same, or differ only in their regions' code. -/
inductive OpRel (L : List Op → List Op → List Op → Prop) : Op → Op → Prop
  | refl (o : Op) : OpRel L o o
  | regions {k res args rt rs loc} : RegionsRel L rt rs →
      OpRel L (.mk k res args rt loc) (.mk k res args rs loc)

inductive RegionsRel (L : List Op → List Op → List Op → Prop) : List Region → List Region → Prop
  | nil : RegionsRel L [] []
  | cons {ps ot os lbl rt rs} : OpsRel L ot os → RegionsRel L rt rs →
      RegionsRel L (.mk ps ot lbl :: rt) (.mk ps os lbl :: rs)

/-- Op lists that are the same except where `L` relates a target sequence to a source one. `L`
also sees the target ops after the sequence, up to the end of the region. -/
inductive OpsRel (L : List Op → List Op → List Op → Prop) : List Op → List Op → Prop
  | refl (l : List Op) : OpsRel L l l
  | cons {o o' t s} : OpRel L o o' → OpsRel L t s → OpsRel L (o :: t) (o' :: s)
  | rw {pt ps t s} : L pt ps t → OpsRel L t s → OpsRel L (pt ++ t) (ps ++ s)
end

variable {L : List Op → List Op → List Op → Prop}

theorem RegionsRel.refl : (rs : List Region) → RegionsRel L rs rs
  | [] => .nil
  | .mk _ _ _ :: rs => .cons (.refl _) (RegionsRel.refl rs)

/-- Related block lists have related blocks under each label. -/
theorem RegionsRel.find? (l : String) : ∀ (bt : List Region) {bs : List Region},
    RegionsRel L bt bs →
    (bt.find? (·.label == some l) = none ∧ bs.find? (·.label == some l) = none) ∨
    ∃ b b', bt.find? (·.label == some l) = some b ∧ bs.find? (·.label == some l) = some b' ∧
      RegionsRel L [b] [b'] ∧ b ∈ bt
  | [], _, h => by cases h; exact .inl ⟨rfl, rfl⟩
  | .mk ps ot lbl :: rt, _, h => by
    cases h with
    | cons ho hr =>
    by_cases hl : lbl = some l
    · subst hl
      exact .inr ⟨_, _, by simp only [List.find?_cons, Region.label, beq_self_eq_true],
        by simp only [List.find?_cons, Region.label, beq_self_eq_true], .cons ho .nil,
        List.mem_cons_self⟩
    · have hl' : ∀ ops, ((Region.mk ps ops lbl).label == some l) = false := fun _ => by
        simpa [Region.label] using hl
      rcases RegionsRel.find? l rt hr with ⟨e1, e2⟩ | ⟨b, b', e1, e2, hb, hm⟩
      · exact .inl ⟨by rw [List.find?_cons, hl']; exact e1, by rw [List.find?_cons, hl']; exact e2⟩
      · exact .inr ⟨b, b', by rw [List.find?_cons, hl']; exact e1,
          by rw [List.find?_cons, hl']; exact e2, hb, List.mem_cons_of_mem _ hm⟩

/-- An op in a region of a list reads only what the list reads. -/
theorem opsReads_of_mem {n : String} : ∀ {rs : List Region} {b : Region}, b ∈ rs →
    regionsReads n rs = false → opsReads n b.ops = false
  | .mk _ _ _ :: rs, b, hb, h => by
    simp only [regionsReads, Bool.or_eq_false_iff] at h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.1
    · exact opsReads_of_mem hb h.2

/-- The cases at the head of related code: both at the end, the same op up to regions, or a
rewritten sequence. -/
theorem OpsRel.head {t0 s0 : List Op} (h : OpsRel L t0 s0) :
    (t0 = [] ∧ s0 = []) ∨
    (∃ ot os t s, t0 = ot :: t ∧ s0 = os :: s ∧ OpRel L ot os ∧ OpsRel L t s) ∨
    (∃ pt ps t s, t0 = pt ++ t ∧ s0 = ps ++ s ∧ L pt ps t ∧ OpsRel L t s) := by
  cases h with
  | refl =>
    cases t0 with
    | nil => exact .inl ⟨rfl, rfl⟩
    | cons o l => exact .inr (.inl ⟨o, o, l, l, rfl, rfl, .refl _, .refl _⟩)
  | cons ho hr => exact .inr (.inl ⟨_, _, _, _, rfl, rfl, ho, hr⟩)
  | rw hl hr => exact .inr (.inr ⟨_, _, _, _, rfl, rfl, hl, hr⟩)

/-! ## Related stacks -/

/-- Two environments agree on every name outside `D`. -/
def EnvAgree (D : String → Prop) (et es : Env) : Prop := ∀ n, ¬ D n → et[n]? = es[n]?

theorem EnvAgree.refl (D : String → Prop) (e : Env) : EnvAgree D e e := fun _ _ => rfl

theorem EnvAgree.insert {D : String → Prop} {et es : Env} (h : EnvAgree D et es) (k : String)
    (v : RVal) : EnvAgree D (et.insert k v) (es.insert k v) := by
  intro n hn
  simp only [Std.HashMap.getElem?_insert]
  split
  · rfl
  · exact h n hn

theorem EnvAgree.bindAll {D : String → Prop} : ∀ {et es : Env}, EnvAgree D et es →
    ∀ (rs : List Result) (vs : List RVal), EnvAgree D (et.bindAll rs vs) (es.bindAll rs vs)
  | _, _, h, r :: rs, v :: vs => by
    simp only [Env.bindAll]; exact EnvAgree.bindAll (h.insert r.name v) rs vs
  | _, _, h, [], _ => by simpa [Env.bindAll] using h
  | _, _, h, _ :: _, [] => by simpa [Env.bindAll] using h

theorem EnvAgree.mono {D D' : String → Prop} {et es : Env} (h : EnvAgree D et es)
    (hD : ∀ n, D n → D' n) : EnvAgree D' et es := fun n hn => h n fun h' => hn (hD n h')

/-- Binding names changes only those names. -/
theorem Env.getElem?_bindAll {n : String} : ∀ (env : Env) (rs : List Result) (vs : List RVal),
    (∀ r ∈ rs, r.name ≠ n) → (env.bindAll rs vs)[n]? = env[n]?
  | env, r :: rs, v :: vs, h => by
    simp only [Env.bindAll]
    rw [Env.getElem?_bindAll _ rs vs fun r' hr' => h r' (by simp [hr']),
      Std.HashMap.getElem?_insert]
    simp [h r (by simp)]
  | _, [], _, _ => by simp [Env.bindAll]
  | _, _ :: _, [], _ => by simp [Env.bindAll]

/-- Frame stacks that hold related code, and whose environments agree outside hidden names that
no target code still to run there reads. `D` is the set of names hidden at the top. -/
inductive StackRel (L : List Op → List Op → List Op → Prop) :
    (String → Prop) → List Frame → List Frame → Prop
  | nil {D} : StackRel L D [] []
  | block {D Db t s ids et es ft fs} : StackRel L Db ft fs → (∀ n, Db n → D n) →
      OpsRel L t s → EnvAgree D et es → NoReads D t →
      StackRel L D (.block t ids et :: ft) (.block s ids es :: fs)
  | ifJoin {D rs loc ft fs} : StackRel L D ft fs →
      StackRel L D (.ifJoin rs loc :: ft) (.ifJoin rs loc :: fs)
  | loop {D p bt bs rs loc ft fs} : StackRel L D ft fs → RegionsRel L [bt] [bs] →
      NoReads D bt.ops → StackRel L D (.loop p bt rs loc :: ft) (.loop p bs rs loc :: fs)
  | call {D D' rs rets scopes loc ft fs} : StackRel L D' ft fs →
      StackRel L D (.call rs rets scopes loc :: ft) (.call rs rets scopes loc :: fs)
  | blocks {D p bt bs rs loc ft fs} : StackRel L D ft fs → RegionsRel L bt bs →
      (∀ b ∈ bt, NoReads D b.ops) →
      StackRel L D (.blocks p bt rs loc :: ft) (.blocks p bs rs loc :: fs)

/-- Machines with the same core whose stacks hold related code and related environments. -/
def MRel (L : List Op → List Op → List Op → Prop) (mt ms : Machine) : Prop :=
  mt.core = ms.core ∧ ∃ D, StackRel L D mt.stack ms.stack

/-- Two results of a step: the same halt, or related machines. -/
def Lockstep (L : List Op → List Op → List Op → Prop) (rt rs : Except Halt Machine) : Prop :=
  (∃ h, rt = .error h ∧ rs = .error h) ∨ (∃ mt ms, rt = .ok mt ∧ rs = .ok ms ∧ MRel L mt ms)

theorem Lockstep.halt {h : Halt} : Lockstep L (.error h) (.error h) := .inl ⟨h, rfl, rfl⟩

theorem Lockstep.ok {c : Core} {D : String → Prop} {ft fs : List Frame}
    (h : StackRel L D ft fs) : Lockstep L (.ok ⟨c, ft⟩) (.ok ⟨c, fs⟩) :=
  .inr ⟨_, _, rfl, rfl, rfl, D, h⟩

/-! ## Facts about related stacks -/

namespace StackRel

variable {D : String → Prop} {ft fs : List Frame}

/-- **Lookups of names that aren't hidden agree.** -/
theorem lookup (h : StackRel L D ft fs) {n : String} (hn : ¬ D n) :
    Fir.lookup n ft = Fir.lookup n fs := by
  induction h with
  | nil => rfl
  | block _ hDb _ hag _ ih =>
    simp only [Fir.lookup]
    rw [hag n hn]
    split
    · rfl
    · exact ih fun h => hn (hDb n h)
  | ifJoin _ ih => exact ih hn
  | loop _ _ _ ih => exact ih hn
  | call => rfl
  | blocks _ _ _ ih => exact ih hn

theorem operandIn (h : StackRel L D ft fs) (loc : Option Loc) {a : Operand}
    (ha : ∀ n, D n → a.reads n = false) : Fir.operandIn ft loc a = Fir.operandIn fs loc a := by
  cases a with
  | var n =>
    have hn : ¬ D n := fun hd => by simp [Operand.reads] at ha; exact ha n hd rfl
    simp only [Fir.operandIn, h.lookup hn]
  | hole => rfl

/-- Operands that read no hidden name have the same values. -/
theorem operands (h : StackRel L D ft fs) (loc : Option Loc) :
    ∀ {args : List Operand}, (∀ n, D n → args.any (Operand.reads n) = false) →
      Fir.operands ft loc args = Fir.operands fs loc args
  | [], _ => rfl
  | a :: args, ha => by
    have h1 : ∀ n, D n → a.reads n = false := fun n hn => by have := ha n hn; simp_all
    have h2 : ∀ n, D n → args.any (Operand.reads n) = false := fun n hn => by
      have := ha n hn; simp_all
    have := h.operands loc h2
    simp only [Fir.operands, List.mapM_cons] at this ⊢
    rw [h.operandIn loc h1, this]

theorem tail {f f' : Frame} (h : StackRel L D (f :: ft) (f' :: fs)) : ∃ D', StackRel L D' ft fs := by
  cases h with
  | block h => exact ⟨_, h⟩
  | ifJoin h => exact ⟨_, h⟩
  | loop h => exact ⟨_, h⟩
  | call h => exact ⟨_, h⟩
  | blocks h => exact ⟨_, h⟩

theorem length_eq (h : StackRel L D ft fs) : ft.length = fs.length := by
  induction h <;> simp_all

theorem shape (h : StackRel L D ft fs) :
    ft.map Frame.isProgressLoop = fs.map Frame.isProgressLoop := by
  induction h with
  | @loop _ p _ _ _ _ _ _ _ _ _ ih => cases p <;> simp_all [Frame.isProgressLoop]
  | @blocks _ p _ _ _ _ _ _ _ _ _ ih => cases p <;> simp_all [Frame.isProgressLoop]
  | _ => simp_all [Frame.isProgressLoop]

theorem blockIds (h : StackRel L D ft fs) : Fir.blockIds ft = Fir.blockIds fs := by
  induction h <;> simp_all [Fir.blockIds]

theorem bindTop (h : StackRel L D ft fs) (rs : List Result) (vs : List RVal) :
    StackRel L D (Fir.bindTop rs vs ft) (Fir.bindTop rs vs fs) := by
  cases h with
  | nil => exact .nil
  | block h hDb ho hag hnr => exact .block h hDb ho (hag.bindAll rs vs) hnr
  | ifJoin h => exact .ifJoin h
  | loop h hb hnr => exact .loop h hb hnr
  | call h => exact .call h
  | blocks h hb hnr => exact .blocks h hb hnr

theorem addAllocId (h : StackRel L D ft fs) (id : Nat) :
    StackRel L D (Fir.addAllocId id ft) (Fir.addAllocId id fs) := by
  cases h with
  | nil => exact .nil
  | block h hDb ho hag hnr => exact .block h hDb ho hag hnr
  | ifJoin h => exact .ifJoin h
  | loop h hb hnr => exact .loop h hb hnr
  | call h => exact .call h
  | blocks h hb hnr => exact .blocks h hb hnr

/-- A new block on top, holding related code that reads no hidden name, with the same
environment on both sides. -/
theorem push {t s : List Op} (h : StackRel L D ft fs) (ho : OpsRel L t s) (hnr : NoReads D t)
    (ids : List Nat) (env : Env) : StackRel L D (.block t ids env :: ft) (.block s ids env :: fs) :=
  .block h (fun _ x => x) ho (EnvAgree.refl _ _) hnr

/-- Where `cf.break` and `cf.continue` go: the same loop on both sides, with related frames
below it. -/
theorem splitLoop (h : StackRel L D ft fs) :
    (splitStack pickLoop ft = none ∧ splitStack pickLoop fs = none) ∨
    ∃ at' as' p bt bs rs loc bt' bs' D', splitStack pickLoop ft = some (at', (p, bt, rs, loc), bt') ∧
      splitStack pickLoop fs = some (as', (p, bs, rs, loc), bs') ∧
      Fir.blockIds at' = Fir.blockIds as' ∧
      StackRel L D' (.loop p bt rs loc :: bt') (.loop p bs rs loc :: bs') := by
  induction h with
  | nil => exact .inl ⟨rfl, rfl⟩
  | @block D Db t s ids et es ft fs _ _ _ _ _ ih =>
    simp only [splitStack, pickLoop, Frame.isCall, Bool.false_eq_true, ite_false]
    rcases ih with ⟨e1, e2⟩ | ⟨at', as', p, bt, bs, rs, loc, bt', bs', D', e1, e2, hids, hr⟩
    · exact .inl ⟨by rw [e1]; rfl, by rw [e2]; rfl⟩
    · exact .inr ⟨_, _, p, bt, bs, rs, loc, bt', bs', D', by rw [e1]; rfl, by rw [e2]; rfl,
        by simp [Fir.blockIds, hids], hr⟩
  | ifJoin _ ih =>
    simp only [splitStack, pickLoop, Frame.isCall, Bool.false_eq_true, ite_false]
    rcases ih with ⟨e1, e2⟩ | ⟨at', as', p, bt, bs, rs, loc, bt', bs', D', e1, e2, hids, hr⟩
    · exact .inl ⟨by rw [e1]; rfl, by rw [e2]; rfl⟩
    · exact .inr ⟨_, _, p, bt, bs, rs, loc, bt', bs', D', by rw [e1]; rfl, by rw [e2]; rfl,
        by simp [Fir.blockIds, hids], hr⟩
  | loop h hb hnr _ =>
    exact .inr ⟨[], [], _, _, _, _, _, _, _, _, rfl, rfl, rfl, .loop h hb hnr⟩
  | call => exact .inl ⟨rfl, rfl⟩
  | blocks _ _ _ ih =>
    simp only [splitStack, pickLoop, Frame.isCall, Bool.false_eq_true, ite_false]
    rcases ih with ⟨e1, e2⟩ | ⟨at', as', p, bt, bs, rs, loc, bt', bs', D', e1, e2, hids, hr⟩
    · exact .inl ⟨by rw [e1]; rfl, by rw [e2]; rfl⟩
    · exact .inr ⟨_, _, p, bt, bs, rs, loc, bt', bs', D', by rw [e1]; rfl, by rw [e2]; rfl,
        by simp [Fir.blockIds, hids], hr⟩

/-- Where `func.ret` goes: the same call on both sides, with related frames below it. -/
theorem splitCall (h : StackRel L D ft fs) :
    (splitStack pickCall ft = none ∧ splitStack pickCall fs = none) ∨
    ∃ at' as' x bt' bs' D', splitStack pickCall ft = some (at', x, bt') ∧
      splitStack pickCall fs = some (as', x, bs') ∧
      Fir.blockIds at' = Fir.blockIds as' ∧ StackRel L D' bt' bs' := by
  induction h with
  | nil => exact .inl ⟨rfl, rfl⟩
  | block _ _ _ _ _ ih =>
    simp only [splitStack, pickCall, Frame.isCall, Bool.false_eq_true, ite_false]
    rcases ih with ⟨e1, e2⟩ | ⟨at', as', x, bt', bs', D', e1, e2, hids, hr⟩
    · exact .inl ⟨by rw [e1]; rfl, by rw [e2]; rfl⟩
    · exact .inr ⟨_, _, x, bt', bs', D', by rw [e1]; rfl, by rw [e2]; rfl,
        by simp [Fir.blockIds, hids], hr⟩
  | ifJoin _ ih =>
    simp only [splitStack, pickCall, Frame.isCall, Bool.false_eq_true, ite_false]
    rcases ih with ⟨e1, e2⟩ | ⟨at', as', x, bt', bs', D', e1, e2, hids, hr⟩
    · exact .inl ⟨by rw [e1]; rfl, by rw [e2]; rfl⟩
    · exact .inr ⟨_, _, x, bt', bs', D', by rw [e1]; rfl, by rw [e2]; rfl,
        by simp [Fir.blockIds, hids], hr⟩
  | loop _ _ _ ih =>
    simp only [splitStack, pickCall, Frame.isCall, Bool.false_eq_true, ite_false]
    rcases ih with ⟨e1, e2⟩ | ⟨at', as', x, bt', bs', D', e1, e2, hids, hr⟩
    · exact .inl ⟨by rw [e1]; rfl, by rw [e2]; rfl⟩
    · exact .inr ⟨_, _, x, bt', bs', D', by rw [e1]; rfl, by rw [e2]; rfl,
        by simp [Fir.blockIds, hids], hr⟩
  | call h => exact .inr ⟨[], [], _, _, _, _, rfl, rfl, rfl, h⟩
  | blocks _ _ _ ih =>
    simp only [splitStack, pickCall, Frame.isCall, Bool.false_eq_true, ite_false]
    rcases ih with ⟨e1, e2⟩ | ⟨at', as', x, bt', bs', D', e1, e2, hids, hr⟩
    · exact .inl ⟨by rw [e1]; rfl, by rw [e2]; rfl⟩
    · exact .inr ⟨_, _, x, bt', bs', D', by rw [e1]; rfl, by rw [e2]; rfl,
        by simp [Fir.blockIds, hids], hr⟩

/-- Where a jump goes: the same `cf.blocks` on both sides, with related frames below it. -/
theorem splitBlocks (h : StackRel L D ft fs) :
    (splitStack pickBlocks ft = none ∧ splitStack pickBlocks fs = none) ∨
    ∃ at' as' p bt bs rs loc bt' bs' D',
      splitStack pickBlocks ft = some (at', (p, bt, rs, loc), bt') ∧
      splitStack pickBlocks fs = some (as', (p, bs, rs, loc), bs') ∧
      Fir.blockIds at' = Fir.blockIds as' ∧
      StackRel L D' (.blocks p bt rs loc :: bt') (.blocks p bs rs loc :: bs') := by
  induction h with
  | nil => exact .inl ⟨rfl, rfl⟩
  | block _ _ _ _ _ ih =>
    simp only [splitStack, pickBlocks, Frame.isCall, Bool.false_eq_true, ite_false]
    rcases ih with ⟨e1, e2⟩ | ⟨at', as', p, bt, bs, rs, loc, bt', bs', D', e1, e2, hids, hr⟩
    · exact .inl ⟨by rw [e1]; rfl, by rw [e2]; rfl⟩
    · exact .inr ⟨_, _, p, bt, bs, rs, loc, bt', bs', D', by rw [e1]; rfl, by rw [e2]; rfl,
        by simp [Fir.blockIds, hids], hr⟩
  | ifJoin _ ih =>
    simp only [splitStack, pickBlocks, Frame.isCall, Bool.false_eq_true, ite_false]
    rcases ih with ⟨e1, e2⟩ | ⟨at', as', p, bt, bs, rs, loc, bt', bs', D', e1, e2, hids, hr⟩
    · exact .inl ⟨by rw [e1]; rfl, by rw [e2]; rfl⟩
    · exact .inr ⟨_, _, p, bt, bs, rs, loc, bt', bs', D', by rw [e1]; rfl, by rw [e2]; rfl,
        by simp [Fir.blockIds, hids], hr⟩
  | loop _ _ _ ih =>
    simp only [splitStack, pickBlocks, Frame.isCall, Bool.false_eq_true, ite_false]
    rcases ih with ⟨e1, e2⟩ | ⟨at', as', p, bt, bs, rs, loc, bt', bs', D', e1, e2, hids, hr⟩
    · exact .inl ⟨by rw [e1]; rfl, by rw [e2]; rfl⟩
    · exact .inr ⟨_, _, p, bt, bs, rs, loc, bt', bs', D', by rw [e1]; rfl, by rw [e2]; rfl,
        by simp [Fir.blockIds, hids], hr⟩
  | call => exact .inl ⟨rfl, rfl⟩
  | blocks h hb hnr _ =>
    exact .inr ⟨[], [], _, _, _, _, _, _, _, _, rfl, rfl, rfl, .blocks h hb hnr⟩

end StackRel

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

/-- Running the same `Except` computation, then continuing on related machines. -/
theorem lockstep_bind {x : Except Halt α} {kt ks : α → Except Halt Machine}
    (hk : ∀ a, Lockstep L (kt a) (ks a)) : Lockstep L (x >>= kt) (x >>= ks) := by
  cases x with
  | error h => exact .halt
  | ok a => exact hk a

theorem bindResults_eq {c : Core} {D : String → Prop} {ft fs : List Frame}
    (h : StackRel L D ft fs) (loc : Option Loc) (rs : List Result) (vs : List RVal) :
    Lockstep L (Machine.bindResults ⟨c, ft⟩ loc rs vs) (Machine.bindResults ⟨c, fs⟩ loc rs vs) := by
  unfold Machine.bindResults
  refine lockstep_exec rfl fun _ core => ?_
  exact Lockstep.ok (h.bindTop rs vs)

theorem enterBody_eq {c : Core} {D : String → Prop} {ft fs : List Frame}
    (h : StackRel L D ft fs) (loc : Option Loc) {bt bs : Region} (hb : RegionsRel L [bt] [bs])
    (hnr : NoReads D bt.ops) (vs : List RVal) :
    Lockstep L (enterBody ⟨c, ft⟩ loc bt vs) (enterBody ⟨c, fs⟩ loc bs vs) := by
  cases hb with
  | cons hops _ =>
    unfold enterBody
    refine lockstep_exec rfl fun _ core => ?_
    exact Lockstep.ok (h.push hops hnr _ _)

/-- A jump from related stacks: to related blocks of the same `cf.blocks`. -/
theorem jump_eq {c : Core} {D : String → Prop} {ft fs : List Frame} (h : StackRel L D ft fs)
    (loc : Option Loc) (s : Succ) (vs : List RVal) :
    Lockstep L (jump ⟨c, ft⟩ loc s vs) (jump ⟨c, fs⟩ loc s vs) := by
  unfold jump
  rcases h.splitBlocks with ⟨e1, e2⟩ |
    ⟨at', as', p, bt, bs, rs, loc', bt', bs', D', e1, e2, hids, hr⟩
  · simp only [e1, e2]; exact .halt
  · simp only [e1, e2, hids]
    cases hr with
    | blocks h0 hb hnr =>
      rcases RegionsRel.find? s.label _ hb with ⟨f1, f2⟩ | ⟨b, b', f1, f2, hbb, hm⟩
      · simp only [f1, f2]; exact .halt
      · simp only [f1, f2]
        refine lockstep_exec rfl fun _ core => ?_
        exact enterBody_eq (.blocks h0 hb hnr) loc hbb (hnr b hm) vs

/-! ## Control flow -/

theorem terminate_eq {c : Core} {D : String → Prop} {ft fs : List Frame} (h : StackRel L D ft fs)
    (loc : Option Loc) (k : OpKind) (vs : List RVal) :
    Lockstep L (terminate ⟨c, ft⟩ loc k vs) (terminate ⟨c, fs⟩ loc k vs) := by
  cases k
  case yield =>
    unfold terminate
    cases h with
    | ifJoin h => exact bindResults_eq h _ _ _
    | blocks h => exact bindResults_eq h _ _ _
    | nil => exact .halt
    | block => exact .halt
    | loop => exact .halt
    | call => exact .halt
  case brk =>
    unfold terminate
    rcases h.splitLoop with ⟨e1, e2⟩ | ⟨at', as', p, bt, bs, rs, loc', bt', bs', D', e1, e2, hids, hr⟩
    · simp only [e1, e2]; exact .halt
    · simp only [e1, e2, hids]
      refine lockstep_exec rfl fun _ core => ?_
      obtain ⟨_, hr⟩ := hr.tail
      exact bindResults_eq hr _ _ _
  case cont =>
    unfold terminate
    rcases h.splitLoop with ⟨e1, e2⟩ | ⟨at', as', p, bt, bs, rs, loc', bt', bs', D', e1, e2, hids, hr⟩
    · simp only [e1, e2]; exact .halt
    · simp only [e1, e2, hids]
      refine lockstep_exec rfl fun _ core => ?_
      cases hr with
      | loop h0 hb hnr => exact enterBody_eq (.loop h0 hb hnr) loc hb hnr vs
  case ret =>
    unfold terminate
    rcases h.splitCall with ⟨e1, e2⟩ | ⟨at', as', x, bt', bs', D', e1, e2, hids, hr⟩
    · simp only [e1, e2]; exact .halt
    · obtain ⟨rs, rets, scopes, loc'⟩ := x
      simp only [e1, e2, hids]
      split
      · exact .halt
      · refine lockstep_exec rfl fun _ core => ?_
        simp only [List.isEmpty_iff_length_eq_zero, hr.length_eq]
        split
        · exact .halt
        · exact bindResults_eq hr _ _ _
  case br => exact jump_eq h loc _ vs
  case condBr t f =>
    simp only [terminate]
    refine lockstep_exec rfl fun x core => ?_
    cases x with
    | poison => exact .halt
    | bits b =>
      by_cases hb : b = 1
      · simp only [hb, ite_true]; exact jump_eq h loc _ _
      · simp only [hb, ite_false]; exact jump_eq h loc _ _
  case switch d cs =>
    simp only [terminate]
    split
    · exact jump_eq h loc _ _
    · exact .halt
    · exact .halt
  all_goals exact .halt

/-- An op without regions, with the current block (the op removed) on top of related stacks. -/
theorem execFlat_eq {c : Core} {D : String → Prop} {ft fs : List Frame} (h : StackRel L D ft fs)
    (kind : OpKind) (results : List Result) {args : List Operand}
    (hargs : ∀ n, D n → args.any (Operand.reads n) = false) (loc : Option Loc) :
    Lockstep L (execFlat ⟨c, ft⟩ kind results args loc) (execFlat ⟨c, fs⟩ kind results args loc) := by
  unfold execFlat
  cases kind.callee? with
  | some callee =>
    simp only [h.operands loc hargs]
    refine lockstep_bind fun vs => ?_
    cases c.funcs[callee]? with
    | none => exact .halt
    | some f =>
      refine lockstep_exec rfl fun _ core => ?_
      exact Lockstep.ok ((StackRel.call (D := fun _ => False) h).push (.refl _) (fun _ x => x.elim) _ _)
  | none =>
  cases kind.stackAlloc? with
  | some sa =>
    refine lockstep_exec rfl fun _ core => ?_
    exact Lockstep.ok ((h.addAllocId _).bindTop _ _)
  | none =>
  simp only
  split
  · simp only [h.operands loc hargs]
    refine lockstep_bind fun vs => ?_
    cases h with
    | nil => exact terminate_eq (D := D) .nil loc kind vs
    | block h' =>
      simp only [blockIds, List.append_nil]
      refine lockstep_exec rfl fun _ core => ?_
      exact terminate_eq h' loc kind vs
    | ifJoin h' =>
      refine lockstep_exec rfl fun _ core => ?_
      exact terminate_eq h' loc kind vs
    | loop h' =>
      refine lockstep_exec rfl fun _ core => ?_
      exact terminate_eq h' loc kind vs
    | call h' =>
      refine lockstep_exec rfl fun _ core => ?_
      exact terminate_eq h' loc kind vs
    | blocks h' =>
      refine lockstep_exec rfl fun _ core => ?_
      exact terminate_eq h' loc kind vs
  · simp only [h.operands loc hargs]
    refine lockstep_bind fun vs => ?_
    refine lockstep_exec rfl fun _ core => ?_
    exact Lockstep.ok (h.bindTop _ _)

/-- An op, with the current block (the op removed) on top of related stacks. -/
theorem execOp_eq {c : Core} {D : String → Prop} {ft fs : List Frame} (h : StackRel L D ft fs)
    {ot os : Op} (ho : OpRel L ot os) (hr : ∀ n, D n → ot.reads n = false) :
    Lockstep L (execOp ⟨c, ft⟩ ot) (execOp ⟨c, fs⟩ os) := by
  obtain ⟨k, res, args, rt, rs, loc, hreg, rfl, rfl⟩ :
      ∃ k res args rt rs loc, RegionsRel L rt rs ∧ ot = .mk k res args rt loc ∧
        os = .mk k res args rs loc := by
    cases ho with
    | refl => cases ot; exact ⟨_, _, _, _, _, _, RegionsRel.refl _, rfl, rfl⟩
    | regions h => exact ⟨_, _, _, _, _, _, h, rfl, rfl⟩
  obtain ⟨hargs, hregs⟩ := Op.reads_mk hr
  cases hk : k.blocksProgress? with
  | some p =>
    cases hreg with
    | nil => simp only [execOp]; exact execFlat_eq h k res hargs loc
    | cons hops hrest =>
      simp only [execOp, hk]
      have hnr : ∀ b ∈ (Region.mk _ _ _ :: _), NoReads D b.ops :=
        fun b hb n hn => opsReads_of_mem hb (hregs n hn)
      exact enterBody_eq (.blocks h (.cons hops hrest) hnr) loc (.cons hops .nil)
        (hnr _ List.mem_cons_self) []
  | none =>
  rcases hreg with _ | ⟨hops1, _ | ⟨hops2, _ | ⟨hops3, hrest⟩⟩⟩
  · exact execFlat_eq h k res hargs loc
  · simp only [execOp, hk]
    cases k.loopProgress? with
    | none => exact .halt
    | some p =>
      simp only [h.operands loc hargs]
      refine lockstep_bind fun vs => ?_
      refine enterBody_eq (.loop h (.cons hops1 .nil) ?_) loc (.cons hops1 .nil) ?_ vs <;>
      · intro n hn; have := hregs n hn; simp_all [regionsReads, Region.ops]
  · simp only [execOp, hk]
    split
    · simp only [h.operands loc hargs]
      refine lockstep_bind fun vs => ?_
      refine lockstep_exec rfl fun x core => ?_
      cases x with
      | poison => exact .halt
      | bits b =>
        have hj := StackRel.ifJoin (rs := res) (loc := loc) h
        by_cases hb : b = 1
        · simp only [hb, ite_true]
          refine Lockstep.ok (hj.push hops1 (fun n hn => ?_) _ _)
          have := hregs n hn; simp_all [regionsReads]
        · simp only [hb, ite_false]
          refine Lockstep.ok (hj.push hops2 (fun n hn => ?_) _ _)
          have := hregs n hn; simp_all [regionsReads]
    · exact .halt
  · simp only [execOp, hk]; exact .halt

/-- The step from related machines whose top blocks are not at a rewritten sequence. -/
theorem step_eq {c : Core} {D Db : String → Prop} {t0 s0 : List Op} {ids : List Nat}
    {et es : Env} {ft fs : List Frame} (h : StackRel L Db ft fs) (hDb : ∀ n, Db n → D n)
    (hag : EnvAgree D et es) (hnr : NoReads D t0)
    (hhead : (t0 = [] ∧ s0 = []) ∨
      (∃ ot os t s, t0 = ot :: t ∧ s0 = os :: s ∧ OpRel L ot os ∧ OpsRel L t s)) :
    Lockstep L (step ⟨c, .block t0 ids et :: ft⟩) (step ⟨c, .block s0 ids es :: fs⟩) := by
  rcases hhead with ⟨rfl, rfl⟩ | ⟨ot, os, t, s, rfl, rfl, ho, hts⟩
  · simp only [step]
    refine lockstep_exec rfl fun _ core => ?_
    exact terminate_eq h none .yield []
  · simp only [step]
    obtain ⟨hr, hnr'⟩ := hnr.cons
    exact execOp_eq (.block h hDb hts hag hnr') ho hr

/-! ## Simulation steps -/

theorem shape_cons {f f' : Frame} {D : String → Prop} {rt rs : List Frame}
    (h : f.isProgressLoop = f'.isProgressLoop) (hrest : StackRel L D rt rs) :
    (f :: rt).map Frame.isProgressLoop = (f' :: rs).map Frame.isProgressLoop := by
  simp [h, hrest.shape]

/-- A lockstep step is a simulation step, for machines whose stacks agree on `progress` loops. -/
theorem StepMatch.of_lockstep {mt ms : Machine} (hshape : ms.shape = mt.shape)
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

/-- A step from related machines. The machines step in lockstep, unless the target's top block
starts a rewritten sequence: `site` handles that case, which is all a rewrite's proof has to do.
`lift` turns the lockstep relation into the proof's own. -/
theorem StepMatch.of_mrel {R : Machine → Machine → Prop} {mt ms : Machine} (hR : MRel L mt ms)
    (lift : ∀ mt' k ms', runSteps (k + 1) ms = .ok ms' → MRel L mt' ms' → R mt' ms')
    (site : ∀ D Db pt ps t s ids et es ft fs, L pt ps t → OpsRel L t s → StackRel L Db ft fs →
      (∀ n, Db n → D n) → EnvAgree D et es → NoReads D (pt ++ t) →
      mt.stack = .block (pt ++ t) ids et :: ft → ms.stack = .block (ps ++ s) ids es :: fs →
      StepMatch R mt ms) :
    StepMatch R mt ms := by
  obtain ⟨hc, D, h⟩ := hR
  obtain ⟨ct, stt⟩ := mt
  obtain ⟨cs, sts⟩ := ms
  dsimp only at hc h
  subst hc
  have hshape : (Machine.mk ct sts).shape = (Machine.mk ct stt).shape := h.shape.symm
  cases h with
  | @block D Db t0 s0 ids et es ft fs hb hDb ho hag hnr =>
    rcases ho.head with hh | hh | ⟨pt, ps, t, s, rfl, rfl, hl, hts⟩
    · exact (StepMatch.of_lockstep hshape (step_eq hb hDb hag hnr (.inl hh))).mono lift
    · exact (StepMatch.of_lockstep hshape (step_eq hb hDb hag hnr (.inr hh))).mono lift
    · exact site D Db pt ps t s ids et es ft fs hl hts hb hDb hag hnr rfl rfl
  | nil => exact (StepMatch.of_lockstep hshape .halt).mono lift
  | ifJoin => exact (StepMatch.of_lockstep hshape .halt).mono lift
  | loop => exact (StepMatch.of_lockstep hshape .halt).mono lift
  | call => exact (StepMatch.of_lockstep hshape .halt).mono lift
  | blocks => exact (StepMatch.of_lockstep hshape .halt).mono lift

/-- A source step that the target doesn't take, before a step match: the source runs one step
ahead of the target. -/
theorem StepMatch.prepend {R : Machine → Machine → Prop} {mt ms ms1 : Machine}
    (e : step ms = .ok ms1) (hshape : ms.shape = mt.shape) (h : StepMatch R mt ms1) :
    StepMatch R mt ms := by
  have run1 : runSteps 1 ms = .ok ms1 := by rw [runSteps_one, e]
  constructor
  · intro mt' et
    rcases h.1 mt' et with hesc | ⟨k, ms', ek, hR, hsh⟩
    · exact .inl (hesc.back run1)
    · refine .inr ⟨k + 1, ms', ?_, hR, fun j mj hj ej => ?_⟩
      · rw [show k + 1 + 1 = 1 + (k + 1) by omega, runSteps_add, run1, Except.ok_bind]; exact ek
      cases j with
      | zero => simp only [runSteps, Except.ok.injEq] at ej; subst ej; exact hshape
      | succ j =>
        rw [show j + 1 = 1 + j by omega, runSteps_add, run1, Except.ok_bind] at ej
        exact hsh j mj (by omega) ej
  · intro ht et
    rcases h.2 ht et with hesc | ⟨j, hs, ej, href⟩
    · exact .inl (hesc.back run1)
    · exact .inr ⟨1 + j, hs, by rw [runSteps_add, run1, Except.ok_bind]; exact ej, href⟩

/-- One target step matched by one source step that runs the same core computation, from tops of
the stack that differ only in code. -/
theorem step_same {R : Machine → Machine → Prop} {mt ms : Machine} {x : Except Halt (α × Core)}
    {ft fs : α → Core → Machine}
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

/-- An op without regions that is not a call, stack allocation, or terminator: evaluate its
operands, compute on the core, bind its results in the current block. -/
theorem execOp_simple (m : Machine) (k : OpKind) (res : List Result) (args : List Operand)
    (loc : Option Loc) (h1 : k.callee? = none) (h2 : k.stackAlloc? = none)
    (h3 : k.isTerminator = false) :
    execOp m (.mk k res args [] loc) =
      (operands m.stack loc args).bind fun vs =>
      (simpleOp loc k res vs m.core).bind fun p =>
      .ok { core := p.2, stack := bindTop res p.1 m.stack } := by
  simp only [execOp, execFlat, h1, h2, h3, Machine.exec, StateT.run, Bool.false_eq_true, ite_false]
  cases operands m.stack loc args with
  | error h => rfl
  | ok vs =>
    simp only [bind, Except.bind]
    cases simpleOp loc k res vs m.core with
    | error h => rfl
    | ok r => rfl

/-! ## Stepping simple ops -/

theorem Except.bind_congr {x : Except ε α} {f g : α → Except ε β} (h : ∀ a, x = .ok a → f a = g a) :
    x.bind f = x.bind g := by
  cases x with
  | error => rfl
  | ok a => exact h a rfl

/-- Binding no results changes nothing. -/
theorem bindTop_nil (vs : List RVal) : ∀ fs : List Frame, bindTop [] vs fs = fs
  | [] => rfl
  | .block _ _ _ :: _ => by simp [bindTop, Env.bindAll]
  | .ifJoin .. :: _ => rfl
  | .loop .. :: _ => rfl
  | .call .. :: _ => rfl
  | .blocks .. :: _ => rfl

/-- Lookups don't depend on the code left in a block. -/
theorem lookup_ops (n : String) (o o' : List Op) (ids : List Nat) (env : Env) (fs : List Frame) :
    lookup n (.block o ids env :: fs) = lookup n (.block o' ids env :: fs) := rfl

theorem operandIn_ops (o o' : List Op) (ids : List Nat) (env : Env) (fs : List Frame)
    (loc : Option Loc) (a : Operand) :
    operandIn (.block o ids env :: fs) loc a = operandIn (.block o' ids env :: fs) loc a := by
  cases a <;> rfl

theorem operands_ops (o o' : List Op) (ids : List Nat) (env : Env) (fs : List Frame)
    (loc : Option Loc) (args : List Operand) :
    operands (.block o ids env :: fs) loc args = operands (.block o' ids env :: fs) loc args := by
  simp only [operands]
  congr 1

/-- A value an operand has doesn't depend on where the op is. -/
theorem operandIn_loc {fs : List Frame} {loc loc' : Option Loc} {a : Operand} {v : RVal}
    (e : operandIn fs loc a = .ok v) : operandIn fs loc' a = .ok v := by
  cases a with
  | var x =>
    simp only [operandIn] at e ⊢
    split at e
    · exact e
    · cases e
  | hole => cases e

/-- Reading an undefined variable gets stuck. -/
theorem operandIn_var_error {fs : List Frame} {loc : Option Loc} {x : String} {h : Halt}
    (e : operandIn fs loc (.var x) = .error h) : h.behavior.Absorbing := by
  simp only [operandIn] at e
  split at e
  · cases e
  · cases e; trivial

theorem operands_one (fs : List Frame) (loc : Option Loc) (a : Operand) :
    operands fs loc [a] = (operandIn fs loc a).bind fun va => .ok [va] := by
  simp only [operands, List.mapM_cons, List.mapM_nil]
  cases operandIn fs loc a <;> rfl

theorem operands_pair (fs : List Frame) (loc : Option Loc) (a b : Operand) :
    operands fs loc [a, b] =
      (operandIn fs loc a).bind fun va => (operandIn fs loc b).bind fun vb => .ok [va, vb] := by
  simp only [operands, List.mapM_cons, List.mapM_nil]
  cases operandIn fs loc a <;> cases operandIn fs loc b <;> rfl

/-- The step that runs a simple op: evaluate its operands on the stack, compute on the core,
bind its results in the current block. -/
theorem step_simple {c : Core} {k : OpKind} {res : List Result} {args : List Operand}
    {loc : Option Loc} {t : List Op} {ids : List Nat} {env : Env} {fs : List Frame}
    (h1 : k.callee? = none) (h2 : k.stackAlloc? = none) (h3 : k.isTerminator = false) :
    step ⟨c, .block (.mk k res args [] loc :: t) ids env :: fs⟩ =
      ((operands (.block t ids env :: fs) loc args).bind fun vs => simpleOp loc k res vs c).bind
        fun p => .ok ⟨p.2, bindTop res p.1 (.block t ids env :: fs)⟩ := by
  simp only [step, execOp_simple _ k res args loc h1 h2 h3]
  cases operands (.block t ids env :: fs) loc args <;> rfl

/-! ## Starting a call -/

/-- Calls of functions with the same parameters and return types, and related bodies, start in
lockstep. -/
theorem init_lockstep {mod : Module} {tgt src : Func} (hparams : tgt.params = src.params)
    (hrets : tgt.rets = src.rets) (hops : OpsRel L tgt.body.ops src.body.ops)
    (oracle : Nat → Int) (args : List RVal) :
    Lockstep L (Machine.init oracle mod tgt args) (Machine.init oracle mod src args) := by
  simp only [Machine.init, hparams, hrets, bind, Except.bind]
  cases (enterCall none src.params args).run (Core.initial oracle mod) with
  | error h => exact .halt
  | ok r =>
    exact Lockstep.ok ((StackRel.call (D := fun _ => False) (D' := fun _ => False) .nil).push hops
      (fun _ x => x.elim) _ _)

/-- Calls that start in lockstep match, for any relation that holds of lockstep machines. -/
theorem InitMatch.of_lockstep {R : Machine → Machine → Prop} {it is : Except Halt Machine}
    (h : Lockstep L it is) (lift : ∀ mt ms, MRel L mt ms → R mt ms) : InitMatch R it is := by
  rcases h with ⟨h, rfl, rfl⟩ | ⟨mt, ms, rfl, rfl, hR⟩
  · by_cases hamb : h.behavior = .ambiguous
    · exact .inl ⟨h, rfl, .inr hamb⟩
    · exact .inr (.inr ⟨h, h, rfl, rfl, Behavior.Refines.refl _ hamb⟩)
  · exact .inr (.inl ⟨mt, ms, rfl, rfl, lift mt ms hR⟩)

end Fir
