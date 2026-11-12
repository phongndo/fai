import Fir.Dce

/-!
# Which op kinds dead code elimination may delete

`Dce.refines` deletes *pure* ops (`Dce.Pure`): no regions, no call, no stack allocation, not a
terminator, operands that are variables, and a computation that only reads the core and fails
only by UB or getting stuck (`ReadOnly`), for every operand value. Everything in that list but
the computation is a property of the op's kind or syntax; `PureKind` collects the kind's part.

`dcePerm` is the classification the Rust pass uses: `crates/fir/src/generated/contracts.rs` is
generated from it (`lake exe gen-contracts`), so the pass deletes exactly the kinds this file
proves pure. `dcePerm_sound` is the binding: every kind it lets the pass delete is `PureKind`, and
`Pure.of_kind` makes any op of such a kind, with variable operands and no regions, `Pure`. The
classification reads only modifiers, never immediates (`dcePerm_erase`), so a table indexed by
the op names (whose kinds have their immediates reset) covers every kind.

Modifiers decide: an op that may trap (`int.add.s.trap`, a `.trap` division edge,
`union.get.trap`) is kept, because a trap is an observable outcome that a target must
reproduce; one whose bad case is UB (`int.div.s.ub`, `union.get.ub`) or `poison` may go, since UB
in the source lets the target do anything. Kinds whose computation consults the oracle
(`freeze`, `ptr.cmp`), gives an allocation its address (`ptr.addr`, `ptr.with_addr`), creates
something (`func.addr`, allocations), or touches memory or scopes (loads, stores, `ptr.expose`,
`ptr.from_exposed`) are kept. `freeze_changes_core` shows the first of these is a real
obstacle, not a missing proof: the declared effects of `freeze` are empty, yet it changes the
core, so an `effects` declaration is not evidence of purity.
-/

namespace Fir.Dce

/-! ## Modifiers that trap -/

def _root_.Fir.Ovf.traps : Ovf → Bool
  | .trap _ => true
  | _ => false

def _root_.Fir.Edge.traps : Edge → Bool
  | .trap => true
  | _ => false

def _root_.Fir.ShiftEdge.traps : ShiftEdge → Bool
  | .trap => true
  | _ => false

theorem arith_noTrap {ovf : Ovf} (h : ovf.traps = false) (op : ArithOp) (a b : Val w) :
    ∀ r, Sem.arith op ovf a b ≠ .trap r := by
  intro r
  cases a <;> cases b <;> cases ovf <;> simp_all [Ovf.traps, Sem.arith, Sem.arithBits] <;>
    split <;> simp

theorem div_noTrap {zero ovf : Edge} (hz : zero.traps = false) (ho : ovf.traps = false)
    (op : DivOp) (a b : Val w) : ∀ r, Sem.div op zero ovf a b ≠ .trap r := by
  intro r
  unfold Sem.div
  cases zero <;> cases ovf <;> simp only [Edge.traps] at hz ho <;> cases a <;> cases b <;>
    simp [Edge.needsDefined] <;> (repeat split) <;> simp_all <;> split <;> simp

theorem shift_noTrap {edge : ShiftEdge} (h : edge.traps = false) (op : ShiftOp) (a b : Val w) :
    ∀ r, Sem.shift op edge a b ≠ .trap r := by
  intro r
  unfold Sem.shift
  cases edge <;> simp only [ShiftEdge.traps] at h <;> cases a <;> cases b <;>
    simp [ShiftEdge.needsDefined] <;> (repeat split) <;> simp_all

/-! ## Computations that only read the core -/

theorem ReadOnly.fromOut {o : OpOut w} (h : ∀ r, o ≠ .trap r) (loc : Option Loc) :
    ReadOnly (Fir.fromOut loc o) := by
  cases o with
  | ok v => exact ReadOnly.pure' _
  | trap r => exact absurd rfl (h r)
  | ub k => exact ReadOnly.ub' _ _ _

theorem ReadOnly.asInt (loc : Option Loc) (w : Nat) (v : RVal) : ReadOnly (Fir.asInt loc w v) := by
  unfold Fir.asInt
  split
  · split
    · exact ReadOnly.pure' _
    · exact ReadOnly.stuck _ _ _
  · exact ReadOnly.stuck _ _ _

theorem ReadOnly.asPtr (loc : Option Loc) (v : RVal) : ReadOnly (Fir.asPtr loc v) := by
  unfold Fir.asPtr
  split
  · exact ReadOnly.pure' _
  · exact ReadOnly.stuck _ _ _

/-- Take apart a computation built from reads, pure values, UB, getting stuck, and the
non-trapping arithmetic above. -/
syntax "read_only" : tactic
macro_rules
  | `(tactic| read_only) => `(tactic| first
    | contradiction
    | exact ReadOnly.pure' _
    | exact ReadOnly.stuck _ _ _
    | exact ReadOnly.ub' _ _ _
    | exact ReadOnly.asInt _ _ _
    | exact ReadOnly.asPtr _ _
    | exact readOnly_asFloat _ _ _
    | exact ReadOnly.get'
    | exact readOnly_getAlloc _ _
    | exact ReadOnly.fromOut (arith_noTrap (by assumption) _ _ _) _
    | exact ReadOnly.fromOut (div_noTrap (by assumption) (by assumption) _ _ _) _
    | exact ReadOnly.fromOut (shift_noTrap (by assumption) _ _ _) _
    | (refine ReadOnly.bind' ?_ fun _ => ?_ <;> read_only)
    | (refine ReadOnly.ite' ?_ ?_ <;> read_only)
    | (split <;> (try injections) <;> (try subst_vars) <;> read_only)
    | (unfold Fir.offsetBy; read_only)
    | (dsimp only; read_only))

theorem readOnly_offsetBy (loc : Option Loc) (inbounds : Bool) (p : Ptr) (n : Int) :
    ReadOnly (offsetBy loc inbounds p n) := by
  unfold offsetBy; read_only

/-! ## The classification -/

/-- What dead code elimination may do with an op of a kind that nothing reads. -/
inductive DcePerm where
  /-- Delete it: `dcePerm_sound` proves the kind pure. -/
  | delete
  /-- Delete it without a proof, on trust (`why` says why it should be pure). The pass deletes
  such kinds only when its policy allows trusted permissions; the proved checker
  (`Fir.Dce.checkFunc`) never accepts their deletion. No kind is trusted today: the slot is for
  ops whose purity proof is still to come (new dialects), so they can be optimized and reported
  as trusted rather than silently treated as proved. -/
  | trusted (why : String)
  /-- Keep it: it may trap, consult the oracle, allocate, touch memory, call, or end a block, or
  no proof says otherwise. -/
  | keep
  deriving DecidableEq, Repr

/-- The kinds dead code elimination deletes when nothing reads their results. Only modifiers
decide (`dcePerm_erase`); every kind not listed is kept. -/
def dcePerm (k : OpKind) : DcePerm :=
  match k with
  | .const _ | .poison | .copy | .select | .bit _ | .cmp _ | .zext | .sext | .trunc _
  | .ptrNull | .ptrOffset _ | .ptrField _ _ _ | .ptrIndex _ _
  | .tySize _ | .tyAlign _ | .tyOffset _ _ | .memGlobal _
  | .aggMake | .aggExtract _ | .aggInsert _ | .overflow _ _
  | .unionMake _ | .unionTag | .sliceMake | .slicePtr | .sliceLen => .delete
  | .arith _ ovf => if ovf.traps then .keep else .delete
  | .div _ zero ovf => if zero.traps || ovf.traps then .keep else .delete
  | .shift _ edge => if edge.traps then .keep else .delete
  | .unionGet trap _ => if trap then .keep else .delete
  -- The float ops that can't trap (`Dce.floatPure`): all but `float.to_int.*.trap`.
  | _ => if floatPure k then .delete else .keep

/-- The kind's part of `Pure`: no call, no stack allocation, not a terminator, not `va.start`, and a
computation
that only reads the core, for every location, result list, and operand value. -/
def PureKind (k : OpKind) : Prop :=
  k.callee? = none ∧ k.stackAlloc? = none ∧ k.isTerminator = false ∧ k.isVaStart = false ∧
    ∀ loc res vs, ReadOnly (evalSimple loc k res vs)

/-- An op of a pure kind, with no regions and variables as operands, is `Pure`. -/
theorem Pure.of_kind {k : OpKind} {res : List Result} {args : List Operand} {loc : Option Loc}
    (hk : PureKind k) (hargs : ∀ a ∈ args, ∃ n, a = .var n) : Pure (.mk k res args [] loc) :=
  ⟨k, res, args, loc, rfl, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hargs, hk.2.2.2.2 loc res⟩

/-- The float ops that can't trap are pure kinds (from `Dce.readOnly_evalFloat`). -/
theorem floatPure_kind {k : OpKind} (hk : floatPure k = true) : PureKind k := by
  refine ⟨?_, ?_, ?_, ?_, fun loc res vs => ?_⟩
  · cases k <;> simp only [floatPure, reduceCtorEq] at hk <;> rfl
  · cases k <;> simp only [floatPure, reduceCtorEq] at hk <;> rfl
  · cases k <;> simp only [floatPure, reduceCtorEq] at hk <;> rfl
  · cases k <;> simp only [floatPure, reduceCtorEq] at hk <;> rfl
  · rw [evalSimple_float hk]
    exact ReadOnly.bind' ReadOnly.get' fun _ => readOnly_evalFloat loc k res vs hk

set_option maxHeartbeats 4000000 in
/-- **Dead code elimination's classification is sound.** Every kind `dcePerm` lets the pass
delete is pure. (One case per kind, each unfolding `evalSimple`: hence the heartbeats.) -/
theorem dcePerm_sound : ∀ k, dcePerm k = .delete → PureKind k := by
  intro k h
  by_cases hf : floatPure k = true
  · exact floatPure_kind hf
  have hf : floatPure k = false := by simpa using hf
  refine ⟨?_, ?_, ?_, ?_, fun loc res vs => ?_⟩
  · cases k <;> first | rfl | simp [dcePerm, hf] at h
  · cases k <;> first | rfl | simp [dcePerm, hf] at h
  · cases k <;> first | rfl | simp [dcePerm, hf] at h
  · cases k <;> first | rfl | simp [dcePerm, hf] at h
  · cases k <;> simp only [dcePerm, hf, ite_eq_right_iff, Bool.or_eq_true, imp_false, not_or,
      Bool.not_eq_true, reduceCtorEq, Bool.false_eq_true, ite_false] at h <;>
      (try obtain ⟨_, _⟩ := h) <;>
      unfold evalSimple <;> read_only

/-- The classification reads only modifiers: resetting a kind's immediates (as the name table
holds kinds) doesn't change it. So a table indexed by op names covers every kind. -/
theorem dcePerm_erase : ∀ k, dcePerm k.erase = dcePerm k := by
  intro k; cases k <;> rfl

/-! ## A declared effect list is not a proof -/

/-- `freeze` of `poison` consults the oracle, which counts its answers: running it changes the
core. Its declaration lists no effects, so an empty `effects` clause doesn't make an op pure. -/
theorem evalSimple_freeze_poison (loc : Option Loc) (r : Result) (w : Nat) (c : Core) :
    evalSimple loc .freeze [r] [.int w .poison] c =
      .ok ([.int w (.bits (BitVec.ofInt w (c.oracle.next c.choices)))],
        { c with choices := c.choices + 1 }) := rfl

theorem freeze_changes_core (loc : Option Loc) (r : Result) (w : Nat) (c : Core) :
    ¬ ReadOnly (evalSimple loc .freeze [r] [.int w .poison]) := by
  intro h
  rcases h c with ⟨_, e, _⟩ | ⟨_, e⟩ <;> rw [evalSimple_freeze_poison] at e
  · cases e
  · injection e with e
    have := congrArg (fun p => p.2.choices) e
    simp at this

end Fir.Dce
