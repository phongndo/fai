import Fir.Dse
import Fir.Space

/-!
# Store-to-load forwarding

A load right after a store of the same type through the same pointer reads back the stored value,
so it can be replaced by a copy of that value:

```
mem.store T %x, %p, align A1
%y: T = mem.load %p, align A2        // becomes  %y: T = copy %x
```

`Fwd.refines` proves the rewrite correct at any number of places in a function, at any depth.
The store runs on both sides, so the two machines stay in lockstep with equal cores; the only
new fact is `load_after_store`: right after the store, the load either fails (a misaligned load
is UB) or does exactly what the copy does. The load records nothing new in the `noalias` scopes
(the store already recorded a write to the same bytes), exposes nothing (the bytes it reads are
the stored value's own), and decodes the bytes back to the stored value, provenance included.

Two conditions make the decoding exact. Integer widths must be whole bytes (`Exact`;
`forward_partial_byte_wrong` shows why), and pointers must take at least one byte, which holds
for the whole run once it holds for the module (`Fir.Space`).

Copies are left for copy propagation to remove, so each rewrite stays one local step.
-/

namespace Fir.Fwd

open Dse (Escape)

/-! ## Unfolding ops -/

theorem simpleOp_one (loc : Option Loc) (k : OpKind) (rs : List Result) (o : Operand) (c : Core) :
    simpleOp loc k rs [o] c =
      (operandIn c.env loc o).bind fun x =>
      (evalSimple loc k rs [x] c).bind fun p => bindResults loc rs p.1 p.2 := by
  simp only [simpleOp, List.mapM_cons, List.mapM_nil, bind, StateT.bind, pure, StateT.pure,
    Except.bind, evalOperand]
  cases operandIn c.env loc o with
  | error h => rfl
  | ok x =>
    simp only [Except.map, Except.pure]

theorem evalSimple_copy (loc : Option Loc) (r : Result) (x : RVal) (c : Core) :
    evalSimple loc .copy [r] [x] c = .ok ([x], c) := rfl

theorem evalSimple_load (loc : Option Loc) (A : Nat) (r : Result) (p : Option Ptr) (c : Core) :
    evalSimple loc (.load A) [r] [.ptr p] c =
      (loadC loc r.ty A p c).bind fun q => .ok ([q.1], q.2) := by
  simp only [evalSimple, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, Except.bind, asPtr, Except.pure]

theorem loadC_some (loc : Option Loc) (T : Ty) (A : Nat) (p : Ptr) (c : Core) :
    loadC loc T A (some p) c =
      (access loc p (T.size c.space) A false c).bind fun q =>
      decodeAs loc T (readBytes (q.2.mem.getD q.1.1 ∅) q.1.2 (T.size c.space)) q.2 := by
  simp only [loadC, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    Except.bind, Except.pure]

theorem access_eq (loc : Option Loc) (p : Ptr) (n A : Nat) (w : Bool) (c : Core) :
    access loc p n A w c =
      (checkAccess c loc p n A).bind fun r =>
      (markAll c.tags loc r.1 r.2.1 r.2.2 n w c.scopes.toList c.marks).bind fun marks =>
      .ok ((r.1, r.2.2), { c with marks }) := by
  simp only [access, bind, Except.bind, pure, Except.pure]

/-- Writing memory doesn't change where an access goes. -/
theorem checkAccess_written (c : Core) (M : Std.ExtTreeMap Nat Marks) (a off : Nat)
    (bs : List Byte) (loc : Option Loc) (p : Ptr) (n A : Nat) :
    checkAccess (Dse.written c M a off bs) loc p n A = checkAccess c loc p n A := rfl


/-! ## Reading after a write -/

theorem markByte_read (d w : Bool) (mk : Mark) :
    markByte d false (markByte d w mk) = markByte d w mk := by
  obtain ⟨x, y, z⟩ := mk
  cases d <;> cases w <;> cases x <;> cases y <;> cases z <;> rfl

theorem markScope_read (d w : Bool) (ms : Marks) (off n : Nat) :
    markScope d false (markScope d w ms off n) off n = markScope d w ms off n := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [Dse.getElem?_markScope]
  split
  · rename_i hk
    simp only [Std.ExtTreeMap.getD_eq_getD_getElem?, Dse.getElem?_markScope, hk, and_self,
      ite_true, Option.getD_some, markByte_read]
  · rfl

theorem firstBad_read (d w : Bool) (ms : Marks) (off n : Nat) :
    firstBad d false (markScope d w ms off n) off n = firstBad d w ms off n := by
  unfold firstBad
  apply Dse.find?_congr
  intro i hi
  rw [List.mem_range] at hi
  rw [Dse.getD_markScope d w ms off n i hi, markByte_read]

/-- Reading bytes just written through the same pointer records nothing new in the scopes. -/
theorem markAll_read {tags : Std.ExtTreeMap Nat (Option Nat)} {loc : Option Loc}
    (loc' : Option Loc) {a t off n : Nat} :
    ∀ {L : List (Nat × Scope)} {mm mm' : Std.ExtTreeMap Nat Marks},
      markAll tags loc a t off n true L mm = .ok mm' → (L.map (·.1)).Nodup →
      markAll tags loc' a t off n false L mm' = .ok mm'
  | [], _, _, e, _ => by cases e; rfl
  | (id, s) :: rest, mm, mm', e, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [markAll] at e ⊢
    split at e
    · rw [ite_eq_left (by assumption)]; exact markAll_read loc' e hnd.2
    · rw [ite_eq_right (by assumption)]
      split at e
      · cases e
      · rw [ite_eq_right (by simp)]
        split at e
        · rw [ite_eq_left (by assumption)]; exact markAll_read loc' e hnd.2
        · rw [ite_eq_right (by assumption)]
          split at e
          · cases e
          · rename_i hb
            have hid := Dse.markAll_other e hnd.1
            rw [Std.ExtTreeMap.getElem?_insert_self] at hid
            have hget : mm'.getD id ∅ =
                markScope (isDerived tags s.tag t) true (mm.getD id ∅) off n := by
              rw [Std.ExtTreeMap.getD_eq_getD_getElem?, hid]; rfl
            simp only [hget, firstBad_read, hb, markScope_read]
            rw [Dse.insert_self hid]
            exact markAll_read loc' e hnd.2

/-! ## Decoding what was encoded -/

/-- Types whose values come back unchanged from memory. Integer widths must be whole bytes. -/
def Exact : Ty → Prop
  | .int w => w % 8 = 0 ∧ 0 < w
  | _ => True

theorem mapM_fragToBits (loc : Option Loc) :
    ∀ (bs : List Byte), (∀ b ∈ bs, ∀ p i, b ≠ .frag p i) → ∀ c : Core,
      bs.mapM (fragToBits loc) c = .ok (bs, c)
  | [], _, _ => rfl
  | b :: bs, h, c => by
    have hb : fragToBits loc b c = .ok (b, c) := by
      cases b with
      | frag p i => exact absurd rfl (h _ (by simp) p i)
      | _ => rfl
    have ih := mapM_fragToBits loc bs (fun b hb => h b (by simp [hb])) c
    simp only [List.mapM_cons, bind, StateT.bind, hb, ih, pure, StateT.pure, Except.bind,
      Except.pure]

theorem encodeInt_noFrags (w : Nat) (v : Val w) : ∀ b ∈ encodeInt w v, ∀ p i, b ≠ .frag p i := by
  cases v with
  | poison => intro b hb p i; simp [encodeInt, List.mem_replicate] at hb; rw [hb.2]; simp
  | bits x => intro b hb p i; simp [encodeInt] at hb; obtain ⟨_, _, rfl⟩ := hb; simp

/-- A value of an exact type, encoded, decodes back to itself without touching the core. -/
theorem decodeAs_encode {loc : Option Loc} {v : RVal} {T : Ty} {c : Core} {cfg : SpaceCfg}
    (hv : v.hasTy T = true) (hT : Exact T) (hcfg : c.space = cfg) (hsp : 0 < cfg.ptrBits / 8) :
    decodeAs loc T (v.encode cfg) c = .ok (v, c) := by
  subst hcfg
  cases v with
  | int w x =>
    cases T with
    | int w' =>
      simp only [RVal.hasTy, beq_iff_eq] at hv
      subst hv
      simp only [decodeAs, RVal.encode, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, Except.bind, Except.pure,
        mapM_fragToBits loc _ (encodeInt_noFrags w x), MemRules.decode_encodeInt w hT.1 hT.2,
        Option.getD_some]
    | _ => simp [RVal.hasTy] at hv
  | ptr p =>
    cases T with
    | ptr =>
      cases p with
      | none =>
        obtain ⟨k, hk⟩ : ∃ k, c.space.ptrBits / 8 = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hsp).symm⟩
        simp [decodeAs, RVal.encode, encodePtr, hk, bind, StateT.bind, get, getThe,
          MonadStateOf.get, StateT.get, pure, StateT.pure, Except.bind, Except.pure, List.replicate_succ]
      | some q =>
        have hlen : (encodePtr c.space (some q)).length = c.space.ptrBits / 8 := by simp [encodePtr]
        have hnp : (encodePtr c.space (some q)).contains .poison = false := by
          simp [encodePtr]
        show decodeAs loc .ptr (encodePtr c.space (some q)) c = _
        simp only [decodeAs, bind, StateT.bind, get, getThe, MonadStateOf.get,
          StateT.get, pure, Except.bind, Except.pure, hnp, hlen, Bool.false_eq_true, ite_false,
          MemRules.ptrOfFrags_encodePtr c.space q hsp]
        rfl
    | _ => simp [RVal.hasTy] at hv
  | bytes bs =>
    cases T with
    | byte w => rfl
    | _ => simp [RVal.hasTy] at hv


/-! ## Forwarding -/

/-- The heart of the proof: right after a store, a load of the stored type through the same
pointer either fails (a misaligned load is UB) or does exactly what a copy of the stored value
does. -/
theorem load_after_store {loc1 loc2 : Option Loc} {T : Ty} {A1 A2 : Nat} {v op : Operand}
    {r : Result} {c c1 : Core} (hr : r.ty = T) (hT : Exact T) (hsp : 0 < c.space.ptrBits / 8)
    (e : simpleOp loc1 (.store T A1) [] [v, op] c = .ok ((), c1)) :
    (∃ h, simpleOp loc2 (.load A2) [r] [op] c1 = .error h ∧ Escape h) ∨
    simpleOp loc2 (.load A2) [r] [op] c1 = simpleOp loc2 .copy [r] [v] c1 := by
  rw [Dse.simpleOp_store] at e
  cases hv : operandIn c.env loc1 v with
  | error h => rw [hv] at e; cases e
  | ok w =>
  cases hp : operandIn c.env loc1 op with
  | error h => rw [hv, hp] at e; cases e
  | ok pv =>
  rw [hv, hp] at e
  simp only [Except.bind] at e
  obtain ⟨pp, rfl⟩ : ∃ pp, pv = .ptr pp := by
    cases pv <;> first | exact ⟨_, rfl⟩ | cases e
  simp only at e
  cases pp with
  | none => rw [Dse.storeC_none] at e; cases e
  | some p =>
  cases hty : w.hasTy T with
  | false => rw [Dse.storeC_ill_typed hty] at e; cases e
  | true =>
  rw [Dse.storeC_typed hty] at e
  cases hc : checkAccess c loc1 p (T.size c.space) A1 with
  | error h => rw [hc] at e; cases e
  | ok x =>
  rw [hc] at e
  simp only [Except.bind] at e
  cases hm : markAll c.tags loc1 x.1 x.2.1 x.2.2 (T.size c.space) true c.scopes.toList
      c.marks with
  | error h => rw [hm] at e; cases e
  | ok M =>
  rw [hm] at e
  cases e
  rw [simpleOp_one, simpleOp_one]
  have henv : (Dse.written c M x.1 x.2.2 (w.encode c.space)).env = c.env := rfl
  rw [henv, Dse.operandIn_loc (loc' := loc2) hp, Dse.operandIn_loc (loc' := loc2) hv]
  simp only [Except.bind, evalSimple_load, evalSimple_copy, loadC_some, access_eq,
    checkAccess_written, hr]
  rw [show (Dse.written c M x.1 x.2.2 (w.encode c.space)).space = c.space from rfl]
  cases hc2 : checkAccess c loc2 p (T.size c.space) A2 with
  | error h => exact .inl ⟨h, rfl, Dse.checkAccess_error hc2⟩
  | ok x' =>
  right
  obtain rfl := Dse.checkAccess_same hc hc2
  rw [show (Dse.written c M x.1 x.2.2 (w.encode c.space)).tags = c.tags from rfl,
    show (Dse.written c M x.1 x.2.2 (w.encode c.space)).scopes = c.scopes from rfl,
    show (Dse.written c M x.1 x.2.2 (w.encode c.space)).marks = M from rfl]
  dsimp only
  rw [markAll_read loc2 hm (Dse.nodup_scopes c)]
  dsimp only
  simp only [Dse.written, Std.ExtTreeMap.getD_insert_self, ← Dse.encode_length hty c.space,
    MemRules.read_write_same]
  rw [decodeAs_encode (cfg := c.space) hty hT ?_ hsp]
  all_goals rfl


/-! ## The rewrite -/

/-- `s` stores a value through a pointer; `l` loads the same type through the same pointer; `c`
copies the stored value into `l`'s result. -/
def Pat (s l c : Op) : Prop :=
  ∃ T A1 v op loc1 A2 r loc2,
    s = .mk (.store T A1) [] [v, op] [] loc1 ∧
    l = .mk (.load A2) [r] [op] [] loc2 ∧
    c = .mk .copy [r] [v] [] loc2 ∧
    r.ty = T ∧ Exact T

/-- The rewrite: the target has `[s, c]` where the source has `[s, l]`. -/
def L (pt ps : List Op) : Prop := ∃ s l c, pt = [s, c] ∧ ps = [s, l] ∧ Pat s l c

/-- On this core, the load `l` escapes, or does exactly what the copy `c` does. -/
def Ready (c l : Op) (core : Core) : Prop :=
  ∃ A2 r op v loc, l = .mk (.load A2) [r] [op] [] loc ∧ c = .mk .copy [r] [v] [] loc ∧
    ((∃ h, simpleOp loc (.load A2) [r] [op] core = .error h ∧ Escape h) ∨
      simpleOp loc (.load A2) [r] [op] core = simpleOp loc .copy [r] [v] core)

/-- Between a store and the load after it: the target is about to copy, the source to load. -/
def Mid (mt ms : Machine) : Prop :=
  mt.core = ms.core ∧ ∃ c l t s ids rt rs,
    mt.stack = .block (c :: t) ids :: rt ∧ ms.stack = .block (l :: s) ids :: rs ∧
    OpsRel L t s ∧ Forall2 (FrameRel L) rt rs ∧ Ready c l ms.core

/-- Related states: in lockstep, or between a store and its forwarded load. Pointers take at least
one byte throughout. -/
def R (mt ms : Machine) : Prop := (MRel L mt ms ∨ Mid mt ms) ∧ 0 < ms.core.space.ptrBits / 8

/-! ## Steps -/

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
def after (m : Machine) : Except Halt (Unit × Core) → Except Halt Machine
  | .ok (_, core) => .ok { m with core }
  | .error h => .error h

/-- One target step matched by one source step that does the same thing to the same core. -/
theorem step_same {mt ms mt'' ms'' : Machine} {x : Except Halt (Unit × Core)}
    (ht : step mt = after mt'' x) (hs : step ms = after ms'' x)
    (hshape : ms.shape = mt.shape)
    (hR : ∀ u core, x = .ok (u, core) → R { mt'' with core } { ms'' with core }) :
    StepMatch R mt ms := by
  cases x with
  | ok p =>
    obtain ⟨_, core⟩ := p
    refine ⟨fun mt' e => ?_, fun h e => ?_⟩
    · rw [ht, after] at e
      cases e
      refine .inr ⟨0, { ms'' with core }, by rw [runSteps_one, hs, after], hR _ core rfl, ?_⟩
      intro j mj hj ej
      obtain rfl : j = 0 := by omega
      simp only [runSteps, Except.ok.injEq] at ej
      subst ej
      exact hshape
    · rw [ht, after] at e; cases e
  | error h' =>
    refine ⟨fun mt' e => ?_, fun h e => ?_⟩
    · rw [ht, after] at e; cases e
    · rw [ht, after] at e
      cases e
      by_cases hamb : h'.behavior = .ambiguous
      · exact .inl ⟨1, h', by rw [runSteps_one, hs, after], .inr hamb⟩
      · exact .inr ⟨1, h', by rw [runSteps_one, hs, after], Behavior.Refines.refl _ hamb⟩

/-- At a rewritten spot, both run the store, and land between it and the load. -/
theorem step_store {mt ms : Machine} {s l c : Op} {t s' : List Op} {ids : List Nat}
    {rt rs : List Frame} (hc : mt.core = ms.core) (hp : Pat s l c) (hts : OpsRel L t s')
    (hrest : Forall2 (FrameRel L) rt rs) (ht : mt.stack = .block (s :: c :: t) ids :: rt)
    (hs : ms.stack = .block (s :: l :: s') ids :: rs) (hsp : 0 < ms.core.space.ptrBits / 8) :
    StepMatch R mt ms := by
  obtain ⟨T, A1, v, op, loc1, A2, r, loc2, rfl, rfl, rfl, hr, hT⟩ := hp
  refine step_same (x := simpleOp loc1 (.store T A1) [] [v, op] ms.core)
    (mt'' := { mt with stack := .block (.mk .copy [r] [v] [] loc2 :: t) ids :: rt })
    (ms'' := { ms with stack := .block (.mk (.load A2) [r] [op] [] loc2 :: s') ids :: rs })
    ?_ ?_ ?_ ?_
  · simp only [step, ht, Dse.execOp_store, hc]; cases simpleOp loc1 (.store T A1) [] [v, op] ms.core <;> rfl
  · simp only [step, hs, Dse.execOp_store]; cases simpleOp loc1 (.store T A1) [] [v, op] ms.core <;> rfl
  · simp only [Machine.shape, ht, hs]
    exact (shape_cons rfl hrest).symm
  · intro u core e
    obtain ⟨⟩ := u
    have hsp' : core.space = ms.core.space := keeps_simpleOp _ _ _ _ ms.core _ rfl e
    refine ⟨.inr ⟨rfl, _, _, t, s', ids, rt, rs, rfl, rfl, hts, hrest, ?_⟩, hsp' ▸ hsp⟩
    refine ⟨A2, r, op, v, loc2, rfl, rfl, ?_⟩
    exact load_after_store hr hT hsp e


/-- Between the store and the load: the target copies, the source loads the same value (or
escapes), and the two are back in lockstep. -/
theorem step_mid {mt ms : Machine} (hmid : Mid mt ms) (hsp : 0 < ms.core.space.ptrBits / 8) :
    StepMatch R mt ms := by
  obtain ⟨hc, c, l, t, s, ids, rt, rs, ht, hs, hts, hrest, A2, r, op, v, loc, rfl, rfl, hready⟩ :=
    hmid
  have stepT : step mt = after { mt with stack := .block t ids :: rt }
      (simpleOp loc .copy [r] [v] ms.core) := by
    simp only [step, ht, execOp_simple _ .copy _ _ _ rfl rfl rfl, hc]
    cases simpleOp loc .copy [r] [v] ms.core <;> rfl
  have stepS : step ms = after { ms with stack := .block s ids :: rs }
      (simpleOp loc (.load A2) [r] [op] ms.core) := by
    simp only [step, hs, execOp_simple _ (.load A2) _ _ _ rfl rfl rfl]
    cases simpleOp loc (.load A2) [r] [op] ms.core <;> rfl
  rcases hready with ⟨h, e, hesc⟩ | heq
  · have esc : Escapes ms := ⟨1, h, by rw [runSteps_one, stepS, e]; rfl, hesc⟩
    exact ⟨fun _ _ => .inl esc, fun _ _ => .inl esc⟩
  refine step_same stepT (by rw [stepS, heq]) ?_ ?_
  · simp only [Machine.shape, ht, hs]
    exact (shape_cons rfl hrest).symm
  · intro u core e
    have hsp' : core.space = ms.core.space := keeps_simpleOp _ _ _ _ ms.core _ rfl e
    exact ⟨.inl (MRel.mk' rfl (Forall2.cons' (.block hts) hrest)), hsp' ▸ hsp⟩

theorem opsRel_cons {ot : Op} {t s0 : List Op} (h : OpsRel L (ot :: t) s0) :
    (∃ os s, s0 = os :: s ∧ OpRel L ot os ∧ OpsRel L t s) ∨
    (∃ l c t' s, t = c :: t' ∧ s0 = ot :: l :: s ∧ Pat ot l c ∧ OpsRel L t' s) := by
  generalize hx : ot :: t = x at h
  cases h with
  | refl => subst hx; exact .inl ⟨_, _, rfl, .refl _, .refl _⟩
  | cons ho hr =>
    injection hx with h1 h2
    subst h1 h2
    exact .inl ⟨_, _, rfl, ho, hr⟩
  | rw hl hr =>
    obtain ⟨s1, l, c, rfl, rfl, hp⟩ := hl
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact .inr ⟨l, c, _, _, rfl, rfl, hp, hr⟩

theorem opsRel_nil {s0 : List Op} (h : OpsRel L [] s0) : s0 = [] := by
  generalize hx : ([] : List Op) = x at h
  cases h with
  | refl => rfl
  | cons => cases hx
  | rw hl _ =>
    obtain ⟨_, _, _, rfl, _, _⟩ := hl
    cases hx

theorem sim : Simulation R := by
  intro mt ms ⟨hR, hsp⟩
  rcases hR with ⟨hc, hst⟩ | hmid
  case inr => exact step_mid hmid hsp
  have lock : (∀ ot t ids rt, mt.stack = .block (ot :: t) ids :: rt →
        ∃ os s rs, ms.stack = .block (os :: s) ids :: rs ∧ OpRel L ot os ∧ OpsRel L t s) →
      (∀ ids rt, mt.stack = .block [] ids :: rt → ∃ rs, ms.stack = .block [] ids :: rs) →
      StepMatch R mt ms := fun hh hn =>
    (StepMatch.of_lockstep ⟨hc, hst⟩ (step_eq ⟨hc, hst⟩ hh hn)).mono
      fun _ _ _ ek h => ⟨.inl h, by rw [runSteps_space ek]; exact hsp⟩
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
          rcases opsRel_cons hops with ⟨os, s, rfl, ho, hts⟩ | ⟨l, c, t', s, rfl, rfl, hp, hts⟩
          · refine lock (fun ot' t' ids' rt' e => ?_) (fun ids' rt' e => ?_)
            · rw [ht, List.cons.injEq, Frame.block.injEq, List.cons.injEq] at e
              obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := e
              exact ⟨os, s, rs, hs, ho, hts⟩
            · rw [ht] at e; simp at e
          · exact step_store hc hp hts hrest ht hs hsp
      | loop hb =>
        refine lock (fun _ _ _ _ e => ?_) (fun _ _ e => ?_) <;> (rw [ht] at e; simp at e)

theorem init_match {mod : Module} {tgt src : Func} (hsp : 0 < mod.space.ptrBits / 8)
    (hparams : tgt.params = src.params) (hrets : tgt.rets = src.rets)
    (hops : OpsRel L tgt.body.ops src.body.ops) (oracle : Nat → Int) (args : List RVal) :
    InitMatch R (Machine.init oracle mod tgt args) (Machine.init oracle mod src args) := by
  have hinit := @init_space oracle mod src args
  simp only [Machine.init, hparams, hrets, bind, Except.bind] at hinit ⊢
  cases e : (enterCall none src.params args).run (Core.initial oracle mod) with
  | error h =>
    by_cases hamb : h.behavior = .ambiguous
    · exact .inl ⟨h, rfl, .inr hamb⟩
    · exact .inr (.inr ⟨h, h, rfl, rfl, Behavior.Refines.refl _ hamb⟩)
  | ok r =>
    rw [e] at hinit
    refine .inr (.inl ⟨_, _, rfl, rfl, .inl (MRel.mk' rfl
      (Forall2.cons' (.block hops) (Forall2.cons' (.refl _) trivial))), ?_⟩)
    rw [hinit rfl]
    exact hsp

/-- **Store-to-load forwarding is correct.** Replacing, anywhere in a function, a load right after
a store of the same type through the same pointer with a copy of the stored value gives a function
that refines the original, for every argument and every oracle. Integer types must be whole bytes,
and pointers must take at least one byte (the verifier checks both). -/
theorem refines {mod : Module} {tgt src : Func} (hsp : 8 ≤ mod.space.ptrBits)
    (hparams : tgt.params = src.params) (hrets : tgt.rets = src.rets)
    (hops : OpsRel L tgt.body.ops src.body.ops) (dec : src.Decided mod) : tgt.Refines mod src :=
  Simulation.refines sim
    (fun oracle args => ⟨oracle, init_match (by omega) hparams hrets hops oracle args⟩) dec


/-! ## Look-alikes that are wrong -/

/-- Forwarding an integer whose width isn't whole bytes is wrong: memory keeps only its whole
bytes, so an `i12` loads back without its top four bits. This is why `Exact` requires whole
bytes. -/
theorem forward_partial_byte_wrong :
    ¬ ∀ v : Val 12, decodeInt? 12 (encodeInt 12 v) = some v := by
  intro h
  have := h (.bits 0xFFF)
  simp [decodeInt?, encodeInt, digits, undigits] at this

end Fir.Fwd
