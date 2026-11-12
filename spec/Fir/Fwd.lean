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

/-- A simple op computes its results, then checks them. -/
theorem simpleOp_eq (loc : Option Loc) (k : OpKind) (rs : List Result) (vs : List RVal) (c : Core) :
    simpleOp loc k rs vs c =
      (evalSimple loc k rs vs c).bind fun p =>
      (checkResults loc rs p.1 p.2).bind fun q => .ok (p.1, q.2) := by
  simp only [simpleOp, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]

theorem evalSimple_copy (loc : Option Loc) (r : Result) (x : RVal) (c : Core) :
    evalSimple loc .copy [r] [x] c = .ok ([x], c) := rfl

/-- A load of a scalar type is `loadC`. -/
theorem loadAny_value {loc : Option Loc} {T : Ty} {A : Nat} {p : Option Ptr}
    (hT : T.isValue = true) : loadAny loc T A p = loadC loc T A p := by
  simp [loadAny, hT]

theorem evalSimple_load (loc : Option Loc) (A : Nat) (r : Result) (p : Option Ptr) (c : Core)
    (hT : r.ty.isValue = true) :
    evalSimple loc (.load A) [r] [.ptr p] c =
      (loadC loc r.ty A p c).bind fun q => .ok ([q.1], q.2) := by
  simp only [evalSimple, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, Except.bind, asPtr, Except.pure, loadAny_value hT]

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

/-- Scalar types whose values come back unchanged from memory. Integer widths must be whole
bytes; floats come back bit for bit, NaN payloads included. (Aggregates are HFIR only; the
rewrite is for MFIR's scalar loads and stores.) -/
def Exact : Ty → Prop
  | .int w => w % 8 = 0 ∧ 0 < w
  | .ptr | .byte _ | .float _ => True
  | _ => False

theorem Exact.isValue {T : Ty} (h : Exact T) : T.isValue = true := by
  cases T <;> simp_all [Exact, Ty.isValue]

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
  | agg vs => cases T <;> simp [Exact, RVal.hasTy] at hT hv
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
  | float f x =>
    cases T with
    | float f' =>
      simp only [RVal.hasTy, beq_iff_eq] at hv
      subst hv
      have hw : f.width % 8 = 0 ∧ 0 < f.width := by cases f <;> decide
      simp only [decodeAs, RVal.encode, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, Except.bind, Except.pure,
        mapM_fragToBits loc _ (encodeInt_noFrags f.width x),
        MemRules.decode_encodeInt f.width hw.1 hw.2, Option.getD_some]
    | _ => simp [RVal.hasTy] at hv


/-! ## Forwarding -/

/-- The heart of the proof: right after a store, a load of the stored type through the same
pointer either fails (a misaligned load is UB) or computes exactly what a copy of the stored value
computes. -/
theorem load_after_store {loc1 loc2 : Option Loc} {T : Ty} {A1 A2 : Nat} {w pv : RVal}
    {r : Result} {c c1 : Core} {outs : List RVal} (hr : r.ty = T) (hT : Exact T)
    (hsp : 0 < c.space.ptrBits / 8)
    (e : simpleOp loc1 (.store T A1) [] [w, pv] c = .ok (outs, c1)) :
    (∃ h, evalSimple loc2 (.load A2) [r] [pv] c1 = .error h ∧ Escape h) ∨
    evalSimple loc2 (.load A2) [r] [pv] c1 = evalSimple loc2 .copy [r] [w] c1 := by
  rw [Dse.simpleOp_store _ _ _ _ _ _ hT.isValue] at e
  obtain ⟨pp, rfl⟩ : ∃ pp, pv = .ptr pp := by
    cases pv <;> first | exact ⟨_, rfl⟩ | cases e
  simp only at e
  cases pp with
  | none => rw [Dse.storeC_none] at e; cases e
  | some p =>
  cases hty : w.hasTy T with
  | false => rw [Dse.storeC_ill_typed hty] at e; cases e
  | true =>
  rw [Dse.storeC_typed hty hT.isValue] at e
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
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  simp only [evalSimple_load _ _ _ _ _ (hr ▸ hT.isValue), evalSimple_copy, loadC_some, access_eq,
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
  dsimp only [Except.bind]
  rw [markAll_read loc2 hm (Dse.nodup_scopes c)]
  dsimp only
  simp only [Dse.written, Std.ExtTreeMap.getD_insert_self, ← Dse.encode_length hty hT.isValue c.space,
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
def L (pt ps _ : List Op) : Prop := ∃ s l c, pt = [s, c] ∧ ps = [s, l] ∧ Pat s l c

/-- On this core, with operands from the frames `fs`, the load `l` escapes, or computes exactly
what the copy `c` computes. -/
def Ready (c l : Op) (fs : List Frame) (core : Core) : Prop :=
  ∃ A2 r op v loc, l = .mk (.load A2) [r] [op] [] loc ∧ c = .mk .copy [r] [v] [] loc ∧
    ((∃ h, ((operands fs loc [op]).bind fun vs => simpleOp loc (.load A2) [r] vs core) = .error h ∧
        Escape h) ∨
      ((operands fs loc [op]).bind fun vs => simpleOp loc (.load A2) [r] vs core) =
        ((operands fs loc [v]).bind fun vs => simpleOp loc .copy [r] vs core))

/-- Between a store and the load after it: the target is about to copy, the source to load. -/
def Mid (mt ms : Machine) : Prop :=
  mt.core = ms.core ∧ ∃ D Db c l t s ids et es ft fs,
    mt.stack = .block (c :: t) ids et :: ft ∧ ms.stack = .block (l :: s) ids es :: fs ∧
    OpsRel L t s ∧ StackRel L Db ft fs ∧ (∀ n, Db n → D n) ∧ EnvAgree D et es ∧
    NoReads D (c :: t) ∧ Ready c l (.block s ids es :: fs) ms.core

/-- Related states: in lockstep, or between a store and its forwarded load. Pointers take at least
one byte throughout. -/
def R (mt ms : Machine) : Prop := (MRel L mt ms ∨ Mid mt ms) ∧ 0 < ms.core.space.ptrBits / 8

/-! ## Steps -/

theorem simpleOp_ok_space {loc : Option Loc} {k : OpKind} {rs : List Result} {vs : List RVal}
    {c c' : Core} {outs : List RVal} (e : simpleOp loc k rs vs c = .ok (outs, c')) :
    c'.space = c.space := by
  have := keeps_simpleOp (sp := c.fixed) loc k rs vs c _ rfl e
  simp only [Core.fixed, Prod.mk.injEq] at this
  exact this.1

/-- At a rewritten spot, both run the store, and land between it and the load. -/
theorem step_store {mt ms : Machine} {s l c : Op} {t s' : List Op} {ids : List Nat}
    {et es : Env} {ft fs : List Frame} {D Db : String → Prop} (hc : mt.core = ms.core)
    (hp : Pat s l c) (hts : OpsRel L t s') (hb : StackRel L Db ft fs) (hDb : ∀ n, Db n → D n)
    (hag : EnvAgree D et es) (hnr : NoReads D ([s, c] ++ t))
    (ht : mt.stack = .block ([s, c] ++ t) ids et :: ft)
    (hs : ms.stack = .block ([s, l] ++ s') ids es :: fs) (hsp : 0 < ms.core.space.ptrBits / 8) :
    StepMatch R mt ms := by
  obtain ⟨T, A1, v, op, loc1, A2, r, loc2, rfl, rfl, rfl, hr, hT⟩ := hp
  obtain ⟨core, stt⟩ := mt
  obtain ⟨cs, sts⟩ := ms
  dsimp only at hc ht hs hsp
  subst hc ht hs
  simp only [List.cons_append, List.nil_append] at hnr ⊢
  obtain ⟨hrs, hnr1⟩ := NoReads.cons hnr
  have rel : StackRel L D (.block t ids et :: ft) (.block s' ids es :: fs) :=
    .block hb hDb hts hag hnr1.cons.2
  have hargs := (Op.reads_mk hrs).1
  let S1 : List Frame := .block (.mk (.load A2) [r] [op] [] loc2 :: s') ids es :: fs
  refine step_same
    (x := (operands S1 loc1 [v, op]).bind fun vs => simpleOp loc1 (.store T A1) [] vs core)
    (ft := fun outs core => ⟨core, bindTop [] outs
      (.block (.mk .copy [r] [v] [] loc2 :: t) ids et :: ft)⟩)
    (fs := fun outs core => ⟨core, bindTop [] outs S1⟩) ?_ ?_ ?_ (Events.Refines.refl _) ?_
  · rw [step_simple rfl rfl rfl, operands_ops _ t, rel.operands loc1 hargs, operands_ops s']
  · rw [step_simple rfl rfl rfl]
  · simp only [Machine.shape]
    exact (shape_cons rfl hb).symm
  · intro outs core' e
    rw [operands_pair] at e
    cases hv : operandIn S1 loc1 v with
    | error h => rw [hv] at e; cases e
    | ok w =>
    cases hop : operandIn S1 loc1 op with
    | error h => rw [hv, hop] at e; cases e
    | ok pv =>
    rw [hv, hop] at e
    simp only [Except.bind] at e
    have hsp' := simpleOp_ok_space e
    simp only [bindTop_nil]
    refine ⟨.inr ⟨rfl, D, Db, _, _, t, s', ids, et, es, ft, fs, rfl, rfl, hts, hb, hDb, hag,
      hnr1, A2, r, op, v, loc2, rfl, rfl, ?_⟩, by simpa [hsp'] using hsp⟩
    rw [operandIn_ops _ s'] at hv hop
    rw [operands_one, operands_one, operandIn_loc (loc' := loc2) hv,
      operandIn_loc (loc' := loc2) hop]
    simp only [Except.bind]
    rw [simpleOp_eq, simpleOp_eq]
    rcases load_after_store (loc2 := loc2) (A2 := A2) hr hT hsp e with ⟨h, e1, hesc⟩ | heq
    · exact .inl ⟨h, by rw [e1]; rfl, hesc⟩
    · exact .inr (by rw [heq])

/-- Between the store and the load: the target copies, the source loads the same value (or
escapes), and the two are back in lockstep. -/
theorem step_mid {mt ms : Machine} (hmid : Mid mt ms) (hsp : 0 < ms.core.space.ptrBits / 8) :
    StepMatch R mt ms := by
  obtain ⟨hc, D, Db, c, l, t, s, ids, et, es, ft, fs, ht, hs, hts, hb, hDb, hag, hnr, A2, r, op, v,
    loc, rfl, rfl, hready⟩ := hmid
  obtain ⟨core, stt⟩ := mt
  obtain ⟨cs, sts⟩ := ms
  dsimp only at hc ht hs hsp hready
  subst hc ht hs
  obtain ⟨hrc, hnr'⟩ := NoReads.cons hnr
  have rel : StackRel L D (.block t ids et :: ft) (.block s ids es :: fs) :=
    .block hb hDb hts hag hnr'
  have stepS := step_simple (c := core) (k := .load A2) (res := [r]) (args := [op]) (loc := loc)
    (t := s) (ids := ids) (env := es) (fs := fs) rfl rfl rfl
  rcases hready with ⟨h, e, hesc⟩ | heq
  · have esc : Escapes core.trace ⟨core, _⟩ :=
      Escapes.one (by rw [runSteps_one, stepS, e]; rfl) hesc (Events.Refines.refl _)
    exact ⟨fun _ _ => .inl esc, fun _ _ => .inl esc⟩
  refine step_same
    (x := (operands (.block s ids es :: fs) loc [v]).bind fun vs => simpleOp loc .copy [r] vs core)
    (ft := fun outs core => ⟨core, bindTop [r] outs (.block t ids et :: ft)⟩)
    (fs := fun outs core => ⟨core, bindTop [r] outs (.block s ids es :: fs)⟩) ?_ ?_ ?_
    (Events.Refines.refl _) ?_
  · rw [step_simple rfl rfl rfl, rel.operands loc (Op.reads_mk hrc).1]
  · rw [stepS, heq]
  · simp only [Machine.shape]
    exact (shape_cons rfl hb).symm
  · intro outs core' e
    obtain ⟨vs, -, e'⟩ : ∃ vs, operands (.block s ids es :: fs) loc [v] = .ok vs ∧
        simpleOp loc .copy [r] vs core = .ok (outs, core') := by
      cases ho : operands (.block s ids es :: fs) loc [v] with
      | error h => rw [ho] at e; cases e
      | ok vs => rw [ho] at e; exact ⟨vs, rfl, e⟩
    exact ⟨.inl ⟨rfl, D, rel.bindTop _ _⟩, by simpa [simpleOp_ok_space e'] using hsp⟩

theorem sim : Simulation R := by
  intro mt ms ⟨hR, hsp⟩
  rcases hR with hR | hmid
  case inr => exact step_mid hmid hsp
  refine StepMatch.of_mrel hR (fun _ _ _ ek h => ⟨.inl h, by rw [runSteps_space ek]; exact hsp⟩) ?_
  intro D Db pt ps t s ids et es ft fs hl hts hb hDb hag hnr ht hs
  obtain ⟨s1, l, c, rfl, rfl, hp⟩ := hl
  exact step_store hR.1 hp hts hb hDb hag hnr ht hs hsp

theorem init_match {mod : Module} {tgt src : Func} (hsp : 0 < mod.space.ptrBits / 8)
    (hparams : tgt.params = src.params) (hrets : tgt.rets = src.rets)
    (hops : OpsRel L tgt.body.ops src.body.ops) (oracle : Nat → Int) (world : World)
    (args : List RVal) :
    InitMatch R (Machine.init oracle world mod tgt args) (Machine.init oracle world mod src args) := by
  rcases init_lockstep (mod := mod) hparams hrets hops oracle world args with ⟨h, e1, e2⟩ |
    ⟨mt, ms, e1, e2, hR⟩
  · rw [e1, e2]
    by_cases hamb : h.outcome = .ambiguous
    · exact .inl ⟨h, rfl, .inr hamb⟩
    · exact .inr (.inr ⟨h, h, rfl, rfl, Outcome.Refines.refl _ hamb⟩)
  · rw [e1, e2]
    exact .inr (.inl ⟨mt, ms, rfl, rfl, .inl hR, by rw [init_space e2]; exact hsp⟩)

/-- **Store-to-load forwarding is correct.** Replacing, anywhere in a function, a load right after
a store of the same type through the same pointer with a copy of the stored value gives a function
that refines the original, for every argument and every oracle. Integer types must be whole bytes,
and pointers must take at least one byte (the verifier checks both). -/
theorem refines {mod : Module} {tgt src : Func} (hsp : 8 ≤ mod.space.ptrBits)
    (hparams : tgt.params = src.params) (hrets : tgt.rets = src.rets)
    (hops : OpsRel L tgt.body.ops src.body.ops) (dec : src.Decided mod) : tgt.Refines mod src :=
  Simulation.refines sim (fun _ _ h => by
      rcases h.1 with h | h <;> rw [h.1] <;> exact Events.Refines.refl _)
    (fun oracle world args => ⟨oracle, init_match (by omega) hparams hrets hops oracle world args⟩) dec


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
