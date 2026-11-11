import Fir.CodeRel
import Fir.MemRules

/-!
# Dead store elimination

The first rewrite proved with the simulation framework: a store immediately followed by another
store of the same size through the same pointer is dead, and can be deleted.

```
mem.store T1 %x, %p, align A1        // deleted
mem.store T2 %y, %p, align A2
```

`Dse.refines` proves the rewrite correct at any number of places in a function, at any depth
(inside `cf.if` and `cf.loop` regions too). The source may fail at the deleted store (an
undefined `%x`, a value of the wrong type, a bad pointer, a broken `noalias` scope); that is UB or
a malformed program, so the target may do anything there. Otherwise the second store leaves
memory and the `noalias` scopes exactly as if only it had run, and the two machines continue
with equal cores.

The look-alikes are rejected in `Fir.MemRules`: a shorter second store doesn't hide the first
(`writeBytes_shorter_wrong`), and two stores to the same byte can't swap places.
-/

namespace Fir.Dse

/-! ## How runs halt -/

/-- A halt that lets the target do anything (UB, stuck), or one `Func.Decided` rules out. -/
def Escape (h : Halt) : Prop := h.behavior.Absorbing ∨ h.behavior = .ambiguous

theorem halt_error {b : Behavior} {loc : Option Loc} {note : String} {h : Halt}
    (e : (halt b loc note : Except Halt α) = .error h) : h.behavior = b := by
  cases e; rfl

theorem escape_ub {k : UBKind} {loc : Option Loc} {note : String} {h : Halt}
    (e : (ub k loc note : Except Halt α) = .error h) : Escape h :=
  .inl (by rw [halt_error e]; trivial)

theorem escape_stuck {msg : String} {loc : Option Loc} {note : String} {h : Halt}
    (e : (halt (.stuck msg) loc note : Except Halt α) = .error h) : Escape h :=
  .inl (by rw [halt_error e]; trivial)

theorem escape_ambiguous {loc : Option Loc} {note : String} {h : Halt}
    (e : (halt .ambiguous loc note : Except Halt α) = .error h) : Escape h :=
  .inr (halt_error e)

/-! ## Value sizes -/

theorem length_digits (k n : Nat) : (digits k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [digits, ih]

/-- A value of type `T` takes `T.size` bytes. -/
theorem encode_length {v : RVal} {T : Ty} (h : v.hasTy T = true) (cfg : SpaceCfg) :
    (v.encode cfg).length = T.size cfg := by
  cases v with
  | int w x =>
    cases T with
    | int w' =>
      simp only [RVal.hasTy, beq_iff_eq] at h
      subst h
      cases x <;> simp [RVal.encode, encodeInt, Ty.size, length_digits]
    | _ => simp [RVal.hasTy] at h
  | ptr p =>
    cases T with
    | ptr => cases p <;> simp [RVal.encode, encodePtr, Ty.size]
    | _ => simp [RVal.hasTy] at h
  | bytes bs =>
    cases T with
    | byte w =>
      simp only [RVal.hasTy, beq_iff_eq] at h
      simp [RVal.encode, Ty.size]
      omega
    | _ => simp [RVal.hasTy] at h

/-! ## Marks -/

theorem markByte_idem (d w : Bool) (mk : Mark) : markByte d w (markByte d w mk) = markByte d w mk := by
  obtain ⟨x, y, z⟩ := mk
  cases d <;> cases w <;> cases x <;> cases y <;> cases z <;> rfl

theorem getElem?_markScope (d w : Bool) (ms : Marks) (off n k : Nat) :
    (markScope d w ms off n)[k]? =
      if off ≤ k ∧ k < off + n then some (markByte d w (ms.getD k (false, false, false)))
      else ms[k]? := by
  induction n generalizing ms off with
  | zero => simp only [markScope]; rw [ite_eq_right (by omega)]
  | succ n ih =>
    rw [markScope, ih]
    simp only [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getD_insert, Nat.compare_eq_eq]
    by_cases h1 : off + 1 ≤ k ∧ k < off + 1 + n
    · have h2 : off ≠ k := by omega
      simp [h1, h2, show off ≤ k ∧ k < off + (n + 1) from by omega]
    · by_cases h2 : off = k
      · subst h2; simp; omega
      · simp [h1, h2, show ¬(off ≤ k ∧ k < off + (n + 1)) from by omega]

theorem getD_markScope (d w : Bool) (ms : Marks) (off n i : Nat) (hi : i < n) :
    (markScope d w ms off n).getD (off + i) (false, false, false) =
      markByte d w (ms.getD (off + i) (false, false, false)) := by
  rw [Std.ExtTreeMap.getD_eq_getD_getElem?, getElem?_markScope, ite_eq_left (by omega)]
  rfl

/-- Marking the same bytes again changes nothing. -/
theorem markScope_idem (d w : Bool) (ms : Marks) (off n : Nat) :
    markScope d w (markScope d w ms off n) off n = markScope d w ms off n := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [getElem?_markScope]
  split
  · rename_i hk
    simp only [Std.ExtTreeMap.getD_eq_getD_getElem?, getElem?_markScope, hk, and_self, ite_true,
      Option.getD_some, markByte_idem]
  · rfl

theorem find?_congr {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.find?_cons, h x (by simp)]
    rw [find?_congr (fun y hy => h y (by simp [hy]))]

theorem firstBad_markScope (d w : Bool) (ms : Marks) (off n : Nat) :
    firstBad d w (markScope d w ms off n) off n = firstBad d w ms off n := by
  unfold firstBad
  apply find?_congr
  intro i hi
  rw [List.mem_range] at hi
  rw [getD_markScope d w ms off n i hi, markByte_idem]

theorem insert_self {mm : Std.ExtTreeMap Nat Marks} {id : Nat} {v : Marks} (h : mm[id]? = some v) :
    mm.insert id v = mm := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [Std.ExtTreeMap.getElem?_insert]
  split
  · rename_i hk; rw [Nat.compare_eq_eq] at hk; subst hk; exact h.symm
  · rfl

theorem markAll_error {tags : Std.ExtTreeMap Nat (Option Nat)} {loc : Option Loc}
    {a t off n : Nat} {w : Bool} :
    ∀ {L : List (Nat × Scope)} {mm : Std.ExtTreeMap Nat Marks} {h : Halt},
      markAll tags loc a t off n w L mm = .error h → Escape h
  | [], _, _, e => by cases e
  | (id, s) :: rest, mm, h, e => by
    simp only [markAll] at e
    split at e
    · exact markAll_error e
    · split at e
      · exact escape_ub e
      · split at e
        · exact markAll_error e
        · split at e
          · exact escape_ub e
          · exact markAll_error e

/-- What the access is recorded as doesn't depend on where the op is. -/
theorem markAll_loc {tags : Std.ExtTreeMap Nat (Option Nat)} {loc loc' : Option Loc}
    {a t off n : Nat} {w : Bool} :
    ∀ {L : List (Nat × Scope)} {mm mm' : Std.ExtTreeMap Nat Marks},
      markAll tags loc a t off n w L mm = .ok mm' → markAll tags loc' a t off n w L mm = .ok mm'
  | [], _, _, e => e
  | (id, s) :: rest, mm, mm', e => by
    simp only [markAll] at e ⊢
    split at e
    · rw [ite_eq_left (by assumption)]; exact markAll_loc e
    · rw [ite_eq_right (by assumption)]
      split at e
      · cases e
      · rw [ite_eq_right (by assumption)]
        split at e
        · rw [ite_eq_left (by assumption)]; exact markAll_loc e
        · rw [ite_eq_right (by assumption)]
          split at e
          · cases e
          · exact markAll_loc e

theorem markAll_other {tags : Std.ExtTreeMap Nat (Option Nat)} {loc : Option Loc}
    {a t off n : Nat} {w : Bool} {id : Nat} :
    ∀ {L : List (Nat × Scope)} {mm mm' : Std.ExtTreeMap Nat Marks},
      markAll tags loc a t off n w L mm = .ok mm' → id ∉ L.map (·.1) → mm'[id]? = mm[id]?
  | [], _, _, e, _ => by cases e; rfl
  | (id', s) :: rest, mm, mm', e, hid => by
    simp only [List.map_cons, List.mem_cons, not_or] at hid
    simp only [markAll] at e
    split at e
    · exact markAll_other e hid.2
    · split at e
      · cases e
      · split at e
        · exact markAll_other e hid.2
        · split at e
          · cases e
          · rw [markAll_other e hid.2, Std.ExtTreeMap.getElem?_insert,
              ite_eq_right (by rw [Nat.compare_eq_eq]; exact fun h => hid.1 h.symm)]

/-- Recording the same access again changes nothing. -/
theorem markAll_idem {tags : Std.ExtTreeMap Nat (Option Nat)} {loc : Option Loc}
    {a t off n : Nat} {w : Bool} :
    ∀ {L : List (Nat × Scope)} {mm mm' : Std.ExtTreeMap Nat Marks},
      markAll tags loc a t off n w L mm = .ok mm' → (L.map (·.1)).Nodup →
      markAll tags loc a t off n w L mm' = .ok mm'
  | [], _, _, e, _ => by cases e; rfl
  | (id, s) :: rest, mm, mm', e, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [markAll] at e ⊢
    split at e
    · rw [ite_eq_left (by assumption)]; exact markAll_idem e hnd.2
    · rw [ite_eq_right (by assumption)]
      split at e
      · cases e
      · rw [ite_eq_right (by assumption)]
        split at e
        · rw [ite_eq_left (by assumption)]; exact markAll_idem e hnd.2
        · rw [ite_eq_right (by assumption)]
          split at e
          · cases e
          · rename_i hb
            have hid := markAll_other e hnd.1
            rw [Std.ExtTreeMap.getElem?_insert_self] at hid
            have hget : mm'.getD id ∅ = markScope (isDerived tags s.tag t) w (mm.getD id ∅) off n := by
              rw [Std.ExtTreeMap.getD_eq_getD_getElem?, hid]; rfl
            simp only [hget, firstBad_markScope, hb, markScope_idem]
            rw [insert_self hid]
            exact markAll_idem e hnd.2

theorem nodup_scopes (c : Core) : (c.scopes.toList.map (·.1)).Nodup := by
  have := Std.ExtTreeMap.distinct_keys_toList (t := c.scopes)
  rw [List.Nodup, List.pairwise_map]
  exact this.imp fun h e => h (by rw [e]; exact Nat.compare_eq_eq.mpr rfl)

/-! ## Accesses -/

theorem resolveIn_error {c : Core} {loc : Option Loc} {p : Ptr} {n : Nat} {h : Halt}
    (e : resolveIn c loc p n = .error h) : Escape h := by
  unfold resolveIn at e
  dsimp only at e
  repeat' split at e
  all_goals (cases e <;> first | exact .inl trivial | exact .inr rfl)

/-- Where an access goes doesn't depend on where the op is. -/
theorem resolveIn_loc {c : Core} {loc loc' : Option Loc} {p : Ptr} {n : Nat}
    {r : Nat × Nat × Int} (e : resolveIn c loc p n = .ok r) : resolveIn c loc' p n = .ok r := by
  unfold resolveIn at e ⊢
  dsimp only at e ⊢
  repeat' split at e
  all_goals (cases e <;> simp_all [pure, Except.pure])

theorem checkAccess_error {c : Core} {loc : Option Loc} {p : Ptr} {n A : Nat} {h : Halt}
    (e : checkAccess c loc p n A = .error h) : Escape h := by
  unfold checkAccess at e
  cases hr : resolveIn c loc p n with
  | error h' =>
    rw [hr] at e
    cases e
    exact resolveIn_error hr
  | ok r =>
    obtain ⟨a, t, off⟩ := r
    rw [hr] at e
    dsimp only [bind, Except.bind] at e
    cases hal : allocIn c loc a with
    | error h' =>
      rw [hal] at e
      unfold allocIn at hal
      split at hal
      · cases hal
      · cases hal; cases e; exact .inl trivial
    | ok al =>
      rw [hal] at e
      dsimp only at e
      repeat' split at e
      all_goals first
        | (rename_i heq; cases heq; done)
        | (cases e; rename_i heq; cases heq; exact .inl trivial)
        | (cases e; done)

/-- A checked access goes where the pointer resolves to. -/
theorem checkAccess_ok {c : Core} {loc : Option Loc} {p : Ptr} {n A : Nat} {r : Nat × Nat × Nat}
    (e : checkAccess c loc p n A = .ok r) :
    ∃ o : Int, resolveIn c loc p n = .ok (r.1, r.2.1, o) ∧ r.2.2 = o.toNat := by
  unfold checkAccess at e
  cases hr : resolveIn c loc p n with
  | error h' => rw [hr] at e; cases e
  | ok x =>
    obtain ⟨a, t, off⟩ := x
    rw [hr] at e
    dsimp only [bind, Except.bind] at e
    cases hal : allocIn c loc a with
    | error h' => rw [hal] at e; cases e
    | ok al =>
      rw [hal] at e
      dsimp only at e
      repeat' split at e
      all_goals first
        | (rename_i heq; cases heq; done)
        | (cases e; done)
        | (cases e; exact ⟨off, rfl, rfl⟩)

/-- Two checked accesses through the same pointer, of the same size, go to the same place. -/
theorem checkAccess_same {c : Core} {loc loc' : Option Loc} {p : Ptr} {n A A' : Nat}
    {r r' : Nat × Nat × Nat} (e : checkAccess c loc p n A = .ok r)
    (e' : checkAccess c loc' p n A' = .ok r') : r = r' := by
  obtain ⟨o, h1, h2⟩ := checkAccess_ok e
  obtain ⟨o', h1', h2'⟩ := checkAccess_ok e'
  rw [resolveIn_loc (loc' := loc') h1] at h1'
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1'
  obtain ⟨ha, ht, ho⟩ := h1'
  obtain ⟨a, t, off⟩ := r
  obtain ⟨a', t', off'⟩ := r'
  simp only at ha ht h2 h2'
  subst ha ht ho
  rw [h2, h2']

/-! ## Stores -/

theorem storeC_none {loc : Option Loc} {T : Ty} {A : Nat} {v : RVal} {c : Core} :
    storeC loc T A v none c =
      .error { behavior := .ub .poison, loc := loc, note := "store through a poison pointer" } :=
  rfl

theorem storeC_ill_typed {loc : Option Loc} {T : Ty} {A : Nat} {v : RVal} {p : Ptr} {c : Core}
    (h : v.hasTy T = false) :
    storeC loc T A v (some p) c =
      .error { behavior := .stuck s!"the stored value isn't a {T}", loc := loc } := by
  simp [storeC, h, halt, throw, throwThe, MonadExcept.throw, bind, Except.bind]
  rfl

/-- The core after a store's write. -/
def written (c : Core) (marks : Std.ExtTreeMap Nat Marks) (a off : Nat) (bs : List Byte) : Core :=
  { c with marks := marks, mem := c.mem.insert a (writeBytes (c.mem.getD a ∅) off bs) }

/-- A store of a value of the right type: check the access, record it in the scopes, write. -/
theorem storeC_typed {loc : Option Loc} {T : Ty} {A : Nat} {v : RVal} {p : Ptr} {c : Core}
    (h : v.hasTy T = true) :
    storeC loc T A v (some p) c =
      (checkAccess c loc p (T.size c.space) A).bind fun r =>
      (markAll c.tags loc r.1 r.2.1 r.2.2 (T.size c.space) true c.scopes.toList c.marks).bind
        fun marks => .ok ((), written c marks r.1 r.2.2 (v.encode c.space)) := by
  simp only [storeC, h, access, encode_length h, ↓reduceIte]
  cases checkAccess c loc p (T.size c.space) A with
  | error e => rfl
  | ok r =>
    simp only [bind, Except.bind, pure, Except.pure]
    cases markAll c.tags loc r.1 r.2.1 r.2.2 (T.size c.space) true c.scopes.toList c.marks with
    | error e => rfl
    | ok m => rfl

theorem storeC_error {loc : Option Loc} {T : Ty} {A : Nat} {v : RVal} {p : Option Ptr} {c : Core}
    {h : Halt} (e : storeC loc T A v p c = .error h) : Escape h := by
  cases p with
  | none => rw [storeC_none] at e; cases e; exact .inl trivial
  | some p =>
    cases hty : v.hasTy T with
    | false => rw [storeC_ill_typed hty] at e; cases e; exact .inl trivial
    | true =>
      rw [storeC_typed hty] at e
      cases hc : checkAccess c loc p (T.size c.space) A with
      | error h' => rw [hc] at e; cases e; exact checkAccess_error hc
      | ok r =>
        rw [hc] at e
        dsimp only [Except.bind] at e
        cases hm : markAll c.tags loc r.1 r.2.1 r.2.2 (T.size c.space) true c.scopes.toList c.marks with
        | error h' => rw [hm] at e; cases e; exact markAll_error hm
        | ok m => rw [hm] at e; cases e

theorem insert_insert {α : Type} {m : Std.ExtTreeMap Nat α} {k : Nat} {x y : α} :
    (m.insert k x).insert k y = m.insert k y := by
  apply Std.ExtTreeMap.ext_getElem?
  intro i
  simp only [Std.ExtTreeMap.getElem?_insert]
  split <;> rfl

/-- The heart of the proof: after a store, a second store of the same size through the same
pointer does exactly what it would have done alone. -/
theorem store_twice {loc1 loc2 : Option Loc} {T1 T2 : Ty} {A1 A2 : Nat} {v1 v2 : RVal}
    {p : Ptr} {c c1 : Core} (hsz : ∀ cfg, T1.size cfg = T2.size cfg)
    (e1 : storeC loc1 T1 A1 v1 (some p) c = .ok ((), c1)) :
    storeC loc2 T2 A2 v2 (some p) c1 = storeC loc2 T2 A2 v2 (some p) c := by
  cases hty1 : v1.hasTy T1 with
  | false => rw [storeC_ill_typed hty1] at e1; cases e1
  | true =>
  rw [storeC_typed hty1] at e1
  cases hc1 : checkAccess c loc1 p (T1.size c.space) A1 with
  | error h => rw [hc1] at e1; cases e1
  | ok r =>
  rw [hc1] at e1
  dsimp only [Except.bind] at e1
  cases hm1 : markAll c.tags loc1 r.1 r.2.1 r.2.2 (T1.size c.space) true c.scopes.toList c.marks with
  | error h => rw [hm1] at e1; cases e1
  | ok M1 =>
  rw [hm1] at e1
  cases e1
  cases hty2 : v2.hasTy T2 with
  | false => rw [storeC_ill_typed hty2, storeC_ill_typed hty2]
  | true =>
  rw [storeC_typed hty2, storeC_typed hty2]
  simp only [← hsz]
  -- The second access checks the same things on both cores.
  show (checkAccess c loc2 p (T1.size c.space) A2).bind _ = (checkAccess c loc2 p (T1.size c.space) A2).bind _
  cases hc2 : checkAccess c loc2 p (T1.size c.space) A2 with
  | error h => rfl
  | ok r' =>
  obtain rfl := checkAccess_same hc1 hc2
  dsimp only [Except.bind]
  simp only [written]
  rw [markAll_idem hm1 (nodup_scopes c) |> markAll_loc (loc' := loc2)]
  rw [markAll_loc (loc' := loc2) hm1]
  have hlen : (v1.encode c.space).length = (v2.encode c.space).length := by
    rw [encode_length hty1, encode_length hty2, hsz]
  rw [insert_insert, Std.ExtTreeMap.getD_insert_self, MemRules.writeBytes_writeBytes _ _ _ _ hlen]

/-! ## The rewrite -/

/-- `s1` stores through `%p`, and `s2` stores the same number of bytes through `%p`. The value
`s1` stores must be a variable (deleting a hole would change which hole a run reaches). -/
def Pat (s1 s2 : Op) : Prop :=
  ∃ T1 A1 x1 xp loc1 T2 A2 v2 loc2,
    s1 = .mk (.store T1 A1) [] [.var x1, .var xp] [] loc1 ∧
    s2 = .mk (.store T2 A2) [] [v2, .var xp] [] loc2 ∧
    ∀ cfg, T1.size cfg = T2.size cfg

/-- The rewrite: the target has `[s2]` where the source has `[s1, s2]`. -/
def L (pt ps : List Op) : Prop := ∃ s1 s2, pt = [s2] ∧ ps = [s1, s2] ∧ Pat s1 s2

theorem simpleOp_store (loc : Option Loc) (T : Ty) (A : Nat) (ov op : Operand) (c : Core) :
    simpleOp loc (.store T A) [] [ov, op] c =
      (operandIn c.env loc ov).bind fun v =>
      (operandIn c.env loc op).bind fun pv =>
      match pv with
      | .ptr p => storeC loc T A v p c
      | _ => .error { behavior := .stuck "expected a ptr", loc := loc } := by
  simp only [simpleOp, List.mapM_cons, List.mapM_nil, bind, StateT.bind, pure, StateT.pure,
    Except.bind, evalOperand]
  cases operandIn c.env loc ov with
  | error h => rfl
  | ok v =>
  simp only [Except.map]
  cases operandIn c.env loc op with
  | error h => rfl
  | ok pv =>
  simp only [Except.pure, evalSimple, get, getThe, MonadStateOf.get, StateT.get,
    bind, StateT.bind, pure, StateT.pure, Except.bind]
  cases pv with
  | ptr p =>
    simp only [asPtr, pure, StateT.pure, Except.pure]
    cases storeC loc T A v p c with
    | error h => rfl
    | ok r => rfl
  | _ => rfl

theorem execOp_store (m : Machine) (T : Ty) (A : Nat) (args : List Operand) (loc : Option Loc) :
    execOp m (.mk (.store T A) [] args [] loc) =
      match simpleOp loc (.store T A) [] args m.core with
      | .ok (_, core) => .ok { m with core }
      | .error h => .error h := by
  simp only [execOp, execFlat, OpKind.callee?, OpKind.stackAlloc?, OpKind.isTerminator,
    Machine.exec, StateT.run]
  cases simpleOp loc (.store T A) [] args m.core with
  | error h => rfl
  | ok r => rfl

theorem operandIn_var_error {env : Env} {loc : Option Loc} {x : String} {h : Halt}
    (e : operandIn env loc (.var x) = .error h) : Escape h := by
  simp only [operandIn] at e
  split at e
  · cases e
  · cases e; exact .inl trivial

theorem operandIn_loc {env : Env} {loc loc' : Option Loc} {o : Operand} {v : RVal}
    (e : operandIn env loc o = .ok v) : operandIn env loc' o = .ok v := by
  cases o with
  | var x =>
    simp only [operandIn] at e ⊢
    split at e
    · exact e
    · cases e
  | hole => cases e

theorem storeC_env {loc : Option Loc} {T : Ty} {A : Nat} {v : RVal} {p : Option Ptr} {c c1 : Core}
    (e : storeC loc T A v p c = .ok ((), c1)) : c1.env = c.env := by
  cases p with
  | none => cases e
  | some p =>
    cases hty : v.hasTy T with
    | false => rw [storeC_ill_typed hty] at e; cases e
    | true =>
      rw [storeC_typed hty] at e
      cases hc : checkAccess c loc p (T.size c.space) A with
      | error h => rw [hc] at e; cases e
      | ok r =>
        rw [hc] at e
        dsimp only [Except.bind] at e
        cases hm : markAll c.tags loc r.1 r.2.1 r.2.2 (T.size c.space) true c.scopes.toList c.marks with
        | error h => rw [hm] at e; cases e
        | ok m => rw [hm] at e; cases e; rfl

/-- Running the deleted store either escapes, or leaves a core on which the next store does
exactly what it does without the deleted one. -/
theorem dse_core {loc1 loc2 : Option Loc} {T1 T2 : Ty} {A1 A2 : Nat} {x1 xp : String}
    {v2 : Operand} (hsz : ∀ cfg, T1.size cfg = T2.size cfg) (c : Core) :
    (∃ h, simpleOp loc1 (.store T1 A1) [] [.var x1, .var xp] c = .error h ∧ Escape h) ∨
    (∃ c1, simpleOp loc1 (.store T1 A1) [] [.var x1, .var xp] c = .ok ((), c1) ∧
      simpleOp loc2 (.store T2 A2) [] [v2, .var xp] c1 =
        simpleOp loc2 (.store T2 A2) [] [v2, .var xp] c) := by
  rw [simpleOp_store]
  cases h1 : operandIn c.env loc1 (.var x1) with
  | error h => exact .inl ⟨h, rfl, operandIn_var_error h1⟩
  | ok w1 =>
  cases hp : operandIn c.env loc1 (.var xp) with
  | error h => exact .inl ⟨h, rfl, operandIn_var_error hp⟩
  | ok pv =>
  simp only [Except.bind]
  cases pv with
  | ptr p =>
    simp only
    cases hs : storeC loc1 T1 A1 w1 p c with
    | error h => exact .inl ⟨h, rfl, storeC_error hs⟩
    | ok r =>
      obtain ⟨⟨⟩, c1⟩ := r
      refine .inr ⟨c1, rfl, ?_⟩
      rw [simpleOp_store, simpleOp_store, storeC_env hs, operandIn_loc (loc' := loc2) hp]
      cases operandIn c.env loc2 v2 with
      | error h => rfl
      | ok w2 =>
        simp only [Except.bind]
        cases p with
        | none => rfl
        | some p => exact store_twice hsz hs
  | _ => exact .inl ⟨_, rfl, .inl trivial⟩

/-! ## Steps -/

theorem shape_cons {f f' : Frame} {rt rs : List Frame} (h : f.isProgressLoop = f'.isProgressLoop)
    (hrest : Forall2 (FrameRel L) rt rs) :
    (f :: rt).map Frame.isProgressLoop = (f' :: rs).map Frame.isProgressLoop := by
  simp [h, shape_eq hrest]

/-- At a rewritten spot, the target's one step is matched by the source's two. -/
theorem step_dse {mt ms : Machine} {s1 s2 : Op} {t s : List Op} {ids : List Nat}
    {rt rs : List Frame} (hc : mt.core = ms.core) (hp : Pat s1 s2) (hts : OpsRel L t s)
    (hrest : Forall2 (FrameRel L) rt rs) (ht : mt.stack = .block (s2 :: t) ids :: rt)
    (hs : ms.stack = .block (s1 :: s2 :: s) ids :: rs) : StepMatch (MRel L) mt ms := by
  obtain ⟨T1, A1, x1, xp, loc1, T2, A2, v2, loc2, rfl, rfl, hsz⟩ := hp
  have stepT : step mt = match simpleOp loc2 (.store T2 A2) [] [v2, .var xp] ms.core with
      | .ok (_, core) => .ok { core, stack := .block t ids :: rt }
      | .error h => .error h := by
    simp only [step, ht, execOp_store, hc]
  have stepS1 : step ms = match simpleOp loc1 (.store T1 A1) [] [.var x1, .var xp] ms.core with
      | .ok (_, core) => .ok { core, stack := .block (.mk (.store T2 A2) [] [v2, .var xp] [] loc2 :: s) ids :: rs }
      | .error h => .error h := by
    simp only [step, hs, execOp_store]
  have stepS2 : ∀ c1 : Core,
      step { core := c1, stack := .block (.mk (.store T2 A2) [] [v2, .var xp] [] loc2 :: s) ids :: rs } =
        match simpleOp loc2 (.store T2 A2) [] [v2, .var xp] c1 with
        | .ok (_, core) => .ok { core, stack := .block s ids :: rs }
        | .error h => .error h := by
    intro c1
    simp only [step, execOp_store]
  rcases dse_core (A1 := A1) (A2 := A2) (x1 := x1) (v2 := v2) (loc1 := loc1) (loc2 := loc2) (xp := xp) hsz
    ms.core with ⟨h, e1, hesc⟩ | ⟨c1, e1, e2⟩
  · -- The deleted store fails: the source escapes.
    have esc : Escapes ms := ⟨1, h, by rw [runSteps_one, stepS1, e1], hesc⟩
    exact ⟨fun _ _ => .inl esc, fun _ _ => .inl esc⟩
  have run1 : runSteps 1 ms = .ok {
      core := c1, stack := .block (.mk (.store T2 A2) [] [v2, .var xp] [] loc2 :: s) ids :: rs } := by
    rw [runSteps_one, stepS1, e1]
  have run2 : runSteps 2 ms = match simpleOp loc2 (.store T2 A2) [] [v2, .var xp] ms.core with
      | .ok (_, core) => .ok { core, stack := .block s ids :: rs }
      | .error h => .error h := by
    rw [show 2 = 1 + 1 from rfl, runSteps_add, run1, Except.ok_bind, runSteps_one, stepS2, e2]
  constructor
  · intro mt' e
    rw [stepT] at e
    cases h2 : simpleOp loc2 (.store T2 A2) [] [v2, .var xp] ms.core with
    | error h => rw [h2] at e; cases e
    | ok r =>
      obtain ⟨u, c2⟩ := r
      rw [h2] at e
      cases e
      refine .inr ⟨1, { core := c2, stack := .block s ids :: rs }, by rw [run2, h2],
        MRel.mk' rfl (Forall2.cons' (.block hts) hrest), ?_⟩
      intro j mj hj ej
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
      · simp only [runSteps, Except.ok.injEq] at ej
        subst ej
        simp only [Machine.shape, ht, hs]
        exact (shape_cons rfl hrest).symm
      · rw [run1, Except.ok.injEq] at ej
        subst ej
        simp only [Machine.shape, ht]
        exact (shape_cons rfl hrest).symm
  · intro h e
    rw [stepT] at e
    cases h2 : simpleOp loc2 (.store T2 A2) [] [v2, .var xp] ms.core with
    | ok r => rw [h2] at e; cases e
    | error h' =>
      rw [h2] at e
      cases e
      by_cases hamb : h.behavior = .ambiguous
      · exact .inl ⟨2, h, by rw [run2, h2], .inr hamb⟩
      · exact .inr ⟨2, h, by rw [run2, h2], Behavior.Refines.refl _ hamb⟩

theorem opsRel_cons {ot : Op} {t s0 : List Op} (h : OpsRel L (ot :: t) s0) :
    (∃ os s, s0 = os :: s ∧ OpRel L ot os ∧ OpsRel L t s) ∨
    (∃ s1 s, s0 = s1 :: ot :: s ∧ Pat s1 ot ∧ OpsRel L t s) := by
  generalize hx : ot :: t = x at h
  cases h with
  | refl => subst hx; exact .inl ⟨_, _, rfl, .refl _, .refl _⟩
  | cons ho hr =>
    injection hx with h1 h2
    subst h1 h2
    exact .inl ⟨_, _, rfl, ho, hr⟩
  | rw hl hr =>
    obtain ⟨s1, s2, rfl, rfl, hp⟩ := hl
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact .inr ⟨s1, _, rfl, hp, hr⟩

theorem opsRel_nil {s0 : List Op} (h : OpsRel L [] s0) : s0 = [] := by
  generalize hx : ([] : List Op) = x at h
  cases h with
  | refl => rfl
  | cons => cases hx
  | rw hl _ =>
    obtain ⟨_, _, rfl, _, _⟩ := hl
    cases hx

theorem sim : Simulation (MRel L) := by
  intro mt ms hR
  obtain ⟨hc, hst⟩ := hR
  have lock : (∀ ot t ids rt, mt.stack = .block (ot :: t) ids :: rt →
        ∃ os s rs, ms.stack = .block (os :: s) ids :: rs ∧ OpRel L ot os ∧ OpsRel L t s) →
      (∀ ids rt, mt.stack = .block [] ids :: rt → ∃ rs, ms.stack = .block [] ids :: rs) →
      StepMatch (MRel L) mt ms :=
    fun hh hn => StepMatch.of_lockstep ⟨hc, hst⟩ (step_eq ⟨hc, hst⟩ hh hn)
  cases ht : mt.stack with
  | nil => exact lock (fun _ _ _ _ e => by rw [ht] at e; cases e) (fun _ _ e => by rw [ht] at e; cases e)
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
          rcases opsRel_cons hops with ⟨os, s, rfl, ho, hts⟩ | ⟨s1, s, rfl, hp, hts⟩
          · refine lock (fun ot' t' ids' rt' e => ?_) (fun ids' rt' e => ?_)
            · rw [ht, List.cons.injEq, Frame.block.injEq, List.cons.injEq] at e
              obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := e
              exact ⟨os, s, rs, hs, ho, hts⟩
            · rw [ht] at e; simp at e
          · exact step_dse hc hp hts hrest ht hs
      | loop hb =>
        refine lock (fun _ _ _ _ e => ?_) (fun _ _ e => ?_) <;> (rw [ht] at e; simp at e)

theorem init_match {mod : Module} {tgt src : Func} (hparams : tgt.params = src.params)
    (hrets : tgt.rets = src.rets) (hops : OpsRel L tgt.body.ops src.body.ops)
    (oracle : Nat → Int) (args : List RVal) :
    InitMatch (MRel L) (Machine.init oracle mod tgt args) (Machine.init oracle mod src args) := by
  simp only [Machine.init, hparams, hrets, bind, Except.bind]
  cases (enterCall none src.params args).run (Core.initial oracle mod) with
  | error h =>
    by_cases hamb : h.behavior = .ambiguous
    · exact .inl ⟨h, rfl, .inr hamb⟩
    · exact .inr (.inr ⟨h, h, rfl, rfl, Behavior.Refines.refl _ hamb⟩)
  | ok r =>
    exact .inr (.inl ⟨_, _, rfl, rfl, MRel.mk' rfl
      (Forall2.cons' (.block hops) (Forall2.cons' (.refl _) trivial))⟩)

/-- **Dead store elimination is correct.** Deleting, anywhere in a function, a store that is
immediately followed by a store of the same size through the same pointer gives a function that
refines the original, for every argument and every oracle. -/
theorem refines {mod : Module} {tgt src : Func} (hparams : tgt.params = src.params)
    (hrets : tgt.rets = src.rets) (hops : OpsRel L tgt.body.ops src.body.ops)
    (dec : src.Decided mod) : tgt.Refines mod src :=
  Simulation.refines sim (fun oracle args => ⟨oracle, init_match hparams hrets hops oracle args⟩) dec

end Fir.Dse
