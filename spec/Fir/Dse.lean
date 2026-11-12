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
def Escape (h : Halt) : Prop := h.outcome.Absorbing ∨ h.outcome = .ambiguous

theorem halt_error {b : Outcome} {loc : Option Loc} {note : String} {h : Halt}
    (e : (halt b loc note : Except Halt α) = .error h) : h.outcome = b := by
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

/-- A value of a scalar type `T` takes `T.size` bytes. -/
theorem encode_length {v : RVal} {T : Ty} (h : v.hasTy T = true) (hT : T.isValue = true)
    (cfg : SpaceCfg) : (v.encode cfg).length = T.size cfg := by
  cases v with
  | agg vs => cases T <;> simp [Ty.isValue, RVal.hasTy] at hT h
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
      .error { outcome := .ub .poison, loc := loc, note := "store through a poison pointer" } :=
  rfl

theorem storeC_ill_typed {loc : Option Loc} {T : Ty} {A : Nat} {v : RVal} {p : Ptr} {c : Core}
    (h : v.hasTy T = false) :
    storeC loc T A v (some p) c =
      .error { outcome := .stuck s!"the stored value isn't a {T}", loc := loc } := by
  simp [storeC, h, halt, throw, throwThe, MonadExcept.throw, bind, Except.bind]
  rfl

/-- The core after a store's write. -/
def written (c : Core) (marks : Std.ExtTreeMap Nat Marks) (a off : Nat) (bs : List Byte) : Core :=
  { c with marks := marks, mem := c.mem.insert a (writeBytes (c.mem.getD a ∅) off bs) }

/-- A store of a value of the right type: check the access, record it in the scopes, write. -/
theorem storeC_typed' {loc : Option Loc} {T : Ty} {A : Nat} {v : RVal} {p : Ptr} {c : Core}
    (h : v.hasTy T = true) :
    storeC loc T A v (some p) c =
      (checkAccess c loc p (v.encode c.space).length A).bind fun r =>
      (markAll c.tags loc r.1 r.2.1 r.2.2 (v.encode c.space).length true c.scopes.toList
        c.marks).bind fun marks => .ok ((), written c marks r.1 r.2.2 (v.encode c.space)) := by
  simp only [storeC, h, access, ↓reduceIte]
  cases checkAccess c loc p (v.encode c.space).length A with
  | error e => rfl
  | ok r =>
    simp only [bind, Except.bind, pure, Except.pure]
    cases markAll c.tags loc r.1 r.2.1 r.2.2 (v.encode c.space).length true c.scopes.toList
      c.marks with
    | error e => rfl
    | ok m => rfl

/-- A store of a value of the right scalar type writes `T.size` bytes. -/
theorem storeC_typed {loc : Option Loc} {T : Ty} {A : Nat} {v : RVal} {p : Ptr} {c : Core}
    (h : v.hasTy T = true) (hT : T.isValue = true) :
    storeC loc T A v (some p) c =
      (checkAccess c loc p (T.size c.space) A).bind fun r =>
      (markAll c.tags loc r.1 r.2.1 r.2.2 (T.size c.space) true c.scopes.toList c.marks).bind
        fun marks => .ok ((), written c marks r.1 r.2.2 (v.encode c.space)) := by
  rw [storeC_typed' h, encode_length h hT]

theorem storeC_error {loc : Option Loc} {T : Ty} {A : Nat} {v : RVal} {p : Option Ptr} {c : Core}
    {h : Halt} (e : storeC loc T A v p c = .error h) : Escape h := by
  cases p with
  | none => rw [storeC_none] at e; cases e; exact .inl trivial
  | some p =>
    cases hty : v.hasTy T with
    | false => rw [storeC_ill_typed hty] at e; cases e; exact .inl trivial
    | true =>
      rw [storeC_typed' hty] at e
      cases hc : checkAccess c loc p (v.encode c.space).length A with
      | error h' => rw [hc] at e; cases e; exact checkAccess_error hc
      | ok r =>
        rw [hc] at e
        dsimp only [Except.bind] at e
        cases hm : markAll c.tags loc r.1 r.2.1 r.2.2 (v.encode c.space).length true
            c.scopes.toList c.marks with
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
    {p : Ptr} {c c1 : Core} (hsz : ∀ cfg, T1.size cfg = T2.size cfg) (hT1 : T1.isValue = true)
    (hT2 : T2.isValue = true)
    (e1 : storeC loc1 T1 A1 v1 (some p) c = .ok ((), c1)) :
    storeC loc2 T2 A2 v2 (some p) c1 = storeC loc2 T2 A2 v2 (some p) c := by
  cases hty1 : v1.hasTy T1 with
  | false => rw [storeC_ill_typed hty1] at e1; cases e1
  | true =>
  rw [storeC_typed hty1 hT1] at e1
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
  rw [storeC_typed hty2 hT2, storeC_typed hty2 hT2]
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
    rw [encode_length hty1 hT1, encode_length hty2 hT2, hsz]
  rw [insert_insert, Std.ExtTreeMap.getD_insert_self, MemRules.writeBytes_writeBytes _ _ _ _ hlen]

/-! ## The rewrite -/

/-- `s1` stores through `%p`, and `s2` stores the same number of bytes through `%p`, both of
scalar types (an aggregate store writes only its leaves, so it doesn't hide an earlier store's
bytes under its padding). The value `s1` stores must be a variable (deleting a hole would change
which hole a run reaches). -/
def Pat (s1 s2 : Op) : Prop :=
  ∃ T1 A1 x1 xp loc1 T2 A2 v2 loc2,
    s1 = .mk (.store T1 A1) [] [.var x1, .var xp] [] loc1 ∧
    s2 = .mk (.store T2 A2) [] [v2, .var xp] [] loc2 ∧
    (∀ cfg, T1.size cfg = T2.size cfg) ∧ T1.isValue = true ∧ T2.isValue = true

/-- The rewrite: the target has `[s2]` where the source has `[s1, s2]`. -/
def L (pt ps _ : List Op) : Prop := ∃ s1 s2, pt = [s2] ∧ ps = [s1, s2] ∧ Pat s1 s2

theorem checkResults_nil (loc : Option Loc) (vs : List RVal) (c : Core) :
    checkResults loc [] vs c =
      match vs with
      | [] => .ok ((), c)
      | _ => .error { outcome := .stuck "wrong number of values", loc := loc } := by
  cases vs <;> rfl

/-- A store of a scalar type is `storeC`. -/
theorem storeAny_value {loc : Option Loc} {T : Ty} {A : Nat} {v : RVal} {p : Option Ptr}
    (hT : T.isValue = true) : storeAny loc T A v p = storeC loc T A v p := by
  simp [storeAny, hT]

theorem simpleOp_store (loc : Option Loc) (T : Ty) (A : Nat) (v pv : RVal) (c : Core)
    (hT : T.isValue = true) :
    simpleOp loc (.store T A) [] [v, pv] c =
      match pv with
      | .ptr p => (storeC loc T A v p c).bind fun r => .ok ([], r.2)
      | _ => .error { outcome := .stuck "expected a ptr", loc := loc } := by
  simp only [simpleOp, evalSimple, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind,
    pure, StateT.pure, Except.bind]
  cases pv with
  | ptr p =>
    simp only [asPtr, pure, StateT.pure, Except.pure, storeAny_value hT]
    cases storeC loc T A v p c with
    | error h => rfl
    | ok r => rfl
  | _ => rfl

/-- Running the deleted store either escapes, or leaves a core on which the next store does
exactly what it does without the deleted one. -/
theorem dse_core {loc1 loc2 : Option Loc} {T1 T2 : Ty} {A1 A2 : Nat}
    (hsz : ∀ cfg, T1.size cfg = T2.size cfg) (hT1 : T1.isValue = true) (hT2 : T2.isValue = true)
    (w1 pv : RVal) (c : Core) :
    (∃ h, simpleOp loc1 (.store T1 A1) [] [w1, pv] c = .error h ∧ Escape h) ∨
    (∃ c1, simpleOp loc1 (.store T1 A1) [] [w1, pv] c = .ok ([], c1) ∧
      ∀ w2, simpleOp loc2 (.store T2 A2) [] [w2, pv] c1 =
        simpleOp loc2 (.store T2 A2) [] [w2, pv] c) := by
  rw [simpleOp_store _ _ _ _ _ _ hT1]
  cases pv with
  | ptr p =>
    simp only
    cases hs : storeC loc1 T1 A1 w1 p c with
    | error h => exact .inl ⟨h, rfl, storeC_error hs⟩
    | ok r =>
      obtain ⟨⟨⟩, c1⟩ := r
      refine .inr ⟨c1, rfl, fun w2 => ?_⟩
      rw [simpleOp_store _ _ _ _ _ _ hT2, simpleOp_store _ _ _ _ _ _ hT2]
      cases p with
      | none => rfl
      | some p => simp only [store_twice hsz hT1 hT2 hs]
  | _ => exact .inl ⟨_, rfl, .inl trivial⟩

/-! ## Steps -/

/-- At a rewritten spot, the source runs the deleted store, then the target's one step is
matched by the source's next. -/
theorem step_dse {mt ms : Machine} {s1 s2 : Op} {t s : List Op} {ids : List Nat}
    {et es : Env} {ft fs : List Frame} {D Db : String → Prop} (hc : mt.core = ms.core)
    (hp : Pat s1 s2) (hts : OpsRel L t s) (hb : StackRel L Db ft fs) (hDb : ∀ n, Db n → D n)
    (hag : EnvAgree D et es) (hnr : NoReads D ([s2] ++ t))
    (ht : mt.stack = .block ([s2] ++ t) ids et :: ft)
    (hs : ms.stack = .block ([s1, s2] ++ s) ids es :: fs) : StepMatch (MRel L) mt ms := by
  obtain ⟨T1, A1, x1, xp, loc1, T2, A2, v2, loc2, rfl, rfl, hsz, hT1, hT2⟩ := hp
  obtain ⟨c, stt⟩ := mt
  obtain ⟨cs, sts⟩ := ms
  dsimp only at hc ht hs
  subst hc ht hs
  obtain ⟨hr2, hnr'⟩ := NoReads.cons hnr
  have rel : StackRel L D (.block t ids et :: ft) (.block s ids es :: fs) :=
    .block hb hDb hts hag hnr'
  have hargs := (Op.reads_mk hr2).1
  -- The source runs the deleted store.
  have step1 := step_simple (c := c) (k := .store T1 A1) (res := []) (args := [.var x1, .var xp])
    (loc := loc1) (t := .mk (.store T2 A2) [] [v2, .var xp] [] loc2 :: s) (ids := ids) (env := es)
    (fs := fs) rfl rfl rfl
  simp only [List.cons_append, List.nil_append, bindTop_nil] at step1 ⊢
  rw [operands_ops _ s] at step1
  cases hx1 : operandIn (.block s ids es :: fs) loc1 (.var x1) with
  | error h =>
    have esc : Escapes c.trace ⟨c, _⟩ := Escapes.one (by
      rw [runSteps_one, step1, operands_pair, hx1]; rfl) (.inl (operandIn_var_error hx1))
      (Events.Refines.refl _)
    exact ⟨fun _ _ => .inl esc, fun _ _ => .inl esc⟩
  | ok w1 =>
  cases hxp : operandIn (.block s ids es :: fs) loc1 (.var xp) with
  | error h =>
    have esc : Escapes c.trace ⟨c, _⟩ := Escapes.one (by
      rw [runSteps_one, step1, operands_pair, hx1, hxp]; rfl) (.inl (operandIn_var_error hxp))
      (Events.Refines.refl _)
    exact ⟨fun _ _ => .inl esc, fun _ _ => .inl esc⟩
  | ok pv =>
  rw [operands_pair, hx1, hxp] at step1
  simp only [Except.bind] at step1
  rcases dse_core (loc2 := loc2) (A2 := A2) hsz hT1 hT2 w1 pv c with ⟨h, e1, hesc⟩ | ⟨c1, e1, e2⟩
  · have esc : Escapes c.trace ⟨c, _⟩ :=
      Escapes.one (by rw [runSteps_one, step1, e1]) hesc (Events.Refines.refl _)
    exact ⟨fun _ _ => .inl esc, fun _ _ => .inl esc⟩
  rw [e1] at step1
  refine StepMatch.prepend step1 ?_ ?_
  · simp only [Machine.shape]
    exact (shape_cons rfl hb).symm
  -- Then both run the second store, with the same operands, to the same core.
  have hxp2 : operandIn (.block s ids es :: fs) loc2 (.var xp) = .ok pv := operandIn_loc hxp
  refine step_same
    (x := (operands (.block s ids es :: fs) loc2 [v2, .var xp]).bind fun vs =>
      simpleOp loc2 (.store T2 A2) [] vs c)
    (ft := fun outs core => ⟨core, bindTop [] outs (.block t ids et :: ft)⟩)
    (fs := fun outs core => ⟨core, bindTop [] outs (.block s ids es :: fs)⟩) ?_ ?_ ?_ ?_ ?_
  · rw [step_simple rfl rfl rfl, rel.operands loc2 hargs]
  · rw [step_simple rfl rfl rfl]
    congr 1
    refine Except.bind_congr fun vs e => ?_
    rw [operands_pair, hxp2] at e
    cases hv : operandIn (.block s ids es :: fs) loc2 v2 with
    | error h => rw [hv] at e; cases e
    | ok w2 => rw [hv] at e; cases e; exact e2 w2
  · simp only [Machine.shape]
    exact (shape_cons rfl hb).symm
  · -- The deleted store left the trace alone.
    have hk := keeps_simpleOp (sp := c.fixed) loc1 (.store T1 A1) [] [w1, pv] c _ rfl e1
    simp only [Core.fixed, Prod.mk.injEq] at hk
    simp only [hk.2]
    exact Events.Refines.refl _
  · intro _ core _
    exact ⟨rfl, D, rel.bindTop _ _⟩

theorem sim : Simulation (MRel L) := by
  intro mt ms hR
  refine StepMatch.of_mrel hR (fun _ _ _ _ h => h) ?_
  intro D Db pt ps t s ids et es ft fs hl hts hb hDb hag hnr ht hs
  obtain ⟨s1, s2, rfl, rfl, hp⟩ := hl
  exact step_dse hR.1 hp hts hb hDb hag hnr ht hs

/-- **Dead store elimination is correct.** Deleting, anywhere in a function, a store that is
immediately followed by a store of the same size through the same pointer gives a function that
refines the original, for every argument and every oracle. -/
theorem refines {mod : Module} {tgt src : Func} (hparams : tgt.params = src.params)
    (hrets : tgt.rets = src.rets) (hops : OpsRel L tgt.body.ops src.body.ops)
    (dec : src.Decided mod) : tgt.Refines mod src :=
  Simulation.refines sim (fun _ _ h => by rw [h.1]; exact Events.Refines.refl _)
    (fun oracle world args => ⟨oracle, InitMatch.of_lockstep
      (init_lockstep hparams hrets hops oracle world args) fun _ _ h => h⟩) dec

end Fir.Dse
