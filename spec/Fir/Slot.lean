import Fir.Fwd

/-!
# A slot's memory: what loads and stores through its own pointer do

Promoting a stack slot to values (`mem2reg`, not proved yet: `docs/design/06-plan.md`) rests on
four facts. Three of them are about single ops and are proved here; they are the leaves of the
simulation still to be written.

1. *Nothing else reaches the slot's bytes.* Not here: it is an invariant of whole runs (the
   pointer never escapes, so no other op, callee, or external function holds it).
2. *A field's load reads the last value stored to it* (`load_tracked`, `store_tracked`), and a
   store to one field leaves the others as they were (`store_keeps`). So does a store through
   a pointer into another allocation (`store_elsewhere`), and so does every load
   (`load_keeps`).
3. *Before any store, a field holds `poison`* (`fresh_tracks`): fresh bytes are the encoding of
   the value the `poison` op gives.

The facts hold for an allocation no active `noalias` or `readonly` scope watches (`Quiet`): an
access to it then records nothing, so a load leaves the core exactly as it was and a store
changes the allocation's bytes only. A slot whose pointer is never passed to a call has no
scope (scopes open on a call's pointer arguments, and on `const` globals); that it stays so is
part of fact 1.

A field is *tracked* at `v` when its bytes are `v`'s encoding:
`readBytes (c.mem.getD a ∅) off (T.size c.space) = v.encode c.space`. The three theorems say
how each op moves that equation: a fresh slot starts it at `poison`, a store sets it, and a load
reads it back without changing anything.
-/

namespace Fir.Slot

open Dse (Escape)

/-- No active `noalias` or `readonly` scope watches allocation `a`. -/
def Quiet (a : Nat) (c : Core) : Prop := ∀ p ∈ c.scopes.toList, p.2.alloc ≠ a

/-- The types of a promoted field: scalars that come back from memory unchanged (`Fwd.Exact`)
and whose unwritten bytes read as `poison`. That leaves out `bN`, whose loads keep each
`poison` byte as it is. -/
def Field : Ty → Prop
  | .int w => w % 8 = 0 ∧ 0 < w
  | .ptr | .float _ => True
  | _ => False

theorem Field.exact {T : Ty} (h : Field T) : Fwd.Exact T := by
  cases T <;> simp_all [Field, Fwd.Exact]

/-! ## Accesses to a quiet allocation -/

/-- An access to an allocation no scope watches records nothing. -/
theorem markAll_quiet {tags : Std.ExtTreeMap Nat (Option Nat)} {loc : Option Loc}
    {a t off n : Nat} {w : Bool} :
    ∀ {L : List (Nat × Scope)} {mm : Std.ExtTreeMap Nat Marks},
      (∀ p ∈ L, p.2.alloc ≠ a) → markAll tags loc a t off n w L mm = .ok mm
  | [], _, _ => rfl
  | (id, s) :: rest, mm, h => by
    have hs : (s.alloc != a) = true := by
      simpa [bne_iff_ne] using h (id, s) (by simp)
    simp only [markAll, hs, ↓reduceIte]
    exact markAll_quiet fun p hp => h p (by simp [hp])

/-- A checked access through a pointer into an allocation goes to that allocation, at the
pointer's offset. -/
theorem checkAccess_rel {c : Core} {loc : Option Loc} {a t : Nat} {off : Int} {n A : Nat}
    {r : Nat × Nat × Nat} (e : checkAccess c loc (.rel a t off) n A = .ok r) :
    r = (a, t, off.toNat) := by
  obtain ⟨o, h1, h2⟩ := Dse.checkAccess_ok e
  simp only [resolveIn, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨ha, ht, ho⟩ := h1
  obtain ⟨a', t', off'⟩ := r
  simp only at ha ht h2
  subst ha ht ho h2
  rfl

/-- An access to a quiet allocation checks the pointer and leaves the core as it was. -/
theorem access_quiet {c : Core} {loc : Option Loc} {a t : Nat} {off : Int} {n A : Nat}
    {w : Bool} (hq : Quiet a c) :
    access loc (.rel a t off) n A w c =
      (checkAccess c loc (.rel a t off) n A).bind fun _ => .ok ((a, off.toNat), c) := by
  rw [Fwd.access_eq]
  cases hc : checkAccess c loc (.rel a t off) n A with
  | error h => rfl
  | ok r =>
    obtain rfl := checkAccess_rel hc
    simp only [Except.bind, markAll_quiet hq]

/-! ## Loads -/

/-- **A load of a tracked field reads the tracked value and changes nothing.** Through a
pointer into a quiet allocation whose bytes at the pointer's offset are the encoding of `v`, a
load of `v`'s type either is UB (the slot is dead, or the access is out of bounds or misaligned)
or gives `v` and leaves the core exactly as it was. -/
theorem load_tracked {loc : Option Loc} {T : Ty} {A a t : Nat} {off : Int} {c : Core} {v : RVal}
    (hT : Fwd.Exact T) (hv : v.hasTy T = true) (hsp : 0 < c.space.ptrBits / 8) (hq : Quiet a c)
    (hb : readBytes (c.mem.getD a ∅) off.toNat (T.size c.space) = v.encode c.space) :
    (∃ h, loadC loc T A (some (.rel a t off)) c = .error h ∧ Escape h) ∨
    loadC loc T A (some (.rel a t off)) c = .ok (v, c) := by
  rw [Fwd.loadC_some, access_quiet hq]
  cases hc : checkAccess c loc (.rel a t off) (T.size c.space) A with
  | error h => exact .inl ⟨h, rfl, Dse.checkAccess_error hc⟩
  | ok r =>
    right
    simp only [Except.bind, hb]
    exact Fwd.decodeAs_encode hv hT rfl hsp

/-- `load_tracked` for the op: the load does what a copy of the tracked value does, or is UB. -/
theorem load_tracked_op {loc : Option Loc} {r : Result} {A a t : Nat} {off : Int} {c : Core}
    {v : RVal} (hT : Fwd.Exact r.ty) (hv : v.hasTy r.ty = true) (hsp : 0 < c.space.ptrBits / 8)
    (hq : Quiet a c)
    (hb : readBytes (c.mem.getD a ∅) off.toNat (r.ty.size c.space) = v.encode c.space) :
    (∃ h, evalSimple loc (.load A) [r] [.ptr (some (.rel a t off))] c = .error h ∧ Escape h) ∨
    evalSimple loc (.load A) [r] [.ptr (some (.rel a t off))] c =
      evalSimple loc .copy [r] [v] c := by
  rw [Fwd.evalSimple_load _ _ _ _ _ hT.isValue, Fwd.evalSimple_copy]
  rcases load_tracked (loc := loc) (A := A) (t := t) hT hv hsp hq hb with ⟨h, e, hesc⟩ | e
  · exact .inl ⟨h, by rw [e]; rfl, hesc⟩
  · exact .inr (by rw [e]; rfl)

/-! ## Stores -/

/-- The core after a store of `bs` at `off` in allocation `a`, when no scope watches `a`: only
`a`'s bytes change. -/
def stored (c : Core) (a off : Nat) (bs : List Byte) : Core :=
  { c with mem := c.mem.insert a (writeBytes (c.mem.getD a ∅) off bs) }

/-- A store to a quiet allocation changes that allocation's bytes and nothing else. -/
theorem store_quiet {loc : Option Loc} {T : Ty} {A a t : Nat} {off : Int} {c c' : Core}
    {v : RVal} (hq : Quiet a c)
    (e : storeC loc T A v (some (.rel a t off)) c = .ok ((), c')) :
    v.hasTy T = true ∧ c' = stored c a off.toNat (v.encode c.space) := by
  cases hty : v.hasTy T with
  | false => rw [Dse.storeC_ill_typed hty] at e; cases e
  | true =>
    rw [Dse.storeC_typed' hty] at e
    cases hc : checkAccess c loc (.rel a t off) (v.encode c.space).length A with
    | error h => rw [hc] at e; cases e
    | ok r =>
      obtain rfl := checkAccess_rel hc
      rw [hc] at e
      simp only [Except.bind, markAll_quiet hq, Except.ok.injEq, Prod.mk.injEq, true_and] at e
      exact ⟨rfl, e.symm⟩

/-- **A store makes the field hold the stored value.** After a store of `v` at type `T` through
a pointer into a quiet allocation, the bytes at the pointer's offset are `v`'s encoding, the
allocation is still quiet, and the memory space is the same. -/
theorem store_tracked {loc : Option Loc} {T : Ty} {A a t : Nat} {off : Int} {c c' : Core}
    {v : RVal} (hT : T.isValue = true) (hq : Quiet a c)
    (e : storeC loc T A v (some (.rel a t off)) c = .ok ((), c')) :
    v.hasTy T = true ∧
    readBytes (c'.mem.getD a ∅) off.toNat (T.size c'.space) = v.encode c'.space ∧
    Quiet a c' ∧ c'.space = c.space := by
  obtain ⟨hty, rfl⟩ := store_quiet hq e
  refine ⟨hty, ?_, hq, rfl⟩
  simp only [stored, Std.ExtTreeMap.getD_insert_self, ← Dse.encode_length hty hT c.space,
    MemRules.read_write_same]

/-- A store to one field leaves the bytes of every range it doesn't overlap as they were. -/
theorem store_keeps {loc : Option Loc} {T : Ty} {A a t : Nat} {off : Int} {c c' : Core}
    {v : RVal} (hT : T.isValue = true) (hq : Quiet a c)
    (e : storeC loc T A v (some (.rel a t off)) c = .ok ((), c')) (off' n : Nat)
    (h : off' + n ≤ off.toNat ∨ off.toNat + T.size c.space ≤ off') :
    readBytes (c'.mem.getD a ∅) off' n = readBytes (c.mem.getD a ∅) off' n := by
  obtain ⟨hty, rfl⟩ := store_quiet hq e
  simp only [stored, Std.ExtTreeMap.getD_insert_self]
  exact MemRules.read_write_disjoint _ _ _ _ _ (by rw [Dse.encode_length hty hT]; exact h)

/-- A store that goes to another allocation leaves this one's bytes, the scopes, and the
memory space as they were. `p` is any pointer, a bare address included: what matters is the
allocation the access resolves to. -/
theorem store_elsewhere {loc : Option Loc} {T : Ty} {A a : Nat} {p : Ptr} {c c' : Core}
    {v : RVal}
    (hp : ∀ n r, checkAccess c loc p n A = .ok r → r.1 ≠ a)
    (e : storeC loc T A v (some p) c = .ok ((), c')) :
    c'.mem.getD a ∅ = c.mem.getD a ∅ ∧ c'.scopes = c.scopes ∧ c'.space = c.space := by
  cases hty : v.hasTy T with
  | false => rw [Dse.storeC_ill_typed hty] at e; cases e
  | true =>
    rw [Dse.storeC_typed' hty] at e
    cases hc : checkAccess c loc p (v.encode c.space).length A with
    | error h => rw [hc] at e; cases e
    | ok r =>
      rw [hc] at e
      dsimp only [Except.bind] at e
      cases hm : markAll c.tags loc r.1 r.2.1 r.2.2 (v.encode c.space).length true
          c.scopes.toList c.marks with
      | error h => rw [hm] at e; cases e
      | ok M =>
        rw [hm] at e
        cases e
        refine ⟨?_, rfl, rfl⟩
        simp only [Dse.written]
        rw [Std.ExtTreeMap.getD_insert,
          ite_eq_right fun h => absurd (Nat.compare_eq_eq.mp h) (hp _ _ hc)]

/-! ## Loads change no memory -/

section
variable {v : Std.ExtTreeMap Nat Bytes × Std.ExtTreeMap Nat Scope × SpaceCfg}

/-- What no load changes: every allocation's bytes, the scopes, and the memory space. (A load
does change the core: it records the access in the scopes' marks, and reading a pointer's bytes
as an integer exposes the pointer.) -/
abbrev Core.held (c : Core) : Std.ExtTreeMap Nat Bytes × Std.ExtTreeMap Nat Scope × SpaceCfg :=
  (c.mem, c.scopes, c.space)

theorem held_choose : Keeps Core.held v choose := by unfold choose; keeps

theorem held_getAlloc (loc : Option Loc) (a : Nat) : Keeps Core.held v (getAlloc loc a) := by
  unfold getAlloc; keeps

theorem held_setAlloc (a : Nat) (al : Alloc) : Keeps Core.held v (setAlloc a al) := by
  unfold setAlloc; keeps

theorem held_realize (loc : Option Loc) (a : Nat) : Keeps Core.held v (realize loc a) := by
  unfold realize
  repeat' first
    | with_reducible exact held_choose
    | with_reducible apply held_getAlloc
    | with_reducible apply held_setAlloc
    | keeps

theorem held_ptrAddr (loc : Option Loc) (p : Ptr) : Keeps Core.held v (ptrAddr loc p) := by
  unfold ptrAddr
  repeat' first
    | with_reducible apply held_realize
    | keeps

theorem held_ptrExpose (loc : Option Loc) (p : Ptr) : Keeps Core.held v (ptrExpose loc p) := by
  unfold ptrExpose
  repeat' first
    | with_reducible apply held_ptrAddr
    | with_reducible apply held_getAlloc
    | with_reducible apply held_setAlloc
    | keeps

theorem held_fromExposed (n : Nat) : Keeps Core.held v (fromExposed n) := by
  unfold fromExposed; keeps

theorem held_access (loc : Option Loc) (p : Ptr) (n A : Nat) (w : Bool) :
    Keeps Core.held v (access loc p n A w) := by
  intro c r hc e
  simp only [access, bind, Except.bind, pure, Except.pure] at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e; exact hc

theorem held_fragToBits (loc : Option Loc) (b : Byte) : Keeps Core.held v (fragToBits loc b) := by
  unfold fragToBits
  repeat' first
    | with_reducible apply held_ptrExpose
    | keeps

theorem held_decodeAs (loc : Option Loc) (T : Ty) (bs : List Byte) :
    Keeps Core.held v (decodeAs loc T bs) := by
  unfold decodeAs
  repeat' first
    | with_reducible apply held_fragToBits
    | with_reducible apply held_fromExposed
    | keeps

/-- A scalar load changes no allocation's bytes, no scope, and not the memory space. -/
theorem held_loadC (loc : Option Loc) (T : Ty) (A : Nat) (p : Option Ptr) :
    Keeps Core.held v (loadC loc T A p) := by
  unfold loadC
  repeat' first
    | with_reducible apply held_access
    | with_reducible apply held_decodeAs
    | keeps

end

/-- **No load changes a slot.** A scalar load through any pointer leaves every allocation's
bytes as they were, and with them every tracked field; the scopes and the memory space stay
too, so a quiet allocation stays quiet. -/
theorem load_keeps {loc : Option Loc} {T : Ty} {A : Nat} {p : Option Ptr} {c c' : Core}
    {out : RVal} (e : loadC loc T A p c = .ok (out, c')) :
    c'.mem = c.mem ∧ c'.scopes = c.scopes ∧ c'.space = c.space := by
  have h := held_loadC (v := Core.held c) loc T A p c (out, c') rfl e
  simp only [Core.held, Prod.mk.injEq] at h
  exact h

/-! ## A fresh slot -/

/-- **A fresh slot holds `poison`.** At a field type, the `poison` op gives one value of that
type and leaves the core alone, and that value's encoding is what fresh bytes read as. So a
field nothing was stored to is tracked at `poison`. -/
theorem fresh_tracks {loc : Option Loc} {r : Result} {c c' : Core} {vs : List RVal}
    (hT : Field r.ty) (e : evalSimple loc .poison [r] [] c = .ok (vs, c')) (off : Nat) :
    ∃ v, vs = [v] ∧ c' = c ∧ v.hasTy r.ty = true ∧
      readBytes ∅ off (r.ty.size c.space) = v.encode c.space := by
  rw [MemRules.read_fresh]
  cases hty : r.ty with
  | int w =>
    simp only [evalSimple, hty, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨_, rfl, rfl, by simp [RVal.hasTy, Ty.width], by simp [RVal.encode, encodeInt, Ty.size, Ty.width]⟩
  | ptr =>
    simp only [evalSimple, hty, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨_, rfl, rfl, rfl, by simp [RVal.encode, encodePtr, Ty.size]⟩
  | float f =>
    simp only [evalSimple, hty, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨_, rfl, rfl, by simp [RVal.hasTy], by simp [RVal.encode, encodeInt, Ty.size]⟩
  | _ => rw [hty] at hT; exact absurd hT (by simp [Field])

end Fir.Slot
