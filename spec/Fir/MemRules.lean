import Fir.Mem
import Fir.Refinement

/-!
# Memory lemmas

The facts about memory that the memory optimizations rest on:

* reading back what was just written gives it back (store-to-load forwarding);
* a write doesn't change bytes outside its range (reordering independent accesses);
* a second write to the same bytes hides the first (dead store elimination);
* fresh memory reads as `poison`.
-/

namespace Fir.MemRules

theorem getD_writeBytes (m : Bytes) (off i : Nat) (bs : List Byte) (d : Byte) :
    (writeBytes m off bs).getD i d =
      if off ≤ i ∧ i < off + bs.length then bs.getD (i - off) d else m.getD i d := by
  induction bs generalizing m off with
  | nil => simp only [writeBytes, List.length_nil]; rw [ite_eq_right (by omega)]
  | cons b bs ih =>
    rw [writeBytes, ih]
    simp only [Std.ExtTreeMap.getD_insert, Nat.compare_eq_eq, List.length_cons]
    by_cases h1 : off + 1 ≤ i ∧ i < off + 1 + bs.length
    · rw [ite_eq_left h1, ite_eq_left (by omega), show i - off = (i - (off + 1)) + 1 by omega]
      simp
    · rw [ite_eq_right h1]
      by_cases h2 : off = i
      · subst h2; simp
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem getElem?_writeBytes (m : Bytes) (off i : Nat) (bs : List Byte) :
    (writeBytes m off bs)[i]? = if off ≤ i ∧ i < off + bs.length then bs[i - off]? else m[i]? := by
  induction bs generalizing m off with
  | nil => simp only [writeBytes, List.length_nil]; rw [ite_eq_right (by omega)]
  | cons b bs ih =>
    rw [writeBytes, ih]
    simp only [Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, List.length_cons]
    by_cases h1 : off + 1 ≤ i ∧ i < off + 1 + bs.length
    · rw [ite_eq_left h1, ite_eq_left (by omega), show i - off = (i - (off + 1)) + 1 by omega]
      simp
    · rw [ite_eq_right h1]
      by_cases h2 : off = i
      · subst h2; simp
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- A second write of the same length to the same place leaves memory exactly as if only the
second write happened. (The read-level version is `write_write_same`.) -/
theorem writeBytes_writeBytes (m : Bytes) (off : Nat) (bs bs' : List Byte)
    (h : bs.length = bs'.length) :
    writeBytes (writeBytes m off bs) off bs' = writeBytes m off bs' := by
  apply Std.ExtTreeMap.ext_getElem?
  intro i
  simp only [getElem?_writeBytes, h]
  split <;> simp

/-- Reading back what was just written gives it back. -/
theorem read_write_same (m : Bytes) (off : Nat) (bs : List Byte) :
    readBytes (writeBytes m off bs) off bs.length = bs := by
  apply List.ext_getElem (by simp [readBytes])
  intro i _ h₂
  simp only [readBytes, List.getElem_map, List.getElem_range, getD_writeBytes]
  rw [ite_eq_left (by omega)]
  simp [List.getD_eq_getElem?_getD, h₂]

/-- A write doesn't change bytes outside its range. -/
theorem read_write_disjoint (m : Bytes) (off off' n : Nat) (bs : List Byte)
    (h : off' + n ≤ off ∨ off + bs.length ≤ off') :
    readBytes (writeBytes m off bs) off' n = readBytes m off' n := by
  apply List.ext_getElem (by simp [readBytes])
  intro i h₁ _
  have hi : i < n := by simpa [readBytes] using h₁
  simp only [readBytes, List.getElem_map, List.getElem_range, getD_writeBytes]
  rw [ite_eq_right (by omega)]

/-- A second write to the same bytes hides the first: every read sees the same bytes as if only
the second write happened. -/
theorem write_write_same (m : Bytes) (off off' n : Nat) (bs bs' : List Byte)
    (h : bs.length = bs'.length) :
    readBytes (writeBytes (writeBytes m off bs) off bs') off' n =
      readBytes (writeBytes m off bs') off' n := by
  rw [writeBytes_writeBytes m off bs bs' h]

/-- Fresh memory reads as `poison`. -/
theorem read_fresh (off n : Nat) : readBytes ∅ off n = List.replicate n .poison := by
  apply List.ext_getElem (by simp [readBytes])
  intro i _ _
  simp [readBytes, Std.ExtTreeMap.getD_empty]

theorem undigits_digits (k n : Nat) : undigits (digits k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [digits, undigits, Nat.mod_one]
  | succ k ih =>
    simp only [digits, undigits, ih, Nat.pow_succ', Nat.mod_mul]

theorem digits_lt (k n : Nat) : ∀ d ∈ digits k n, d < 256 := by
  induction k generalizing n with
  | zero => simp [digits]
  | succ k ih =>
    intro d hd
    simp only [digits, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ (by decide)
    · exact ih _ d hd

theorem map_mod_digits (k n : Nat) : (digits k n).map (fun x => x % 256) = digits k n := by
  conv => rhs; rw [← List.map_id (digits k n)]
  apply List.map_congr_left
  intro d hd
  exact Nat.mod_eq_of_lt (digits_lt _ _ d hd)

/-- An integer stored and loaded back is unchanged. -/
theorem decode_encodeInt (w : Nat) (hw : w % 8 = 0) (hpos : 0 < w) (v : Val w) :
    decodeInt? w (encodeInt w v) = some v := by
  cases v with
  | poison =>
    have : 0 < w / 8 := by omega
    simp [decodeInt?, encodeInt, List.any_replicate, Nat.ne_of_gt this]
  | bits b =>
    have hpow : (256 : Nat) ^ (w / 8) = 2 ^ w := by
      rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, show 8 * (w / 8) = w by omega]
    simp [decodeInt?, encodeInt, List.any_map, Function.comp_def]
    rw [map_mod_digits, undigits_digits, hpow, Nat.mod_eq_of_lt b.isLt]
    simp

/-- Fresh memory loaded as an integer is `poison`. -/
theorem decode_fresh (w : Nat) (hw : 8 ≤ w) :
    decodeInt? w (List.replicate (w / 8) .poison) = some .poison := by
  have : 0 < w / 8 := by omega
  simp [decodeInt?, List.any_replicate, Nat.ne_of_gt this]

/-- A pointer stored and loaded back is the same pointer, provenance included. -/
theorem ptrOfFrags_encodePtr (cfg : SpaceCfg) (p : Ptr) (h : 0 < cfg.ptrBits / 8) :
    ptrOfFrags? (cfg.ptrBits / 8) (encodePtr cfg (some p)) = some p := by
  obtain ⟨k, hk⟩ : ∃ k, cfg.ptrBits / 8 = k + 1 := ⟨cfg.ptrBits / 8 - 1, by omega⟩
  simp only [encodePtr, hk, List.range_succ_eq_map, List.map_cons, ptrOfFrags?]
  simp

/-! ## Look-alikes that are wrong

Each lemma above has a near miss that Lean rejects. -/

/-- Forwarding a store to a load that only partly overlaps it is wrong. -/
theorem read_write_overlap_wrong :
    ¬ ∀ (m : Bytes) (bs : List Byte), readBytes (writeBytes m 0 bs) 2 bs.length = bs := by
  intro h
  have := h ∅ [.bits 1, .bits 2, .bits 3, .bits 4]
  simp [readBytes, getD_writeBytes, List.range_succ, Std.ExtTreeMap.getD_empty] at this

/-- A shorter second write doesn't hide the first: the first write's last byte survives. So dead
store elimination needs the second store to be at least as large (`Fir.Dse` requires equal sizes). -/
theorem writeBytes_shorter_wrong :
    ¬ ∀ (m : Bytes) (bs bs' : List Byte),
      writeBytes (writeBytes m 0 bs) 0 bs' = writeBytes m 0 bs' := by
  intro h
  have := congrArg (·[1]?) (h ∅ [.bits 1, .bits 2] [.bits 3])
  simp [getElem?_writeBytes] at this

/-- Two writes to the same bytes can't swap places. -/
theorem write_write_swap_wrong :
    ¬ ∀ (m : Bytes) (x y : Byte),
      readBytes (writeBytes (writeBytes m 0 [x]) 0 [y]) 0 1 =
        readBytes (writeBytes (writeBytes m 0 [y]) 0 [x]) 0 1 := by
  intro h
  have := h ∅ (.bits 1) (.bits 2)
  simp [readBytes, getD_writeBytes] at this

end Fir.MemRules
