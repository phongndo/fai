import Fir.Sem

/-!
# Arithmetic facts behind the lowering

The expansions of `Fir.Lower` compute in a wider integer type where the operation is exact, then
truncate. These lemmas say they give what the HFIR ops define:

* `wrap_ext`: truncating the wide result gives the wrapped result;
* `flag_ext`: the wide result differs from its truncation extended back exactly when the
  operation overflows, as `Sem.overflow` (and so `int.add.s.trap`) defines it;
* `index_inbounds`, `index_wrap`: the index times the stride, computed at twice the address
  size and truncated with `.nsw`, or wrapped, is what `ptr.index` computes;
* `toInt_ofInt_small`: a small constant reads back as itself.
-/

namespace Fir.LowerBits

open BitVec

/-- Sign- or zero-extension. -/
def ext (signed : Bool) (W : Nat) (x : BitVec w) : BitVec W :=
  if signed then x.signExtend W else x.setWidth W

/-- The width where the operation on `w`-bit values is exact. -/
def wide (op : ArithOp) (w : Nat) : Nat := if op = .mul then 2 * w else w + 1

theorem setWidth_signExtend {x : BitVec w} (h : w ≤ W) : (x.signExtend W).setWidth w = x := by
  ext i hi
  simp only [getElem_setWidth, getLsbD_signExtend]
  simp [hi, show i < W by omega]

theorem ext_nil (signed : Bool) (x : BitVec 0) : ext signed W x = 0#W := by
  rw [BitVec.eq_nil x]
  cases signed
  · simp [ext]
  · simp only [ext, ite_true]
    rw [signExtend_eq_setWidth_of_msb_false (by rfl)]
    simp

theorem wrapOp_zero (op : ArithOp) : Sem.wrapOp op (0#W) (0#W) = 0#W := by
  cases op <;> simp [Sem.wrapOp]

theorem ext_setWidth (signed : Bool) {x : BitVec w} (h : w ≤ W) :
    (ext signed W x).setWidth w = x := by
  cases signed
  · simp [ext, setWidth_setWidth_of_le _ h]
  · simp [ext, setWidth_signExtend h]

theorem wrap_ext (op : ArithOp) (signed : Bool) (x y : BitVec w) (h : w ≤ W) :
    (Sem.wrapOp op (ext signed W x) (ext signed W y)).setWidth w = Sem.wrapOp op x y := by
  cases op
  · simp [Sem.wrapOp, setWidth_add _ _ h, ext_setWidth signed h]
  · simp only [Sem.wrapOp, BitVec.sub_eq_add_neg, setWidth_add _ _ h, setWidth_neg_of_le h,
      ext_setWidth signed h]
  · simp [Sem.wrapOp, setWidth_mul _ _ h, ext_setWidth signed h]

theorem le_wide (op : ArithOp) (w : Nat) : w ≤ wide op w := by
  unfold wide; split <;> omega

/-- What the wide width must be for the operation to be exact. -/
def Fits (op : ArithOp) (w W : Nat) : Prop := if op = .mul then 2 * w ≤ W else w + 1 ≤ W

theorem fits_wide (op : ArithOp) (w : Nat) : Fits op w (wide op w) := by
  unfold Fits wide; split <;> omega

theorem Fits.le {op : ArithOp} {w W : Nat} (h : Fits op w W) : w ≤ W := by
  unfold Fits at h; split at h <;> omega

theorem two_pow_eq {n : Nat} (hn : 0 < n) : ((2 ^ n : Nat) : Int) = 2 * 2 ^ (n - 1) := by
  rw [show n = (n - 1) + 1 by omega, Nat.pow_succ]
  push_cast
  rw [Int.mul_comm]

theorem half_pow {n : Nat} (hn : 0 < n) : ((2 ^ n : Nat) : Int) / 2 = 2 ^ (n - 1) := by
  rw [two_pow_eq hn]; omega

theorem half_pow' {n : Nat} (hn : 0 < n) : ((2 ^ n : Nat) + 1 : Int) / 2 = 2 ^ (n - 1) := by
  rw [two_pow_eq hn]; omega

/-- An integer in the signed range of `n > 0` bits is its own balanced residue. -/
theorem bmod_small {n : Nat} {e : Int} (hn : 0 < n) (h0 : -(2 ^ (n - 1) : Int) ≤ e)
    (h1 : e < 2 ^ (n - 1)) : e.bmod (2 ^ n) = e := by
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  rw [Int.bmod_eq_iff hpos]
  have hh := half_pow (show 0 < n by omega)
  have hh' := half_pow' (show 0 < n by omega)
  rw [hh, hh']
  exact ⟨h0, h1, by simp⟩

/-- The balanced residue mod `2^n` is in the signed range of `n` bits. -/
theorem bmod_range {n : Nat} (hn : 0 < n) (e : Int) :
    -(2 ^ (n - 1) : Int) ≤ e.bmod (2 ^ n) ∧ e.bmod (2 ^ n) < 2 ^ (n - 1) := by
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have l := Int.le_bmod (x := e) hpos
  have u := Int.bmod_lt (x := e) hpos
  have hh := half_pow (show 0 < n by omega)
  have hh' := half_pow' (show 0 < n by omega)
  rw [hh] at l
  rw [hh'] at u
  exact ⟨l, u⟩

/-! ## Signed -/

theorem toInt_ext_true {x : BitVec w} (h : w ≤ W) : (ext true W x).toInt = x.toInt := by
  simp [ext, toInt_signExtend_of_le h]

theorem pow_le_pow {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ≤ 2 ^ b := by
  exact_mod_cast Nat.pow_le_pow_right (by decide) h

/-- The exact result fits the wide type. -/
theorem exact_fits (op : ArithOp) (x y : BitVec w) (hW : Fits op w W) :
    -(2 ^ (W - 1) : Int) ≤ Sem.exact op x.toInt y.toInt ∧
      Sem.exact op x.toInt y.toInt < 2 ^ (W - 1) := by
  have hx1 := le_two_mul_toInt (x := x)
  have hx2 := two_mul_toInt_lt (x := x)
  have hy1 := le_two_mul_toInt (x := y)
  have hy2 := two_mul_toInt_lt (x := y)
  unfold Fits at hW
  cases op
  · simp only [reduceCtorEq, ite_false] at hW
    have := pow_le_pow (show w ≤ W - 1 by omega)
    simp only [Sem.exact]
    omega
  · simp only [reduceCtorEq, ite_false] at hW
    have := pow_le_pow (show w ≤ W - 1 by omega)
    simp only [Sem.exact]
    omega
  · simp only [ite_true] at hW
    simp only [Sem.exact]
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · have hx : x.toInt = 0 := by rw [BitVec.eq_nil x]; rfl
      have hy : y.toInt = 0 := by rw [BitVec.eq_nil y]; rfl
      rw [hx, hy, Int.mul_zero]
      have : (0 : Int) < 2 ^ (W - 1) := Int.pow_pos (by decide)
      omega
    have hl := le_toInt_mul_toInt (x := x) (y := y)
    have hu := toInt_mul_toInt_le (x := x) (y := y)
    have e1 : (2 : Int) ^ (2 * w - 1) = 2 * 2 ^ (w * 2 - 2) := by
      rw [show 2 * w - 1 = (w * 2 - 2) + 1 by omega, Int.pow_succ, Int.mul_comm]
    have hle := pow_le_pow (show 2 * w - 1 ≤ W - 1 by omega)
    rw [e1] at hle
    have : (0 : Int) < 2 ^ (w * 2 - 2) := Int.pow_pos (by decide)
    constructor <;> omega

/-- The wide signed result is exact. -/
theorem toInt_wide (op : ArithOp) (x y : BitVec w) (hW : Fits op w W) :
    (Sem.wrapOp op (ext true W x) (ext true W y)).toInt = Sem.exact op x.toInt y.toInt := by
  have h := hW.le
  rcases Nat.eq_zero_or_pos W with rfl | hW0
  · obtain rfl : w = 0 := by omega
    have hx : x.toInt = 0 := by rw [BitVec.eq_nil x]; rfl
    have hy : y.toInt = 0 := by rw [BitVec.eq_nil y]; rfl
    rw [ext_nil, ext_nil, wrapOp_zero, hx, hy]
    cases op <;> rfl
  have hf := exact_fits op x y hW
  cases op <;>
  · simp only [Sem.wrapOp, toInt_add, toInt_sub, toInt_mul, toInt_ext_true h]
    exact bmod_small hW0 hf.1 hf.2

/-- A wide signed value equals its truncation extended back exactly when it fits `w` bits. -/
theorem signExtend_setWidth_eq {z : BitVec W} (h : w ≤ W) (hw : 0 < w) :
    (z.setWidth w).signExtend W = z ↔ -(2 ^ (w - 1) : Int) ≤ z.toInt ∧ z.toInt < 2 ^ (w - 1) := by
  rw [← toInt_inj, toInt_signExtend_of_le h, toInt_setWidth]
  have hb : (z.toNat : Int).bmod (2 ^ w) = z.toInt.bmod (2 ^ w) := by
    rw [toInt_eq_toNat_bmod (x := z)]
    rw [Int.bmod_def, Int.bmod_def]
    have := Int.dvd_bmod_sub_self (x := (z.toNat : Int)) (m := 2 ^ W)
    have hd : ((2 ^ w : Nat) : Int) ∣ ((z.toNat : Int).bmod (2 ^ W) - z.toNat) :=
      Int.dvd_trans (by exact_mod_cast Nat.pow_dvd_pow 2 h) this
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd (by
      rw [← Int.dvd_neg, Int.neg_sub]; exact hd))]
  rw [hb]
  constructor
  · intro e; rw [← e]; exact bmod_range hw _
  · intro ⟨h1, h2⟩; exact bmod_small hw h1 h2

/-! ## Unsigned -/

theorem toNat_ext_false {x : BitVec w} (h : w ≤ W) : (ext false W x).toNat = x.toNat := by
  simp only [ext, Bool.false_eq_true, ite_false, toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))

/-- A wide value equals its truncation extended back exactly when it is below `2^w`. -/
theorem setWidth_setWidth_eq {z : BitVec W} (h : w ≤ W) :
    (z.setWidth w).setWidth W = z ↔ z.toNat < 2 ^ w := by
  rw [← toNat_inj, toNat_setWidth, toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos w))
      (Nat.pow_le_pow_right (by decide) h))]
  constructor
  · intro e; rw [← e]; exact Nat.mod_lt _ (Nat.two_pow_pos w)
  · intro hl; exact Nat.mod_eq_of_lt hl

/-- Whether a wide value differs from its truncation extended back. -/
theorem bne_ext_false {z : BitVec W} (h : w ≤ W) :
    (z != ext false W (z.setWidth w)) = decide (2 ^ w ≤ z.toNat) := by
  have := setWidth_setWidth_eq (z := z) h
  by_cases hz : z.toNat < 2 ^ w
  · simp [ext, this.mpr hz, Nat.not_le.mpr hz]
  · have hne : (z.setWidth w).setWidth W ≠ z := fun e => hz (this.mp e)
    simp only [ext, Bool.false_eq_true, ite_false]
    rw [decide_eq_true (Nat.le_of_not_lt hz)]
    simpa using fun e => hne e.symm

theorem flag_ext_false (op : ArithOp) (x y : BitVec w) (hW : Fits op w W) :
    (Sem.wrapOp op (ext false W x) (ext false W y) !=
        ext false W ((Sem.wrapOp op (ext false W x) (ext false W y)).setWidth w)) =
      Sem.overflowU op x y := by
  have h := hW.le
  rw [bne_ext_false h]
  have hx := x.isLt
  have hy := y.isLt
  unfold Fits at hW
  cases op
  · simp only [reduceCtorEq, ite_false] at hW
    have hWp : 2 ^ (w + 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
    simp only [Sem.wrapOp, Sem.overflowU, toNat_add, toNat_ext_false h, uaddOverflow]
    rw [Nat.mod_eq_of_lt (by rw [Nat.pow_succ] at hWp; omega)]
  · simp only [reduceCtorEq, ite_false] at hW
    have hWp : 2 ^ (w + 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
    rw [Nat.pow_succ] at hWp
    simp only [Sem.wrapOp, Sem.overflowU, toNat_sub, toNat_ext_false h, usubOverflow]
    by_cases hl : x.toNat < y.toNat
    · rw [show 2 ^ W - y.toNat + x.toNat = 2 ^ W - (y.toNat - x.toNat) by omega,
        Nat.mod_eq_of_lt (by omega)]
      simp only [hl, decide_true, decide_eq_true_eq]
      omega
    · rw [show 2 ^ W - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ W by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      simp only [hl, decide_false, decide_eq_false_iff_not, Nat.not_le]
      omega
  · simp only [ite_true] at hW
    simp only [Sem.wrapOp, Sem.overflowU, toNat_mul, toNat_ext_false h, umulOverflow]
    have hm : x.toNat * y.toNat < 2 ^ W := by
      refine Nat.lt_of_lt_of_le ?_ (Nat.pow_le_pow_right (by decide) hW)
      rw [show 2 * w = w + w by omega, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_lt hx hy
    rw [Nat.mod_eq_of_lt hm]

theorem flag_ext_true (op : ArithOp) (x y : BitVec w) (hW : Fits op w W) :
    (Sem.wrapOp op (ext true W x) (ext true W y) !=
        ext true W ((Sem.wrapOp op (ext true W x) (ext true W y)).setWidth w)) =
      Sem.overflowS op x y := by
  have h := hW.le
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have hx : x.toInt = 0 := by rw [BitVec.eq_nil x]; rfl
    have hy : y.toInt = 0 := by rw [BitVec.eq_nil y]; rfl
    have e0 : ∀ z : BitVec W, ext true W (z.setWidth 0) = 0#W := fun z => ext_nil true _
    have hz : Sem.wrapOp op (ext true W x) (ext true W y) = 0#W := by
      rw [ext_nil, ext_nil, wrapOp_zero]
    rw [e0, hz, bne_self_eq_false]
    cases op <;> simp [Sem.overflowS, saddOverflow, ssubOverflow, smulOverflow, hx, hy]
  have key := signExtend_setWidth_eq (w := w) (z := Sem.wrapOp op (ext true W x)
    (ext true W y)) h hw
  rw [toInt_wide op x y hW] at key
  have hs : Sem.overflowS op x y =
      ((Sem.exact op x.toInt y.toInt ≥ 2 ^ (w - 1)) ||
        (Sem.exact op x.toInt y.toInt < -2 ^ (w - 1))) := by
    cases op <;> rfl
  rw [hs]
  by_cases hin : -(2 ^ (w - 1) : Int) ≤ Sem.exact op x.toInt y.toInt ∧
      Sem.exact op x.toInt y.toInt < 2 ^ (w - 1)
  · have e := key.mpr hin
    simp only [ext, ite_true] at e ⊢
    rw [e]
    simp only [bne_self_eq_false]
    symm
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  · have hne := mt key.mp hin
    simp only [ext, ite_true] at hne ⊢
    rw [bne_iff_ne.mpr (Ne.symm hne)]
    symm
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega

/-- **The overflow flag.** Comparing the exact wide result with its truncation extended back
gives `Sem.overflow`. -/
theorem flag_ext (op : ArithOp) (signed : Bool) (x y : BitVec w) (hW : Fits op w W) :
    (Sem.wrapOp op (ext signed W x) (ext signed W y) !=
        ext signed W ((Sem.wrapOp op (ext signed W x) (ext signed W y)).setWidth w)) =
      Sem.overflow signed op x y := by
  cases signed
  · exact flag_ext_false op x y hW
  · exact flag_ext_true op x y hW

/-! ## Indices and offsets -/

theorem toInt_ofInt_small {n : Nat} {i : Int} (hn : 0 < n) (h0 : -(2 ^ (n - 1) : Int) ≤ i)
    (h1 : i < 2 ^ (n - 1)) : (BitVec.ofInt n i).toInt = i := by
  rw [toInt_ofInt, bmod_small hn h0 h1]

/-- `ptr.index.wrap`: the wrapped product. -/
theorem index_wrap (x : BitVec n) (s : Nat) :
    (x * BitVec.ofInt n s).toInt = (BitVec.ofInt n (x.toInt * s)).toInt := by
  simp only [toInt_mul, toInt_ofInt]
  rw [Int.mul_bmod_bmod]

/-- At twice the width, the index times a stride below `2^n` is exact. -/
theorem index_exact (x : BitVec n) {s : Nat} (hs : s < 2 ^ n) :
    (x.signExtend (2 * n) * BitVec.ofInt (2 * n) s).toInt = x.toInt * s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [BitVec.eq_nil x]
  have hx1 := le_toInt x
  have hx2 := toInt_lt (x := x)
  have hp : (2 : Int) ^ (2 * n - 1) = 2 ^ (n - 1) * 2 ^ n := by
    rw [← Int.pow_add]; congr 1; omega
  have hsI : (s : Int) < 2 ^ n := by exact_mod_cast hs
  have hs0 : (0 : Int) ≤ s := Int.natCast_nonneg _
  have hpn : (1 : Int) ≤ 2 ^ (n - 1) := Int.pow_pos (by decide)
  have hpn' : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
  have hsmall : (BitVec.ofInt (2 * n) (s : Int)).toInt = s := by
    apply toInt_ofInt_small (by omega)
    · have : (0 : Int) ≤ 2 ^ (2 * n - 1) := Int.pow_nonneg (by decide)
      omega
    · rw [hp]
      calc (s : Int) < 2 ^ n := hsI
        _ = 1 * 2 ^ n := (Int.one_mul _).symm
        _ ≤ 2 ^ (n - 1) * 2 ^ n := Int.mul_le_mul_of_nonneg_right hpn (Int.le_of_lt hpn')
  rw [toInt_mul, toInt_signExtend_of_le (by omega), hsmall]
  apply bmod_small (by omega)
  · rw [hp]
    calc -(2 ^ (n - 1) * 2 ^ n : Int) = (-2 ^ (n - 1)) * 2 ^ n := by rw [Int.neg_mul]
      _ ≤ (-2 ^ (n - 1)) * s := Int.mul_le_mul_of_nonpos_left (by omega) (by omega)
      _ ≤ x.toInt * s := Int.mul_le_mul_of_nonneg_right hx1 hs0
  · rw [hp]
    calc x.toInt * s ≤ 2 ^ (n - 1) * s := Int.mul_le_mul_of_nonneg_right (by omega) hs0
      _ < 2 ^ (n - 1) * 2 ^ n := Int.mul_lt_mul_of_pos_left hsI (by omega)

/-- Two integers that differ by a multiple of `2^m` with `n ≤ m` have the same balanced residue
mod `2^n`. -/
theorem bmod_congr {a b : Int} {n m : Nat} (h : n ≤ m) (hd : (2 ^ m : Int) ∣ a - b) :
    a.bmod (2 ^ n) = b.bmod (2 ^ n) := by
  have hd' : ((2 ^ n : Nat) : Int) ∣ a - b := by
    refine Int.dvd_trans ?_ hd
    exact_mod_cast Nat.pow_dvd_pow 2 h
  rw [Int.bmod_def, Int.bmod_def, show a % ((2 ^ n : Nat) : Int) = b % ((2 ^ n : Nat) : Int) from
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hd')]

/-- `ptr.index.inbounds`: the product at twice the width, truncated with `.nsw`, is `poison`
exactly when `ptr.index.inbounds` gives `poison`, and otherwise the same offset. -/
theorem index_inbounds (x : BitVec n) {s : Nat} (hs : s < 2 ^ n) :
    ((((x.signExtend (2 * n) * BitVec.ofInt (2 * n) s).setWidth n).signExtend (2 * n) =
        x.signExtend (2 * n) * BitVec.ofInt (2 * n) s) ↔
      (BitVec.ofInt n (x.toInt * s)).toInt = x.toInt * s) ∧
    ((x.signExtend (2 * n) * BitVec.ofInt (2 * n) s).setWidth n).toInt =
      (BitVec.ofInt n (x.toInt * s)).toInt := by
  have he := index_exact x hs
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [BitVec.eq_nil x]
      simp
    rw [signExtend_setWidth_eq (by omega) hn0, he, toInt_ofInt]
    constructor
    · rintro ⟨h0, h1⟩; exact bmod_small hn0 h0 h1
    · intro e
      rw [← e]
      have hn := hn0
      have hpos : 0 < 2 ^ n := Nat.two_pow_pos _
      have l := Int.le_bmod (x := x.toInt * s) hpos
      have u := Int.bmod_lt (x := x.toInt * s) hpos
      have hh := half_pow (show 0 < n by omega)
      have hh' := half_pow' (show 0 < n by omega)
      rw [hh] at l
      rw [hh'] at u
      exact ⟨l, u⟩
  · rw [toInt_setWidth, toInt_ofInt]
    apply bmod_congr (m := 2 * n) (by omega)
    rw [← he, toInt_eq_toNat_bmod (x := x.signExtend (2 * n) * BitVec.ofInt (2 * n) s)]
    have := Int.dvd_bmod_sub_self (x := ((x.signExtend (2 * n) * BitVec.ofInt (2 * n) s).toNat : Int))
      (m := 2 ^ (2 * n))
    rw [← Int.dvd_neg, Int.neg_sub]
    exact_mod_cast this

end Fir.LowerBits
