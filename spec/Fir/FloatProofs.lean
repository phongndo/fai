import Fir.Float

/-!
# Float lemmas

Facts that pin `Fir.Float` down, generically over the format where they hold generically:

* `round_decode`: rounding a value that is exactly representable gives its bits back (rounding
  is the identity on the format's values), and `decode_round` the other way around: a
  representable number of units rounds to bits that decode to it.
* `neg_neg`: `float.neg` is an involution on bits (NaN payloads included).
* `add_comm`, `mul_comm`: addition and multiplication commute up to the NaN payload the oracle
  picks: for every answer on one side there is one on the other that gives the same bits.
* `cvt_cvt`: widening then narrowing (`float.ext` then `float.trunc`) gives every non-NaN value
  back; `ext_trunc` is the case of `f32` through `f64`.
* `truncInt_ofInt`: integers of at most `m + 1` bits convert to a float and back exactly;
  `f32` and `f64` instances below.
-/

namespace Fir.Float

variable {F G : FloatFmt}

/-! ## Arithmetic helpers -/

theorem two_pow_pos (n : Nat) : 0 < 2 ^ n := Nat.pos_of_ne_zero (by simp)

theorem rne_exact {a d : Nat} (hd : 0 < d) : rne (a * d) d = a := by
  unfold rne
  rw [Nat.mul_mod_left, Nat.mul_div_cancel _ hd]
  simp
  omega

/-- A number divisible by `d`, divided exactly, rounds to its quotient. -/
theorem rne_dvd {n d : Nat} (hd : 0 < d) (h : n % d = 0) : rne n d = n / d := by
  have : n = n / d * d := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm
  conv => lhs; rw [this]
  exact rne_exact hd

theorem four_le (he : 2 ≤ F.e) : 4 ≤ 2 ^ F.e :=
  calc 4 = 2 ^ 2 := rfl
    _ ≤ 2 ^ F.e := Nat.pow_le_pow_right (by decide) he

theorem getD_of_lt {l : List α} {i : Nat} {d : α} (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem log2_eq {n k : Nat} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) : n.log2 = k :=
  (Nat.log2_eq_iff (by have := two_pow_pos k; omega)).mpr ⟨h1, h2⟩

theorem log2_lt_of_lt {n k : Nat} (h : n < 2 ^ k) : n.log2 < k ∨ n = 0 := by
  by_cases hn : n = 0
  · exact .inr hn
  · exact .inl ((Nat.log2_lt hn).mpr h)

/-! ## Fields -/

theorem width_eq (F : FloatFmt) : 2 ^ F.width = 2 * (2 ^ F.e * 2 ^ F.m) := by
  simp only [FloatFmt.width, Nat.pow_succ, Nat.pow_add]; ac_rfl

/-- The number with these fields. -/
def packNat (F : FloatFmt) (neg : Bool) (E T : Nat) : Nat :=
  (if neg then 2 ^ (F.e + F.m) else 0) + E * 2 ^ F.m + T

theorem packNat_lt {neg : Bool} {E T : Nat} (hE : E < 2 ^ F.e) (hT : T < 2 ^ F.m) :
    packNat F neg E T < 2 ^ F.width := by
  rw [width_eq]
  unfold packNat
  rw [Nat.pow_add]
  have h1 : (E + 1) * 2 ^ F.m ≤ 2 ^ F.e * 2 ^ F.m := Nat.mul_le_mul_right _ hE
  rw [Nat.succ_mul] at h1
  split <;> omega

theorem toNat_pack {neg : Bool} {E T : Nat} (hE : E < 2 ^ F.e) (hT : T < 2 ^ F.m) :
    (pack F neg E T).toNat = packNat F neg E T := by
  unfold pack
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (packNat_lt hE hT)

/-- `packNat` as `P * (Q * s + E) + T`, with `P = 2^m`, `Q = 2^e`, and `s` the sign bit. -/
theorem packNat_eq (neg : Bool) (E T : Nat) :
    packNat F neg E T = 2 ^ F.m * (2 ^ F.e * (if neg then 1 else 0) + E) + T := by
  unfold packNat
  rw [Nat.pow_add]
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.zero_add]
    rw [Nat.mul_comm]
  · simp only [↓reduceIte, Nat.mul_one]
    rw [Nat.mul_add, Nat.mul_comm (2 ^ F.m) E, Nat.mul_comm (2 ^ F.m) (2 ^ F.e)]

/-- Reading the fields back from `P * (Q * s + E) + T`. -/
theorem decomp {P Q s E T : Nat} (hP : 0 < P) (hT : T < P) (hE : E < Q) :
    (P * (Q * s + E) + T) % P = T ∧ (P * (Q * s + E) + T) / P % Q = E ∧
      (P * (Q * s + E) + T) / P / Q = s := by
  have hQ : 0 < Q := by omega
  have h1 : (P * (Q * s + E) + T) / P = Q * s + E := by
    rw [Nat.mul_add_div hP, Nat.div_eq_of_lt hT, Nat.add_zero]
  refine ⟨by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hT], ?_, ?_⟩
  · rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hE]
  · rw [h1, Nat.mul_add_div hQ, Nat.div_eq_of_lt hE, Nat.add_zero]

theorem manOf_pack {neg : Bool} {E T : Nat} (hE : E < 2 ^ F.e) (hT : T < 2 ^ F.m) :
    manOf (pack F neg E T) = T := by
  unfold manOf
  rw [toNat_pack hE hT, packNat_eq]
  exact (decomp (two_pow_pos _) hT hE).1

theorem expOf_pack {neg : Bool} {E T : Nat} (hE : E < 2 ^ F.e) (hT : T < 2 ^ F.m) :
    expOf (pack F neg E T) = E := by
  unfold expOf
  rw [toNat_pack hE hT, packNat_eq]
  exact (decomp (two_pow_pos _) hT hE).2.1

theorem signOf_pack {neg : Bool} {E T : Nat} (hE : E < 2 ^ F.e) (hT : T < 2 ^ F.m) :
    signOf (pack F neg E T) = neg := by
  unfold signOf
  rw [toNat_pack hE hT, packNat_eq, Nat.add_comm F.e, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    (decomp (two_pow_pos _) hT hE).2.2]
  cases neg <;> rfl

/-- Every float is its fields packed. -/
theorem pack_fields (x : Bits F) : pack F (signOf x) (expOf x) (manOf x) = x := by
  apply BitVec.eq_of_toNat_eq
  have hE : expOf x < 2 ^ F.e := Nat.mod_lt _ (two_pow_pos _)
  have hT : manOf x < 2 ^ F.m := Nat.mod_lt _ (two_pow_pos _)
  rw [toNat_pack hE hT, packNat_eq]
  have hx := x.isLt
  rw [width_eq] at hx
  unfold signOf expOf manOf
  generalize x.toNat = n at hx ⊢
  have hP := two_pow_pos F.m
  have hdiv : n / 2 ^ (F.e + F.m) = n / 2 ^ F.m / 2 ^ F.e := by
    rw [Nat.div_div_eq_div_mul, Nat.add_comm, Nat.pow_add]
  have hs : n / 2 ^ F.m / 2 ^ F.e < 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (Nat.mul_pos hP (two_pow_pos _)),
      Nat.mul_comm (2 ^ F.m) (2 ^ F.e)]
    exact hx
  have e1 := Nat.div_add_mod n (2 ^ F.m)
  have e2 := Nat.div_add_mod (n / 2 ^ F.m) (2 ^ F.e)
  have hb : (if (n / 2 ^ (F.e + F.m) % 2 == 1) = true then 1 else 0) = n / 2 ^ F.m / 2 ^ F.e := by
    rw [hdiv]
    generalize n / 2 ^ F.m / 2 ^ F.e = k at hs ⊢
    rcases k with _ | _ | k
    · rfl
    · rfl
    · omega
  rw [hb, e2, e1]

theorem decode_pack {neg : Bool} {E T : Nat} (hE : E < F.special) (hT : T < 2 ^ F.m) :
    decode (pack F neg E T) = .fin neg (mag F E T) := by
  have hE' : E < 2 ^ F.e := by unfold FloatFmt.special at hE; omega
  unfold decode
  rw [expOf_pack hE' hT, manOf_pack hE' hT, signOf_pack hE' hT]
  simp only [show ¬ E = F.special by omega, ↓reduceIte]

/-! ## Representable values -/

/-- A number of units the format represents exactly: its top `m + 1` bits hold all its set
bits, and it is below where rounding overflows. -/
def Repr (F : FloatFmt) (N : Nat) : Prop := N % 2 ^ (N.log2 - F.m) = 0 ∧ N < 2 ^ F.top

/-- The exponent field of a representable number of units. -/
def efield (F : FloatFmt) (N : Nat) : Nat := if N < 2 ^ F.m then 0 else N.log2 - F.m + 1

/-- The trailing significand of a representable number of units. -/
def tfield (F : FloatFmt) (N : Nat) : Nat :=
  if N < 2 ^ F.m then N else N / 2 ^ (N.log2 - F.m) - 2 ^ F.m

/-- The bounds on the significand of a number of at least `2^m` units. -/
theorem sig_bounds {N : Nat} (h : 2 ^ F.m ≤ N) :
    F.m ≤ N.log2 ∧ 2 ^ F.m ≤ N / 2 ^ (N.log2 - F.m) ∧ N / 2 ^ (N.log2 - F.m) < 2 ^ (F.m + 1) := by
  have hN : N ≠ 0 := by have := two_pow_pos F.m; omega
  have hL : F.m ≤ N.log2 := (Nat.le_log2 hN).mpr h
  have h1 := Nat.log2_self_le hN
  have h2 := Nat.lt_log2_self (n := N)
  refine ⟨hL, ?_, ?_⟩
  · rw [Nat.le_div_iff_mul_le (two_pow_pos _), ← Nat.pow_add, Nat.add_sub_cancel' hL]; exact h1
  · rw [Nat.div_lt_iff_lt_mul (two_pow_pos _), ← Nat.pow_add,
      show F.m + 1 + (N.log2 - F.m) = N.log2 + 1 by omega]
    exact h2

/-- `round` of a representable number of units, scaled by any `c > 0`: the bits of its fields. -/
theorem round_repr {N c : Nat} {neg : Bool} (hc : 0 < c) (hN : Repr F N) (he : 2 ≤ F.e) :
    round F neg (N * c) c = pack F neg (efield F N) (tfield F N) := by
  obtain ⟨hmod, htop⟩ := hN
  unfold round
  simp only [Nat.mul_div_cancel _ hc]
  have hs : rne (N * c) (c * 2 ^ (N.log2 - F.m)) = N / 2 ^ (N.log2 - F.m) := by
    rw [rne_dvd (Nat.mul_pos hc (two_pow_pos _)) (by
      rw [Nat.mul_comm c, Nat.mul_mod_mul_right, hmod, Nat.zero_mul]),
      Nat.mul_comm c, Nat.mul_div_mul_right _ _ hc]
  rw [hs]
  unfold efield tfield
  by_cases hm : N < 2 ^ F.m
  · have hs0 : N.log2 - F.m = 0 := by
      rcases log2_lt_of_lt hm with h | h
      · omega
      · subst h; simp
    simp only [hs0, Nat.pow_zero, Nat.div_one, hm, ↓reduceIte]
  · obtain ⟨hL, hlo, hhi⟩ := sig_bounds (F := F) (N := N) (by omega)
    simp only [hm, show ¬ N / 2 ^ (N.log2 - F.m) < 2 ^ F.m by omega, ↓reduceIte]
    have hne : N / 2 ^ (N.log2 - F.m) ≠ 2 ^ (F.m + 1) := by omega
    simp only [hne, ↓reduceIte]
    have hlt : N.log2 < F.top := (Nat.log2_lt (by have := two_pow_pos F.m; omega)).mpr htop
    have : ¬ (N.log2 - F.m + 1 ≥ F.special) := by
      unfold FloatFmt.top at hlt; unfold FloatFmt.special
      have : 4 ≤ 2 ^ F.e := by
        calc 4 = 2 ^ 2 := rfl
          _ ≤ 2 ^ F.e := Nat.pow_le_pow_right (by decide) he
      omega
    simp only [this, ↓reduceIte]

theorem mag_fields {N : Nat} (hN : N % 2 ^ (N.log2 - F.m) = 0) :
    mag F (efield F N) (tfield F N) = N := by
  unfold mag efield tfield
  by_cases hm : N < 2 ^ F.m
  · simp [hm]
  · obtain ⟨hL, hlo, _⟩ := sig_bounds (F := F) (N := N) (by omega)
    simp only [hm, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [Nat.add_sub_cancel' hlo]
    exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hN)

theorem fields_lt {N : Nat} (hN : Repr F N) (he : 2 ≤ F.e) :
    efield F N < F.special ∧ tfield F N < 2 ^ F.m := by
  obtain ⟨_, htop⟩ := hN
  unfold efield tfield FloatFmt.special
  have : 4 ≤ 2 ^ F.e := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ F.e := Nat.pow_le_pow_right (by decide) he
  by_cases hm : N < 2 ^ F.m
  · simp only [hm, ↓reduceIte]
    exact ⟨by omega, trivial⟩
  · obtain ⟨hL, hlo, hhi⟩ := sig_bounds (F := F) (N := N) (by omega)
    simp only [hm, ↓reduceIte]
    have hlt : N.log2 < F.top := (Nat.log2_lt (by have := two_pow_pos F.m; omega)).mpr htop
    unfold FloatFmt.top at hlt
    rw [Nat.pow_succ] at hhi
    omega

/-- **A representable number of units rounds to bits that decode to it.** -/
theorem decode_round {N c : Nat} {neg : Bool} (hc : 0 < c) (hN : Repr F N) (he : 2 ≤ F.e) :
    decode (round F neg (N * c) c) = .fin neg N := by
  obtain ⟨hE, hT⟩ := fields_lt hN he
  rw [round_repr hc hN he, decode_pack hE hT, mag_fields hN.1]

/-- A finite float's number of units is representable, and its fields are its own. -/
theorem repr_mag {E T : Nat} (hE : E < F.special) (hT : T < 2 ^ F.m) (he : 2 ≤ F.e) :
    Repr F (mag F E T) ∧ efield F (mag F E T) = E ∧ tfield F (mag F E T) = T := by
  have h4 := four_le he
  unfold FloatFmt.special at hE
  unfold mag
  by_cases h0 : E = 0
  · subst h0
    simp only [↓reduceIte]
    have hs0 : T.log2 - F.m = 0 := by
      rcases log2_lt_of_lt hT with h | h
      · omega
      · subst h; simp
    refine ⟨⟨by simp [hs0, Nat.mod_one], ?_⟩, by simp [efield, hT], by simp [tfield, hT]⟩
    exact Nat.lt_of_lt_of_le hT (Nat.pow_le_pow_right (by decide) (by unfold FloatFmt.top; omega))
  · simp only [h0, ↓reduceIte]
    have hL : ((2 ^ F.m + T) * 2 ^ (E - 1)).log2 = F.m + (E - 1) := by
      apply log2_eq
      · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ (by omega)
      · rw [show F.m + (E - 1) + 1 = (F.m + 1) + (E - 1) by omega, Nat.pow_add]
        exact Nat.mul_lt_mul_of_pos_right (by rw [Nat.pow_succ]; omega) (two_pow_pos _)
    have hge : ¬ (2 ^ F.m + T) * 2 ^ (E - 1) < 2 ^ F.m := by
      have := Nat.le_mul_of_pos_right (2 ^ F.m + T) (two_pow_pos (E - 1)); omega
    have hs : F.m + (E - 1) - F.m = E - 1 := by omega
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hL, hs]; exact Nat.mul_mod_left _ _
    · calc (2 ^ F.m + T) * 2 ^ (E - 1) < 2 ^ (F.m + 1) * 2 ^ (E - 1) :=
            Nat.mul_lt_mul_of_pos_right (by rw [Nat.pow_succ]; omega) (two_pow_pos _)
        _ = 2 ^ (F.m + 1 + (E - 1)) := (Nat.pow_add 2 (F.m + 1) (E - 1)).symm
        _ ≤ 2 ^ F.top := Nat.pow_le_pow_right (by decide) (by unfold FloatFmt.top; omega)
    · unfold efield; simp only [hge, ↓reduceIte, hL]; omega
    · unfold tfield
      simp only [hge, ↓reduceIte, hL, hs, Nat.mul_div_cancel _ (two_pow_pos _),
        Nat.add_sub_cancel_left]

/-- The fields of a non-special float. -/
theorem decode_fin {x : Bits F} {neg : Bool} {n : Nat} (h : decode x = .fin neg n) :
    expOf x < F.special ∧ manOf x < 2 ^ F.m ∧ neg = signOf x ∧ n = mag F (expOf x) (manOf x) := by
  have hE : expOf x < 2 ^ F.e := Nat.mod_lt _ (two_pow_pos _)
  have hT : manOf x < 2 ^ F.m := Nat.mod_lt _ (two_pow_pos _)
  unfold decode at h
  by_cases hs : expOf x = F.special
  · simp only [hs, ↓reduceIte] at h
    split at h <;> cases h
  · simp only [hs, ↓reduceIte] at h
    cases h
    exact ⟨by unfold FloatFmt.special at hs ⊢; omega, hT, rfl, rfl⟩

/-- **Rounding a representable value is the identity**: a finite float's value, rounded, gives
its bits back. -/
theorem round_decode {x : Bits F} {neg : Bool} {n : Nat} (h : decode x = .fin neg n)
    (he : 2 ≤ F.e) : round F neg n 1 = x := by
  obtain ⟨hE, hT, rfl, rfl⟩ := decode_fin h
  obtain ⟨hR, hEf, hTf⟩ := repr_mag hE hT he
  rw [← Nat.mul_one (mag F _ _), round_repr Nat.one_pos hR he, hEf, hTf, pack_fields]

/-! ## Negation -/

/-- **`float.neg` is an involution on bits.** -/
theorem neg_neg (x : Bits F) : neg (neg x) = x := by
  simp [neg, BitVec.xor_assoc]

/-! ## Commutativity up to the NaN choice -/

/-- A NaN result from a permutation of the inputs: any answer on one side has one on the
other that picks the same NaN. -/
theorem nanResult_perm {l1 l2 : List (Bits F)} (hp : l1.Perm l2) (o : Int) :
    ∃ o', nanResult G o l1 = nanResult G o' l2 := by
  unfold nanResult
  simp only
  generalize hc1 : canonNaN G :: (l1.filter isNaN).map (quietAs G) = c1
  generalize hc2 : canonNaN G :: (l2.filter isNaN).map (quietAs G) = c2
  have hp' : c1.Perm c2 := by
    rw [← hc1, ← hc2]; exact .cons _ ((hp.filter _).map _)
  have hlen : 0 < c1.length := by rw [← hc1]; simp
  have hi : o.toNat % c1.length < c1.length := Nat.mod_lt _ hlen
  have hmem : c1.getD (o.toNat % c1.length) (canonNaN G) ∈ c2 := by
    rw [getD_of_lt hi]
    exact hp'.subset (List.getElem_mem hi)
  obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hmem
  refine ⟨j, ?_⟩
  rw [show ((j : Int).toNat % c2.length) = j by simp [Nat.mod_eq_of_lt hj], getD_of_lt hj, hjv]

theorem addFin_comm (a : Bool) (n : Nat) (b : Bool) (k : Nat) :
    addFin F a n b k = addFin F b k a n := by
  unfold addFin
  rw [Int.add_comm, Bool.and_comm]

/-- **Addition commutes**, up to the NaN payload the oracle picks. -/
theorem add_comm (o : Int) (x y : Bits F) : ∃ o', add o x y = add o' y x := by
  have hp : [x, y].Perm [y, x] := .swap _ _ _
  unfold add
  rcases hx : decode x with _ | a | ⟨a, n⟩ <;> rcases hy : decode y with _ | b | ⟨b, k⟩ <;>
    simp only
  all_goals first
    | exact nanResult_perm hp o
    | exact ⟨o, rfl⟩
    | exact ⟨o, trivial⟩
    | exact ⟨o, addFin_comm _ _ _ _⟩
    | skip
  -- Two infinities.
  by_cases h : a = b
  · subst h; exact ⟨o, by simp⟩
  · simp only [h, Ne.symm h, ↓reduceIte]; exact nanResult_perm hp o

/-- **Multiplication commutes**, up to the NaN payload the oracle picks. -/
theorem mul_comm (o : Int) (x y : Bits F) : ∃ o', mul o x y = mul o' y x := by
  have hp : [x, y].Perm [y, x] := .swap _ _ _
  have hb (a b : Bool) : (a != b) = (b != a) := by cases a <;> cases b <;> rfl
  unfold mul
  rcases hx : decode x with _ | a | ⟨a, n⟩ <;> rcases hy : decode y with _ | b | ⟨b, k⟩ <;>
    simp only
  any_goals exact nanResult_perm hp o
  · exact ⟨o, by rw [hb]⟩
  · by_cases hk : k = 0
    · simp only [hk, ↓reduceIte]; exact nanResult_perm hp o
    · simp only [hk, ↓reduceIte]; exact ⟨o, trivial⟩
  · by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]; exact nanResult_perm hp o
    · simp only [hn, ↓reduceIte]; exact ⟨o, trivial⟩
  · exact ⟨o, by rw [hb, Nat.mul_comm n k]⟩

/-! ## Conversions -/

/-- Widening keeps representability. -/
theorem repr_widen {N : Nat} (hN : Repr F N) (hm : F.m ≤ G.m)
    (ht : F.top + (G.qneg - F.qneg) ≤ G.top) : Repr G (N * 2 ^ (G.qneg - F.qneg)) := by
  obtain ⟨hmod, htop⟩ := hN
  refine ⟨?_, ?_⟩
  · by_cases h0 : N = 0
    · subst h0; simp
    have hL : (N * 2 ^ (G.qneg - F.qneg)).log2 = N.log2 + (G.qneg - F.qneg) := by
      apply log2_eq
      · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ (Nat.log2_self_le h0)
      · rw [show N.log2 + (G.qneg - F.qneg) + 1 = (N.log2 + 1) + (G.qneg - F.qneg) by omega,
          Nat.pow_add]
        exact Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (two_pow_pos _)
    rw [hL]
    apply Nat.mod_eq_zero_of_dvd
    have h1 : 2 ^ (N.log2 - F.m) ∣ N := Nat.dvd_of_mod_eq_zero hmod
    have h2 : 2 ^ (N.log2 - F.m + (G.qneg - F.qneg)) ∣ N * 2 ^ (G.qneg - F.qneg) := by
      rw [Nat.pow_add]; exact Nat.mul_dvd_mul_right h1 _
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) h2
  · calc N * 2 ^ (G.qneg - F.qneg) < 2 ^ F.top * 2 ^ (G.qneg - F.qneg) :=
          Nat.mul_lt_mul_of_pos_right htop (two_pow_pos _)
      _ = 2 ^ (F.top + (G.qneg - F.qneg)) := by rw [Nat.pow_add]
      _ ≤ 2 ^ G.top := Nat.pow_le_pow_right (by decide) ht

theorem decode_inf {x : Bits F} {neg : Bool} (h : decode x = .inf neg) : x = inf F neg := by
  unfold decode at h
  by_cases hE : expOf x = F.special
  · simp only [hE, ↓reduceIte] at h
    by_cases hT : manOf x = 0
    · simp only [hT, ↓reduceIte] at h
      cases h
      calc x = pack F (signOf x) (expOf x) (manOf x) := (pack_fields x).symm
        _ = inf F (signOf x) := by rw [hE, hT]; rfl
    · simp only [hT, ↓reduceIte] at h; cases h
  · simp only [hE, ↓reduceIte] at h; cases h

theorem decode_inf' (neg : Bool) : decode (inf F neg) = .inf neg := by
  have hE : F.special < 2 ^ F.e := by unfold FloatFmt.special; have := two_pow_pos F.e; omega
  unfold decode inf
  rw [expOf_pack hE (two_pow_pos _), manOf_pack hE (two_pow_pos _),
    signOf_pack hE (two_pow_pos _)]
  simp

/-- **Widening, then narrowing back, gives every non-NaN value back**, whatever NaN choices
the oracle makes. -/
theorem cvt_cvt {x : Bits F} (hx : decode x ≠ .nan) (o o' : Int) (hm : F.m ≤ G.m)
    (hq : F.qneg < G.qneg) (ht : F.top + (G.qneg - F.qneg) ≤ G.top) (he : 2 ≤ F.e)
    (heG : 2 ≤ G.e) : cvt F o' (cvt G o x) = x := by
  unfold cvt
  rcases h : decode x with _ | neg | ⟨neg, n⟩
  · exact absurd h hx
  · simp only
    rw [decode_inf' neg]
    simp only
    exact (decode_inf h).symm
  · simp only [Nat.le_of_lt hq, ↓reduceIte]
    obtain ⟨hE, hT, rfl, rfl⟩ := decode_fin h
    obtain ⟨hR, _, _⟩ := repr_mag hE hT he
    have hR' := repr_widen hR hm ht
    rw [← Nat.mul_one (_ * _), decode_round Nat.one_pos hR' heG]
    simp only [show ¬ G.qneg ≤ F.qneg by omega, ↓reduceIte]
    rw [round_repr (two_pow_pos _) hR he]
    obtain ⟨hR, hEf, hTf⟩ := repr_mag hE hT he
    rw [hEf, hTf, pack_fields]

/-- **`float.ext` then `float.trunc` is the identity on `f32`**, NaNs aside (they come back
quiet, or canonical). -/
theorem ext_trunc {x : Bits FloatTy.f32.fmt} (hx : decode x ≠ .nan) (o o' : Int) :
    cvt FloatTy.f32.fmt o' (cvt FloatTy.f64.fmt o x) = x :=
  cvt_cvt hx o o' (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## Integers -/

/-- **Integers of at most `m + 1` bits convert exactly**: to a float and back to an integer
(toward zero), they are unchanged, when the format's range holds them. -/
theorem truncInt_ofInt {v : Int} (hv : v.natAbs < 2 ^ (F.m + 1)) (he : 2 ≤ F.e)
    (hr : F.m + 1 ≤ 2 ^ (F.e - 1)) : truncInt (ofInt F v) = some v := by
  have hR : Repr F (v.natAbs * 2 ^ F.qneg) := by
    refine ⟨?_, ?_⟩
    · by_cases h0 : v.natAbs = 0
      · simp [h0]
      have hL : (v.natAbs * 2 ^ F.qneg).log2 = v.natAbs.log2 + F.qneg := by
        apply log2_eq
        · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ (Nat.log2_self_le h0)
        · rw [show v.natAbs.log2 + F.qneg + 1 = (v.natAbs.log2 + 1) + F.qneg by omega,
            Nat.pow_add]
          exact Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (two_pow_pos _)
      have hl : v.natAbs.log2 < F.m + 1 := (Nat.log2_lt h0).mpr hv
      rw [hL]
      apply Nat.mod_eq_zero_of_dvd
      exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_left _ _)
    · have : F.m + 1 + F.qneg ≤ F.top := by
        unfold FloatFmt.top FloatFmt.qneg
        have : 2 ^ F.e = 2 * 2 ^ (F.e - 1) := by
          rw [← Nat.pow_succ']; congr 1; omega
        have : 2 ≤ 2 ^ (F.e - 1) := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ (F.e - 1) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      calc v.natAbs * 2 ^ F.qneg < 2 ^ (F.m + 1) * 2 ^ F.qneg :=
            Nat.mul_lt_mul_of_pos_right hv (two_pow_pos _)
        _ = 2 ^ (F.m + 1 + F.qneg) := (Nat.pow_add 2 (F.m + 1) F.qneg).symm
        _ ≤ 2 ^ F.top := Nat.pow_le_pow_right (by decide) this
  unfold truncInt ofInt
  rw [← Nat.mul_one (_ * _), decode_round Nat.one_pos hR he]
  simp only [Nat.mul_div_cancel _ (two_pow_pos _)]
  unfold sval
  congr 1
  by_cases h : v < 0
  · simp only [h, decide_true, ↓reduceIte]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

/-- Integers of at most 24 bits convert to `f32` and back exactly. -/
theorem truncInt_ofInt_f32 {v : Int} (hv : v.natAbs < 2 ^ 24) :
    truncInt (ofInt FloatTy.f32.fmt v) = some v :=
  truncInt_ofInt hv (by decide) (by decide)

/-- Integers of at most 53 bits convert to `f64` and back exactly. -/
theorem truncInt_ofInt_f64 {v : Int} (hv : v.natAbs < 2 ^ 53) :
    truncInt (ofInt FloatTy.f64.fmt v) = some v :=
  truncInt_ofInt hv (by decide) (by decide)

end Fir.Float
