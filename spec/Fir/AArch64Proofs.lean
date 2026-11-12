import Fir.AArch64
import Fir.FloatProofs
import Fir.Sem
import Fir.Interp

/-!
# Arm's FP results are ones FIR allows

Each scalar FP instruction (`Fir.AArch64`) gives what FIR's op gives for some NaN answer of the
oracle (decision: NaN choice): `processNaNs` picks a quieted NaN operand, which is one of the
choices `nanResult` offers, and the default NaN is the canonical one, answer 0 (`fpAlu_allowed`,
`fpSqrt_allowed`, `fpMulAdd_allowed`, `fpConvert_allowed`). Arm's choice depends only on the
instruction and its operands, so the oracle whose `nan` is that choice is one the semantics
quantifies over: native NaNs are the source's under it (`armNan`, `Oracle.arm`, and the
`*_arm` theorems: under that oracle FIR's float ops give exactly the instructions' results).
`fcvtzs` and `fcvtzu` are `float.to_int.*.sat` exactly (`fcvtz_sat`).
-/

namespace Fir.AArch64

open _root_.Fir.Float

variable {F G : FloatFmt}

theorem decode_nan {x : Bits F} : decode x = .nan ↔ isNaN x = true := by
  unfold decode isNaN
  by_cases h1 : expOf x = F.special <;> by_cases h2 : manOf x = 0 <;> simp [h1, h2]

theorem nanResult_zero (ins : List (Bits F)) : nanResult G 0 ins = canonNaN G := by
  simp [nanResult]

/-- Every quieted NaN input is a NaN result some answer picks. -/
theorem nanResult_mem {ins : List (Bits F)} {r : Bits G}
    (h : r ∈ (ins.filter isNaN).map (quietAs G)) : ∃ o, nanResult G o ins = r := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  refine ⟨((i + 1 : Nat) : Int), ?_⟩
  unfold nanResult
  have hl : i + 1 < (canonNaN G :: (ins.filter isNaN).map (quietAs G)).length := by
    simp only [List.length_cons]; omega
  simp only [Int.toNat_natCast, Nat.mod_eq_of_lt hl]
  rw [getD_of_lt hl]
  simp

theorem nan_of_mem {ins : List (Bits F)} {r : Bits G}
    (h : r ∈ (ins.filter isNaN).map (quietAs G)) : ∃ z ∈ ins, isNaN z = true := by
  obtain ⟨z, hz, _⟩ := List.mem_map.mp h
  exact ⟨z, (List.mem_filter.mp hz).1, (List.mem_filter.mp hz).2⟩

/-- `processNaNs` gives a quieted NaN operand. -/
theorem processNaNs_some {ins : List (Bits F)} {r : Bits F} (h : processNaNs ins = some r) :
    r ∈ (ins.filter isNaN).map (quietAs F) := by
  unfold processNaNs at h
  split at h
  · rename_i x hx
    injection h with h
    subst h
    have hs := List.find?_some hx
    simp only [isSNaN, Bool.and_eq_true, decide_eq_true_eq] at hs
    exact List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hx, hs.1⟩, rfl⟩
  · cases hf : ins.find? isNaN with
    | none => simp [hf] at h
    | some x =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      subst h
      exact List.mem_map.mpr
        ⟨x, List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hf, List.find?_some hf⟩, rfl⟩

/-! ## Each op, with a NaN operand, gives `nanResult` -/

theorem alu_nan (op : FAluOp) (o : Int) {x y : Bits F} (h : ∃ z ∈ [x, y], isNaN z = true) :
    op.float o x y = nanResult F o [x, y] := by
  obtain ⟨z, hz, hn⟩ := h
  have hd := decode_nan.mpr hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;> cases op <;>
    simp only [FAluOp.float, Float.add, Float.sub, Float.mul, Float.div] <;> split <;> simp_all

theorem sqrt_nan (o : Int) {x : Bits F} (h : isNaN x = true) : Float.sqrt o x = nanResult F o [x] := by
  unfold Float.sqrt
  rw [decode_nan.mpr h]

theorem fma_nan (o : Int) {x y z : Bits F} (h : ∃ w ∈ [x, y, z], isNaN w = true) :
    Float.fma o x y z = nanResult F o [x, y, z] := by
  obtain ⟨w, hw, hn⟩ := h
  have hd := decode_nan.mpr hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  unfold Float.fma
  rcases hw with rfl | rfl | rfl <;> split <;> simp_all

theorem cvt_nan (o : Int) {x : Bits F} (h : isNaN x = true) : Float.cvt G o x = nanResult G o [x] := by
  unfold Float.cvt
  rw [decode_nan.mpr h]

/-! ## Arm's results are allowed -/

/-- **`fadd`, `fsub`, `fmul`, `fdiv` give what `float.add`, … allow.** -/
theorem fpAlu_allowed (op : FAluOp) (x y : Bits F) : ∃ o, fpAlu op x y = op.float o x y := by
  unfold fpAlu
  split
  · rename_i r h
    have hm := processNaNs_some h
    obtain ⟨o, ho⟩ := nanResult_mem hm
    exact ⟨o, by rw [alu_nan op o (nan_of_mem hm), ho]⟩
  · exact ⟨0, rfl⟩

/-- **`fsqrt` gives what `float.sqrt` allows.** -/
theorem fpSqrt_allowed (x : Bits F) : ∃ o, fpSqrt x = Float.sqrt o x := by
  unfold fpSqrt
  split
  · rename_i r h
    have hm := processNaNs_some h
    obtain ⟨o, ho⟩ := nanResult_mem hm
    obtain ⟨z, hz, hn⟩ := nan_of_mem hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    subst hz
    exact ⟨o, by rw [sqrt_nan o hn, ho]⟩
  · exact ⟨0, rfl⟩

/-- **`fmadd` gives what `float.fma` allows**, its addend last. -/
theorem fpMulAdd_allowed (a n m : Bits F) : ∃ o, fpMulAdd a n m = Float.fma o n m a := by
  unfold fpMulAdd
  split
  · rename_i h
    have ha : isNaN a = true := by revert h; cases isNaN a <;> simp
    refine ⟨0, ?_⟩
    rw [fma_nan 0 ⟨a, by simp, ha⟩, nanResult_zero]
  · split
    · rename_i r h
      have hm := processNaNs_some h
      -- The same NaNs, in another order.
      have hm' : r ∈ ([n, m, a].filter isNaN).map (quietAs F) := by
        simp only [List.mem_map, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false]
          at hm ⊢
        obtain ⟨z, ⟨hz, hn⟩, e⟩ := hm
        exact ⟨z, ⟨by rcases hz with rfl | rfl | rfl <;> simp, hn⟩, e⟩
      obtain ⟨o, ho⟩ := nanResult_mem hm'
      exact ⟨o, by rw [fma_nan o (nan_of_mem hm'), ho]⟩
    · exact ⟨0, rfl⟩

/-- **`fcvt` gives what `float.ext` and `float.trunc` allow.** -/
theorem fpConvert_allowed (x : Bits F) : ∃ o, fpConvert G x = Float.cvt G o x := by
  unfold fpConvert
  split
  · rename_i h
    have hm : quietAs G x ∈ ([x].filter isNaN).map (quietAs G) := by simp [h]
    obtain ⟨o, ho⟩ := nanResult_mem hm
    exact ⟨o, by rw [cvt_nan o h, ho]⟩
  · exact ⟨0, rfl⟩

/-! ## Conversions to integers -/

theorem fpToInt_satInt (signed : Bool) (n : Nat) (x : Bits F) :
    fpToInt signed n x = BitVec.ofInt n (Sem.satInt signed n x) := by
  unfold fpToInt Sem.satInt
  cases signed <;> cases decode x <;> simp

/-- **`fcvtzs` and `fcvtzu` are `float.to_int.s.sat` and `float.to_int.u.sat`.** -/
theorem fcvtz_sat (signed : Bool) (n : Nat) (x : Bits F) :
    Sem.floatToInt F signed .sat n (.bits x) = .ok (.bits (fpToInt signed n x)) := by
  rw [fpToInt_satInt]
  unfold Sem.floatToInt
  cases ht : truncInt x with
  | none => simp only [ht]
  | some v =>
    have hv : Sem.satInt signed n x = max (if signed then -(2 ^ (n - 1)) else 0)
        (min (if signed then 2 ^ (n - 1) - 1 else 2 ^ n - 1) v) := by
      have ht' := ht
      unfold Sem.satInt
      unfold truncInt at ht
      split at ht
      · rename_i heq
        simp only [heq, ht', Option.getD_some]
      · simp at ht
    simp only [ht, hv]
    cases signed <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> split
    all_goals first
      | rfl
      | (rename_i hr; rw [Int.min_eq_right hr.2, Int.max_eq_right hr.1])

/-! ## Arm's NaN choice as the oracle's -/

/-- The instruction instruction selection uses for a binary float op, if one. -/
def _root_.Fir.FBinOp.arm : FBinOp → Option FAluOp
  | .add => some .fadd
  | .sub => some .fsub
  | .mul => some .fmul
  | .div => some .fdiv
  | .copysign => none

/-- Arm's NaN choice as the oracle's (`Oracle.nan`, decision: NaN choice): for a float op on
defined operands of one format, an answer under which FIR's op gives what the instruction that
implements it gives (`fadd`, …, `fsqrt`, `fmadd` with the addend `c` of `float.fma a, b, c`,
`fcvt`). Chosen by the `*_allowed` theorems, so not computable; `fir run`'s counterpart is Rust's
`NanRule::Arm`, which computes the instructions' results directly. -/
noncomputable def armNan : OpKind → List RVal → Int
  | .floatBin op, [.float f (.bits a), .float g (.bits b)] =>
    if h : g = f then
      match op.arm with
      | some o => Classical.choose (fpAlu_allowed (F := f.fmt) o a (h ▸ b))
      | none => 0
    else 0
  | .floatUn .sqrt, [.float f (.bits a)] => Classical.choose (fpSqrt_allowed (F := f.fmt) a)
  | .floatFma, [.float f (.bits a), .float g (.bits b), .float k (.bits c)] =>
    if h : g = f ∧ k = f then
      Classical.choose (fpMulAdd_allowed (F := f.fmt) (h.2 ▸ c) a (h.1 ▸ b))
    else 0
  | .floatExt, [.float f (.bits a)] =>
    Classical.choose (fpConvert_allowed (F := f.fmt) (G := FloatTy.f64.fmt) a)
  | .floatTrunc, [.float f (.bits a)] =>
    Classical.choose (fpConvert_allowed (F := f.fmt) (G := FloatTy.f32.fmt) a)
  | _, _ => 0

/-- The oracle that answers 0 to every sequential choice and picks NaNs as Arm does. -/
noncomputable def _root_.Fir.Oracle.arm : Oracle := ⟨fun _ => 0, armNan⟩

/-- **Under Arm's NaN choice, `float.add` and friends are `fadd` and friends.** -/
theorem floatBin_arm {f : FloatTy} {op : FBinOp} {o : FAluOp} (ho : op.arm = some o)
    (a b : BitVec f.width) :
    Sem.floatBin f.fmt op (armNan (.floatBin op) [.float f (.bits a), .float f (.bits b)])
      (.bits a) (.bits b) = .bits (fpAlu o a b) := by
  have e := (Classical.choose_spec (fpAlu_allowed (F := f.fmt) o a b)).symm
  cases op <;> simp only [FBinOp.arm, reduceCtorEq, Option.some.injEq] at ho <;> subst ho <;>
    simp only [Sem.floatBin, armNan, FBinOp.arm, dite_true] <;> exact congrArg _ e

/-- **Under Arm's NaN choice, `float.sqrt` is `fsqrt`.** -/
theorem floatSqrt_arm {f : FloatTy} (a : BitVec f.width) :
    Sem.floatUn f.fmt .sqrt (armNan (.floatUn .sqrt) [.float f (.bits a)]) (.bits a) =
      .bits (fpSqrt a) := by
  simp only [Sem.floatUn, armNan]
  exact congrArg _ (Classical.choose_spec (fpSqrt_allowed (F := f.fmt) a)).symm

/-- **Under Arm's NaN choice, `float.fma %a, %b, %c` is `fmadd` with addend `%c`.** -/
theorem floatFma_arm {f : FloatTy} (a b c : BitVec f.width) :
    Sem.floatFma f.fmt (armNan .floatFma [.float f (.bits a), .float f (.bits b), .float f (.bits c)])
      (.bits a) (.bits b) (.bits c) = .bits (fpMulAdd c a b) := by
  simp only [Sem.floatFma, armNan, and_self, dite_true]
  exact congrArg _ (Classical.choose_spec (fpMulAdd_allowed (F := f.fmt) c a b)).symm

/-- **Under Arm's NaN choice, `float.ext` and `float.trunc` are `fcvt`.** -/
theorem floatExt_arm (a : BitVec FloatTy.f32.width) :
    Sem.floatCvt FloatTy.f32.fmt FloatTy.f64.fmt (armNan .floatExt [.float .f32 (.bits a)])
      (.bits a) = .bits (fpConvert FloatTy.f64.fmt a) := by
  simp only [Sem.floatCvt, armNan]
  exact congrArg _ (Classical.choose_spec (fpConvert_allowed (F := FloatTy.f32.fmt)
    (G := FloatTy.f64.fmt) a)).symm

theorem floatTrunc_arm (a : BitVec FloatTy.f64.width) :
    Sem.floatCvt FloatTy.f64.fmt FloatTy.f32.fmt (armNan .floatTrunc [.float .f64 (.bits a)])
      (.bits a) = .bits (fpConvert FloatTy.f32.fmt a) := by
  simp only [Sem.floatCvt, armNan]
  exact congrArg _ (Classical.choose_spec (fpConvert_allowed (F := FloatTy.f64.fmt)
    (G := FloatTy.f32.fmt) a)).symm

end Fir.AArch64
