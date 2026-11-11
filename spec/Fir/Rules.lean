import Std.Tactic.BVDecide
import Fir.Refinement
import Fir.Sem

/-!
# First proved rewrite rules

Each rule says: the right-hand side refines the left-hand side, for every input (including
`poison`) and, unless stated otherwise, every bit width.
-/

namespace Fir.Rules

open Sem

/-- `int.mul.wrap %x, 2` → `int.add.wrap %x, %x`.

Sound with `poison`, since both sides give `poison` exactly when `%x` is `poison`. (LLVM's old
`undef` broke this rule: the two uses of an `undef` `%x` could differ, so `%x + %x` could be odd.) -/
theorem mul_two (x : Val w) :
    (arith .add .wrap x x).Refines (arith .mul .wrap x (const w 2)) := by
  cases x with
  | poison => simp [arith, Ovf.needsDefined, OpOut.Refines, Val.Refines]
  | bits a =>
    simp only [arith, const, arithBits, wrapOp, OpOut.Refines, Val.Refines]
    rw [show BitVec.ofInt w 2 = 2#w by simp [BitVec.ofInt_ofNat], BitVec.mul_two]

/-- `int.add.<any> %x, 0` → `%x`, for every overflow behavior: adding zero never overflows. -/
theorem add_zero (ovf : Ovf) (x : Val w) :
    (OpOut.ok x).Refines (arith .add ovf x (const w 0)) := by
  cases x with
  | poison =>
    cases ovf <;> simp [arith, Ovf.needsDefined, OpOut.Refines, Val.Refines]
  | bits a =>
    have hs : a.saddOverflow 0#w = false := by
      simp [BitVec.saddOverflow, BitVec.toInt_lt, BitVec.le_toInt]
    have hu : a.uaddOverflow 0#w = false := by
      simp [BitVec.uaddOverflow, a.isLt]
    rcases ovf with _ | _ | _ | _ | s | s | s <;> (try cases s) <;>
      simp [arith, arithBits, const, wrapOp, overflow, overflowS, overflowU, hs, hu,
        OpOut.Refines, Val.Refines]

/-- `int.cmp.sgt (int.add.nsw %x, 1), %x` → `int.const 1` (true), for widths of at least 2.

When `%x + 1` overflows, the `.nsw` add gives `poison`, and `poison` may be replaced by anything.
Otherwise `%x + 1` really is greater than `%x`. -/
theorem add_nsw_one_sgt (hw : 2 ≤ w) (x : Val w) :
    (OpOut.ok (const 1 1)).Refines
      ((arith .add .nsw x (const w 1)).bind fun y => .ok (cmp .sgt y x)) := by
  cases x with
  | poison => simp [arith, Ovf.needsDefined, OpOut.bind, cmp, OpOut.Refines, Val.Refines]
  | bits a =>
    have hc : BitVec.ofInt w 1 = 1#w := by simp
    simp only [arith, arithBits, wrapOp, overflowS, const, OpOut.bind, hc]
    by_cases hov : a.saddOverflow 1#w = true
    · simp [hov, cmp, OpOut.Refines, Val.Refines]
    · have hsum := BitVec.toInt_add_of_not_saddOverflow hov
      have hlt : a.toInt < a.toInt + 1 := by omega
      simp [hlt, hov, cmp, cmpBits, OpOut.Refines, Val.Refines, BitVec.slt, hsum,
        BitVec.toInt_one (by omega : 1 < w)]

/-- The same rewrite with `.wrap` is wrong, and Lean rejects it: at `i32`, `%x = MAX` wraps to
`MIN`, and `MIN > MAX` is false. This is the kind of rule that has caused real miscompiles. -/
theorem add_wrap_one_sgt_wrong :
    ¬ ∀ x : Val 32, (OpOut.ok (const 1 1)).Refines
      ((arith .add .wrap x (const 32 1)).bind fun y => .ok (cmp .sgt y x)) := by
  intro h
  have := OpOut.refines_iff.mpr (h (.bits (BitVec.intMax 32)))
  revert this
  decide

/-- Why `add_nsw_one_sgt` needs `2 ≤ w`: in `i1`, the constant `1` is the bit pattern `1`, which
is `-1` as a signed value. So `%x + 1` is `%x - 1`, and at `%x = 0` the rewrite is wrong. -/
theorem add_nsw_one_sgt_wrong_at_i1 :
    ¬ ∀ x : Val 1, (OpOut.ok (const 1 1)).Refines
      ((arith .add .nsw x (const 1 1)).bind fun y => .ok (cmp .sgt y x)) := by
  intro h
  have := OpOut.refines_iff.mpr (h (.bits 0))
  revert this
  decide

end Fir.Rules
