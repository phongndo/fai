import Fir.Basic
import Fir.Syntax

/-!
# Op semantics

What each FIR-0 op computes, as a function from input values to an outcome. The interpreter, the
verifier's constant checks, and the rewrite proofs all use these same definitions.

Two rules apply to every op:

* `poison` in, `poison` out.
* Exception: an op that can trap or has UB on some inputs needs those inputs defined. A `poison`
  input there is UB, since it might be the input that hits the edge case.
-/

namespace Fir.Sem

open BitVec

/-- An `iN` constant. Literals may be written signed or unsigned; both wrap to `w` bits. -/
def const (w : Nat) (n : Int) : Val w := .bits (BitVec.ofInt w n)

/-! ## Add, sub, mul -/

def wrapOp : ArithOp → BitVec w → BitVec w → BitVec w
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

def overflowS : ArithOp → BitVec w → BitVec w → Bool
  | .add, a, b => a.saddOverflow b
  | .sub, a, b => a.ssubOverflow b
  | .mul, a, b => a.smulOverflow b

def overflowU : ArithOp → BitVec w → BitVec w → Bool
  | .add, a, b => a.uaddOverflow b
  | .sub, a, b => a.usubOverflow b
  | .mul, a, b => a.umulOverflow b

def overflow (signed : Bool) : ArithOp → BitVec w → BitVec w → Bool :=
  if signed then overflowS else overflowU

def exact : ArithOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- The exact result clamped to the representable range. -/
def saturate (signed : Bool) (op : ArithOp) (a b : BitVec w) : BitVec w :=
  if signed then
    let r := exact op a.toInt b.toInt
    BitVec.ofInt w (max (-(2 ^ (w - 1))) (min r (2 ^ (w - 1) - 1)))
  else
    let r := exact op a.toNat b.toNat
    BitVec.ofInt w (max 0 (min r (2 ^ w - 1)))

def arithBits (op : ArithOp) : Ovf → BitVec w → BitVec w → OpOut w
  | .wrap, a, b => .ok (.bits (wrapOp op a b))
  | .nsw, a, b => .ok (if overflowS op a b then .poison else .bits (wrapOp op a b))
  | .nuw, a, b => .ok (if overflowU op a b then .poison else .bits (wrapOp op a b))
  | .nswNuw, a, b =>
    .ok (if overflowS op a b || overflowU op a b then .poison else .bits (wrapOp op a b))
  | .trap s, a, b => if overflow s op a b then .trap .overflow else .ok (.bits (wrapOp op a b))
  | .ub s, a, b => if overflow s op a b then .ub .overflow else .ok (.bits (wrapOp op a b))
  | .sat s, a, b =>
    .ok (.bits (if overflow s op a b then saturate s op a b else wrapOp op a b))

def _root_.Fir.Ovf.needsDefined : Ovf → Bool
  | .trap _ | .ub _ => true
  | _ => false

def arith (op : ArithOp) (ovf : Ovf) : Val w → Val w → OpOut w
  | .bits a, .bits b => arithBits op ovf a b
  | _, _ => if ovf.needsDefined then .ub .poison else .ok .poison

/-! ## Bitwise -/

def bit (op : BitOp) : Val w → Val w → Val w
  | .bits a, .bits b =>
    .bits (match op with
      | .and => a &&& b
      | .or => a ||| b
      | .xor => a ^^^ b)
  | _, _ => .poison

/-! ## Division and remainder -/

def divBits : DivOp → BitVec w → BitVec w → BitVec w
  | .divS, a, b => a.sdiv b
  | .divU, a, b => a.udiv b
  | .remS, a, b => a.srem b
  | .remU, a, b => a.umod b

def _root_.Fir.Edge.needsDefined : Edge → Bool
  | .ub | .trap => true
  | _ => false

/-- `zero` applies to a zero divisor; `ovf` applies to signed `MIN / -1`.
`divBits` already gives the `total` and `wrap` results (`x / 0 = 0`, `x rem 0 = x`,
`MIN / -1 = MIN`, `MIN rem -1 = 0`). -/
def div (op : DivOp) (zero ovf : Edge) : Val w → Val w → OpOut w
  | _, .poison => if zero.needsDefined then .ub .poison else .ok .poison
  | a, .bits b =>
    if b = 0 then
      match zero, a with
      | .ub, _ => .ub .div0
      | .trap, _ => .trap .div0
      | _, .poison => .ok .poison
      | _, .bits x => .ok (.bits (divBits op x b))
    else
      match a with
      | .poison =>
        if op.signed && ovf.needsDefined then .ub .poison else .ok .poison
      | .bits x =>
        if op.signed && x = BitVec.intMin w && b = BitVec.allOnes w then
          match ovf with
          | .ub => .ub .overflow
          | .trap => .trap .overflow
          | _ => .ok (.bits (divBits op x b))
        else .ok (.bits (divBits op x b))

/-! ## Shifts -/

def shiftBits : ShiftOp → BitVec w → Nat → BitVec w
  | .shl, a, n => a <<< n
  | .shrU, a, n => a >>> n
  | .shrS, a, n => a.sshiftRight n

def _root_.Fir.ShiftEdge.needsDefined : ShiftEdge → Bool
  | .ub | .trap => true
  | _ => false

/-- The amount is read as unsigned. -/
def shift (op : ShiftOp) (edge : ShiftEdge) : Val w → Val w → OpOut w
  | _, .poison => if edge.needsDefined then .ub .poison else .ok .poison
  | a, .bits n =>
    if n.toNat < w then
      match a with
      | .poison => .ok .poison
      | .bits x => .ok (.bits (shiftBits op x n.toNat))
    else
      match edge, a with
      | .ub, _ => .ub .shift
      | .trap, _ => .trap .shift
      | _, .poison => .ok .poison
      | .mask, .bits x => .ok (.bits (shiftBits op x (n.toNat % w)))
      | _, .bits x => .ok (.bits (shiftBits op x n.toNat))

/-! ## Comparison, selection, casts -/

def cmpBits : Pred → BitVec w → BitVec w → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .slt, a, b => a.slt b
  | .sle, a, b => a.sle b
  | .sgt, a, b => b.slt a
  | .sge, a, b => b.sle a
  | .ult, a, b => a.ult b
  | .ule, a, b => a.ule b
  | .ugt, a, b => b.ult a
  | .uge, a, b => b.ule a

def cmp (p : Pred) : Val w → Val w → Val 1
  | .bits a, .bits b => .bits (BitVec.ofBool (cmpBits p a b))
  | _, _ => .poison

def select : Val 1 → Val w → Val w → Val w
  | .bits c, a, b => if c = 1 then a else b
  | .poison, _, _ => .poison

def zext (v : Nat) : Val w → Val v
  | .bits a => .bits (a.setWidth v)
  | .poison => .poison

def sext (v : Nat) : Val w → Val v
  | .bits a => .bits (a.signExtend v)
  | .poison => .poison

def trunc (mode : TruncMode) (v : Nat) : Val w → Val v
  | .poison => .poison
  | .bits a =>
    let r := a.setWidth v
    match mode with
    | .wrap => .bits r
    | .nsw => if r.signExtend w = a then .bits r else .poison
    | .nuw => if r.setWidth w = a then .bits r else .poison

/-! ## Facts -/

/-- Whether a value satisfies a fact. `poison` satisfies every fact. -/
def _root_.Fir.Fact.holds : Fact → Val w → Bool
  | _, .poison => true
  | .rangeS lo hi, .bits b => lo ≤ b.toInt && b.toInt ≤ hi
  | .rangeU lo hi, .bits b => lo ≤ (b.toNat : Int) && (b.toNat : Int) ≤ hi

end Fir.Sem
