/-!
# Runtime values and outcomes

The values FIR-0 programs compute, and the outcomes of running one op or a whole function.
-/

namespace Fir

/-- An integer value of width `w`: concrete bits, or `poison` (deferred UB). -/
inductive Val (w : Nat) where
  | poison
  | bits (b : BitVec w)
  deriving DecidableEq, Repr

def Val.isPoison : Val w → Bool
  | .poison => true
  | .bits _ => false

/-- Why a trap happened. Traps are precise and observable, so a correct rewrite must keep them. -/
inductive TrapReason where
  | div0
  | overflow
  | shift
  deriving DecidableEq, Repr

/-- Which rule a program broke when its behavior is undefined. Refinement ignores the kind;
tools use it to explain the UB. -/
inductive UBKind where
  | div0
  | overflow
  | shift
  /-- A poison value was used where a defined value is required (a branch condition, or an
  input of an op that traps or has UB on some inputs). -/
  | poison
  /-- A value violated a fact written on it. -/
  | fact
  /-- A `cf.loop progress` never exited. -/
  | noProgress
  deriving DecidableEq, Repr

/-- The outcome of evaluating one op with result width `w`. -/
inductive OpOut (w : Nat) where
  | ok (v : Val w)
  | trap (r : TrapReason)
  | ub (k : UBKind)
  deriving DecidableEq, Repr

/-- Continue with the result of an op, propagating traps and UB. -/
def OpOut.bind : OpOut w → (Val w → OpOut v) → OpOut v
  | .ok x, f => f x
  | .trap r, _ => .trap r
  | .ub k, _ => .ub k

/-- A runtime value whose width is only known at runtime, as stored in an environment. -/
structure RVal where
  w : Nat
  v : Val w
  deriving DecidableEq, Repr

/-- What running a function does, as seen from outside. -/
inductive Behavior where
  | ret (vs : List RVal)
  | trap (r : TrapReason)
  | ub (k : UBKind)
  /-- Runs forever. -/
  | diverge
  /-- Reached a hole (`?name`) that has no value yet. -/
  | hole (name : String)
  /-- The program is malformed. Verified programs never get stuck. -/
  | stuck (msg : String)
  deriving DecidableEq, Repr

def TrapReason.name : TrapReason → String
  | .div0 => "div0"
  | .overflow => "overflow"
  | .shift => "shift"

def UBKind.name : UBKind → String
  | .div0 => "div0"
  | .overflow => "overflow"
  | .shift => "shift"
  | .poison => "poison"
  | .fact => "fact"
  | .noProgress => "no-progress"

end Fir
