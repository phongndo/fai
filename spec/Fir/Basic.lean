/-!
# Runtime values and outcomes

The values FIR programs compute, and the outcomes of running one op or a whole function.
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

/-- A pointer. Its provenance says which allocation it may access.

Allocations get a numeric address lazily, the first time one is observed, so a pointer derived
from an allocation is stored relative to it. -/
inductive Ptr where
  /-- Into allocation `alloc`, derived through tag `tag`, at byte offset `off`. The offset may be
  out of bounds; accessing it there is UB. -/
  | rel (alloc tag : Nat) (off : Int)
  /-- A bare address, from `ptr.from_exposed` or `ptr.null`. `cands` are the exposed
  `(allocation, tag)` pairs it may belong to; the one that makes an access valid is chosen when
  the pointer is used (ISO C's "user disambiguation"). No candidates means no provenance. -/
  | abs (addr : Nat) (cands : List (Nat × Nat))
  deriving DecidableEq, Repr

def Ptr.null : Ptr := .abs 0 []

/-- A byte in memory. -/
inductive Byte where
  | bits (b : BitVec 8)
  /-- Never written, or written with `poison`. -/
  | poison
  /-- Byte `i` of pointer `p`, which keeps its provenance when copied. -/
  | frag (p : Ptr) (i : Nat)
  deriving DecidableEq, Repr

/-- A runtime value. -/
inductive RVal where
  | int (w : Nat) (v : Val w)
  /-- A pointer; `none` is `poison`. -/
  | ptr (p : Option Ptr)
  /-- A value of a byte type `bN`: raw bytes, copied exactly. -/
  | bytes (bs : List Byte)
  deriving DecidableEq, Repr

/-- Why a trap happened. Traps are precise and observable, so a correct rewrite must keep them. -/
inductive TrapReason where
  | div0
  | overflow
  | shift
  /-- `mem.alloc.trap` failed. -/
  | oom
  deriving DecidableEq, Repr

/-- Which rule a program broke when its behavior is undefined. Refinement ignores the kind;
tools use it to explain the UB. -/
inductive UBKind where
  | div0
  | overflow
  | shift
  /-- A poison value was used where a defined value is required. -/
  | poison
  /-- A value violated a fact written on it. -/
  | fact
  /-- A `cf.loop progress` never exited. -/
  | noProgress
  /-- An access through a pointer with no provenance, such as null. -/
  | noProvenance
  | outOfBounds
  | useAfterFree
  | misaligned
  | doubleFree
  /-- `mem.free` of a pointer that isn't the start of a live heap allocation of that family. -/
  | badFree
  /-- An access that breaks a `noalias` fact. -/
  | noalias
  /-- A write through a pointer derived from a `readonly` one. -/
  | readonly
  /-- An ordered comparison of pointers into different allocations. -/
  | ptrCompare
  /-- No free address range was left when an allocation needed an address. -/
  | addressSpace
  /-- A write to a `const` global. -/
  | constWrite
  /-- A load or store through a pointer to a function. -/
  | funcAccess
  /-- An indirect call through a pointer that isn't the start of a function of the call's
  signature. -/
  | badCall
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

/-- How a run ends, after its events. -/
inductive Outcome where
  | ret (vs : List RVal)
  | trap (r : TrapReason)
  | ub (k : UBKind)
  /-- Runs forever without another event. -/
  | diverge
  /-- Reached a hole (`?name`) that has no value yet. -/
  | hole (name : String)
  /-- The program is malformed. Verified programs never get stuck. -/
  | stuck (msg : String)
  /-- The run reached a choice the reference semantics doesn't decide yet: an address that may
  belong to several exposed (allocation, tag) pairs, where the choice changes what happens. The
  intended rule picks the pair that avoids UB; until that is implemented, the run's behavior is
  unknown, so it refines nothing and is refined by nothing but UB. -/
  | ambiguous
  deriving DecidableEq, Repr

/-- An observable event: a call to an external function, with the arguments it was passed and
the results the environment returned (`none`: the call never returned). -/
structure Event where
  callee : String
  args : List RVal
  results : Option (List RVal)
  deriving DecidableEq, Repr

/-- What running a function does, as seen from outside: a trace of events. A finite trace ends
in an outcome (`diverge` if the run goes on forever without another event); a run with
infinitely many events has no outcome. -/
inductive Behavior where
  | fin (es : List Event) (o : Outcome)
  | inf (es : Nat → Event)

def TrapReason.name : TrapReason → String
  | .div0 => "div0"
  | .overflow => "overflow"
  | .shift => "shift"
  | .oom => "oom"

def UBKind.name : UBKind → String
  | .div0 => "div0"
  | .overflow => "overflow"
  | .shift => "shift"
  | .poison => "poison"
  | .fact => "fact"
  | .noProgress => "no-progress"
  | .noProvenance => "no-provenance"
  | .outOfBounds => "out-of-bounds"
  | .useAfterFree => "use-after-free"
  | .misaligned => "misaligned"
  | .doubleFree => "double-free"
  | .badFree => "bad-free"
  | .noalias => "noalias"
  | .readonly => "readonly"
  | .ptrCompare => "ptr-compare"
  | .addressSpace => "address-space"
  | .constWrite => "const-write"
  | .funcAccess => "func-access"
  | .badCall => "bad-call"

end Fir
