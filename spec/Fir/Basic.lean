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

/-- A binary floating-point format (IEEE 754): the widths of the exponent field (`e`) and of the
trailing significand field (`m`). A value takes `1 + e + m` bits: the sign, then the exponent,
then the significand. -/
structure FloatFmt where
  e : Nat
  m : Nat
  deriving DecidableEq, Repr

/-- How many bits a value of the format takes. -/
def FloatFmt.width (F : FloatFmt) : Nat := F.e + F.m + 1

/-- The float types FIR builds (decision: Floats): IEEE 754 binary32 (`f32`) and binary64
(`f64`). `f16` and `bf16` are decided but not built. -/
inductive FloatTy where
  | f32
  | f64
  deriving DecidableEq, Repr

def FloatTy.fmt : FloatTy → FloatFmt
  | .f32 => ⟨8, 23⟩
  | .f64 => ⟨11, 52⟩

/-- The bit width: 32 or 64. -/
def FloatTy.width (f : FloatTy) : Nat := f.fmt.width

def FloatTy.name : FloatTy → String
  | .f32 => "f32"
  | .f64 => "f64"

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
  /-- Byte `i` of a `va_list` cursor (decision: va_list): at variadic argument `pos` of the call
  whose variadic arguments are allocation `area` (first tag `tag`). Copied exactly like any byte;
  read as anything but bytes, it is `poison`. Only `va.start` writes one. -/
  | va (area tag pos i : Nat)
  deriving DecidableEq, Repr

/-- Whether a byte is unspecified to everything but `va.arg`: `poison` itself, or a `va_list`
cursor's byte (decision: va_list). It reads as `poison`, and any byte refines it. -/
def Byte.opaque : Byte → Bool
  | .poison | .va .. => true
  | _ => false

/-- A runtime value. -/
inductive RVal where
  | int (w : Nat) (v : Val w)
  /-- A pointer; `none` is `poison`. -/
  | ptr (p : Option Ptr)
  /-- A value of a byte type `bN`: raw bytes, copied exactly. -/
  | bytes (bs : List Byte)
  /-- An HFIR aggregate value: a struct's fields or an array's elements in order, a slice's
  pointer and length, or a union's tag (an `i32`) and its variant's payload. There is no
  aggregate `poison`: `poison` stays in the scalars. -/
  | agg (vs : List RVal)
  /-- A float: its bits (decision: Floats), or `poison`. NaN payloads are bits like any other. -/
  | float (f : FloatTy) (v : Val f.width)
  deriving Repr

mutual
  /-- Equality of runtime values, by structure. (`deriving` doesn't handle the nested list.) -/
  def RVal.decEq : (a b : RVal) → Decidable (a = b)
    | .int w v, .int w' v' =>
      if h : w = w' then
        if hv : h ▸ v = v' then isTrue (by subst h; subst hv; rfl)
        else isFalse (by intro e; cases e; exact hv rfl)
      else isFalse (by intro e; cases e; exact h rfl)
    | .ptr p, .ptr p' =>
      if h : p = p' then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
    | .bytes bs, .bytes bs' =>
      if h : bs = bs' then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
    | .agg vs, .agg vs' =>
      match RVal.decEqList vs vs' with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | .float f v, .float f' v' =>
      if h : f = f' then
        if hv : h ▸ v = v' then isTrue (by subst h; subst hv; rfl)
        else isFalse (by intro e; cases e; exact hv rfl)
      else isFalse (by intro e; cases e; exact h rfl)
    | .int .., .ptr _ | .int .., .bytes _ | .int .., .agg _ | .ptr _, .int .. | .ptr _, .bytes _
    | .ptr _, .agg _ | .bytes _, .int .. | .bytes _, .ptr _ | .bytes _, .agg _ | .agg _, .int ..
    | .agg _, .ptr _ | .agg _, .bytes _ | .float .., .int .. | .float .., .ptr _
    | .float .., .bytes _ | .float .., .agg _ | .int .., .float .. | .ptr _, .float ..
    | .bytes _, .float .. | .agg _, .float .. => isFalse (by intro e; cases e)
  def RVal.decEqList : (a b : List RVal) → Decidable (a = b)
    | [], [] => isTrue rfl
    | v :: vs, v' :: vs' =>
      match RVal.decEq v v', RVal.decEqList vs vs' with
      | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
      | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | [], _ :: _ | _ :: _, [] => isFalse (by intro e; cases e)
end

instance : DecidableEq RVal := RVal.decEq

/-- Why a trap happened. Traps are precise and observable, so a correct rewrite must keep them. -/
inductive TrapReason where
  | div0
  | overflow
  | shift
  /-- `mem.alloc.trap` failed. -/
  | oom
  /-- An index outside a slice (`slice.get.trap`, `slice.set.trap`). -/
  | bounds
  /-- A union read as a variant it doesn't hold (`union.get.trap`). -/
  | tag
  /-- A float converted to an integer is NaN or out of range (`float.to_int.*.trap`). -/
  | convert
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
  /-- An index outside a slice (`slice.get.ub`, `slice.set.ub`). -/
  | bounds
  /-- A union read as a variant it doesn't hold (`union.get.ub`). -/
  | tag
  /-- A float converted to an integer is NaN or out of range (`float.to_int.*.ub`). -/
  | convert
  /-- `va.arg` of an object that doesn't hold a `va_list` cursor, past the last variadic
  argument, or of a type whose class (integer and pointer, or float) isn't the argument's. -/
  | vaArg
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
  /-- An exception escaped the function that was called (`exn.throw` with nothing to catch it),
  with this value. -/
  | threw (v : RVal)
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
  | .bounds => "bounds"
  | .tag => "tag"
  | .convert => "convert"

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
  | .bounds => "bounds"
  | .tag => "tag"
  | .convert => "convert"
  | .vaArg => "va-arg"

end Fir
