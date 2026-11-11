/-!
# Syntax

The shape of a FIR-0 program. Following the structure decision, everything is an op: an op has a
kind, typed results, operands, nested regions, and a source location. A region has typed
parameters (block arguments) and a list of ops.

FIR-0 covers integers and structured control flow. Memory, calls, and floats come later.
-/

namespace Fir

/-- A source location, `@line:col`. -/
structure Loc where
  line : Nat
  col : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A type. FIR-0 has only signless integers `iN`. -/
inductive Ty where
  | int (w : Nat)
  deriving DecidableEq, Repr, Inhabited

def Ty.width : Ty → Nat
  | .int w => w

instance : ToString Ty := ⟨fun t => s!"i{t.width}"⟩

/-- How much a fact is trusted. All three mean the same thing (a violation is UB); they differ in
how the compiler treats the fact: relied on, checked at runtime, or proved. -/
inductive Trust where
  | assume
  | check
  | proved
  deriving DecidableEq, Repr

/-- A claim about a value. Facts constrain defined values only; `poison` passes. -/
inductive Fact where
  /-- Signed range, inclusive. -/
  | rangeS (lo hi : Int)
  /-- Unsigned range, inclusive. -/
  | rangeU (lo hi : Int)
  deriving DecidableEq, Repr

structure TrustedFact where
  fact : Fact
  trust : Trust
  deriving DecidableEq, Repr

/-- Overflow behavior of `int.add`, `int.sub`, and `int.mul`, written as the op's modifiers. -/
inductive Ovf where
  /-- `.wrap`: two's-complement wraparound. -/
  | wrap
  /-- `.nsw`: signed overflow gives `poison`. -/
  | nsw
  /-- `.nuw`: unsigned overflow gives `poison`. -/
  | nuw
  /-- `.nsw.nuw`: either overflow gives `poison`. -/
  | nswNuw
  /-- `.s.trap` / `.u.trap`: overflow traps. -/
  | trap (signed : Bool)
  /-- `.s.sat` / `.u.sat`: overflow clamps to the nearest representable value. -/
  | sat (signed : Bool)
  /-- `.s.ub` / `.u.ub`: overflow is immediate UB. -/
  | ub (signed : Bool)
  deriving DecidableEq, Repr

/-- Edge-case behaviors of division and remainder. The first modifier names the behavior on a zero
divisor (`ub`, `trap`, or `total`); signed ops name a second one for `MIN / -1` (`ub`, `trap`, or
`wrap`). A single modifier covers both cases: `.ub` means both are UB, `.trap` means both trap, and
`.total` means a zero divisor gives a defined result and `MIN / -1` wraps. -/
inductive Edge where
  | ub
  | trap
  /-- A zero divisor gives a defined result: `x / 0 = 0` and `x rem 0 = x`. -/
  | total
  /-- `MIN / -1 = MIN` and `MIN rem -1 = 0`. -/
  | wrap
  deriving DecidableEq, Repr

/-- Behavior of shifts when the amount is at least the bit width. -/
inductive ShiftEdge where
  | ub
  | trap
  /-- The amount is taken modulo the width (x86, Wasm). -/
  | mask
  /-- All bits are shifted out: `0`, or the sign bit for `shr.s`. -/
  | total
  deriving DecidableEq, Repr

/-- Behavior of `int.trunc` when bits are lost. -/
inductive TruncMode where
  | wrap
  | nsw
  | nuw
  deriving DecidableEq, Repr

inductive Pred where
  | eq | ne | slt | sle | sgt | sge | ult | ule | ugt | uge
  deriving DecidableEq, Repr

inductive ArithOp where
  | add | sub | mul
  deriving DecidableEq, Repr

inductive BitOp where
  | and | or | xor
  deriving DecidableEq, Repr

inductive DivOp where
  | divS | divU | remS | remU
  deriving DecidableEq, Repr

def DivOp.signed : DivOp → Bool
  | .divS | .remS => true
  | .divU | .remU => false

inductive ShiftOp where
  | shl | shrU | shrS
  deriving DecidableEq, Repr

inductive OpKind where
  /-- `int.const n` -/
  | const (n : Int)
  | poison
  | freeze
  /-- `select %c, %a, %b` -/
  | select
  | arith (op : ArithOp) (ovf : Ovf)
  | bit (op : BitOp)
  | div (op : DivOp) (zero ovf : Edge)
  | shift (op : ShiftOp) (edge : ShiftEdge)
  | cmp (p : Pred)
  | zext
  | sext
  | trunc (mode : TruncMode)
  /-- `cf.if %c { … } else { … }`: two regions. -/
  | if_
  /-- `cf.loop [progress] iter(…) { … }`: one region whose parameters are the loop state. -/
  | loop (progress : Bool)
  /-- `cf.yield`: ends a `cf.if` region with the `cf.if`'s results. -/
  | yield
  /-- `cf.break`: leaves the nearest loop with the loop's results. -/
  | brk
  /-- `cf.continue`: starts the next iteration with new loop state. -/
  | cont
  /-- `func.ret` -/
  | ret
  deriving DecidableEq, Repr

def OpKind.isTerminator : OpKind → Bool
  | .yield | .brk | .cont | .ret => true
  | _ => false

/-- An operand: a value, or a hole `?name: T` standing for a value not written yet. -/
inductive Operand where
  | var (name : String)
  | hole (name : String) (ty : Ty)
  deriving DecidableEq, Repr

/-- A result: its name, its type, and the facts written on it. -/
structure Result where
  name : String
  ty : Ty
  facts : List TrustedFact := []
  deriving DecidableEq, Repr

mutual
  inductive Op where
    | mk (kind : OpKind) (results : List Result) (args : List Operand) (regions : List Region)
        (loc : Option Loc)
  inductive Region where
    | mk (params : List (String × Ty)) (ops : List Op)
end

instance : Inhabited Op := ⟨.mk .poison [] [] [] none⟩
instance : Inhabited Region := ⟨.mk [] []⟩

def Op.kind : Op → OpKind | .mk k .. => k
def Op.results : Op → List Result | .mk _ rs .. => rs
def Op.args : Op → List Operand | .mk _ _ as .. => as
def Op.regions : Op → List Region | .mk _ _ _ rs _ => rs
def Op.loc : Op → Option Loc | .mk _ _ _ _ l => l
def Region.params : Region → List (String × Ty) | .mk ps _ => ps
def Region.ops : Region → List Op | .mk _ ops => ops

/-- A function. Its parameters are the parameters of its body region. -/
structure Func where
  name : String
  rets : List Ty
  file : Option String
  body : Region
  deriving Inhabited

def Func.params (f : Func) : List (String × Ty) := f.body.params

structure Module where
  funcs : List Func

def Module.find? (m : Module) (name : String) : Option Func :=
  m.funcs.find? (·.name == name)

end Fir
