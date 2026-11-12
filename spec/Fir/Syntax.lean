/-!
# Syntax

The shape of a FIR-0 program. Following the structure decision, everything is an op: an op has a
kind, typed results, operands, nested regions, and a source location. A region has typed
parameters (block arguments) and a list of ops.

FIR-1 covers integers, structured control flow, memory, and calls between FIR functions. Floats,
external calls, and threads come later.
-/

namespace Fir

/-- A source location, `@line:col`. -/
structure Loc where
  line : Nat
  col : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A type: signless integers `iN`, pointers, and byte types `bN` (raw memory, copied exactly). -/
inductive Ty where
  | int (w : Nat)
  | ptr
  | byte (w : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The bit width of an integer or byte type. -/
def Ty.width : Ty → Nat
  | .int w | .byte w => w
  | .ptr => 0

def Ty.isInt : Ty → Bool
  | .int _ => true
  | _ => false

instance : ToString Ty := ⟨fun
  | .int w => s!"i{w}"
  | .ptr => "ptr"
  | .byte w => s!"b{w}"⟩

/-- A memory space's sizes, in bits. The pointer size is how much memory a pointer takes; the
address (index) size is what `ptr.addr`, offsets, and allocation sizes use. -/
structure SpaceCfg where
  ptrBits : Nat := 64
  addrBits : Nat := 64
  deriving DecidableEq, Repr, Inhabited

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
  /-- A pointer that isn't null. -/
  | nonnull
  /-- A pointer aligned to `n` bytes. -/
  | align (n : Nat)
  /-- On a function parameter: for the call, a byte accessed through this pointer (or one
  derived from it) and written by anyone may only be accessed through derived pointers. -/
  | noalias
  /-- On a function parameter: no writes through this pointer or ones derived from it during
  the call. -/
  | readonly
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

/-- What `mem.alloc` does when allocation fails. -/
inductive AllocFail where
  /-- Return null, like C `malloc`. -/
  | null
  /-- Trap, like Rust and Java. -/
  | trap
  deriving DecidableEq, Repr

inductive OpKind where
  /-- `int.const n` -/
  | const (n : Int)
  | poison
  | freeze
  /-- `copy %x`: the same value, of any type. Rewrites produce it (store-to-load forwarding
  turns a load into a copy of the stored value), and copy propagation removes it. -/
  | copy
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
  /-- `mem.stack 16, align 4`: stack memory, freed when its region ends. -/
  | memStack (size align : Nat)
  /-- `mem.alloc.null c.malloc %n, align 16`: heap memory from an allocator family. -/
  | memAlloc (fail : AllocFail) (family : String) (align : Nat)
  /-- `mem.free c.malloc %p` -/
  | memFree (family : String)
  /-- `mem.load %p, align 4`: the result type is the accessed type. -/
  | load (align : Nat)
  /-- `mem.store i32 %v, %p, align 4` -/
  | store (ty : Ty) (align : Nat)
  /-- `ptr.offset.inbounds %p, %n` (poison if it leaves the allocation) or `ptr.offset.wrap`. -/
  | ptrOffset (inbounds : Bool)
  /-- `ptr.addr %p`: the address, without exposing the allocation. -/
  | ptrAddr
  /-- `ptr.expose %p`: the address, and `ptr.from_exposed` may reach the allocation from now on. -/
  | ptrExpose
  | ptrFromExposed
  /-- `ptr.with_addr %p, %a`: a new address in `%p`'s allocation. -/
  | ptrWithAddr
  | ptrNull
  /-- `ptr.cmp.eq` and friends; ordered comparisons are unsigned. -/
  | ptrCmp (p : Pred)
  /-- `func.call @f(%a, %b)` -/
  | call (callee : String)
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
  /-- A region's parameters are written like results, and can carry facts. -/
  inductive Region where
    | mk (params : List Result) (ops : List Op)
end

instance : Inhabited Op := ⟨.mk .poison [] [] [] none⟩
instance : Inhabited Region := ⟨.mk [] []⟩

def Op.kind : Op → OpKind | .mk k .. => k
def Op.results : Op → List Result | .mk _ rs .. => rs
def Op.args : Op → List Operand | .mk _ _ as .. => as
def Op.regions : Op → List Region | .mk _ _ _ rs _ => rs
def Op.loc : Op → Option Loc | .mk _ _ _ _ l => l
def Region.params : Region → List Result | .mk ps _ => ps
def Region.ops : Region → List Op | .mk _ ops => ops

/-- A function. Its parameters are the parameters of its body region. -/
structure Func where
  name : String
  rets : List Ty
  file : Option String
  body : Region
  deriving Inhabited

def Func.params (f : Func) : List Result := f.body.params

structure Module where
  /-- The default memory space. -/
  space : SpaceCfg := {}
  funcs : List Func

def Module.find? (m : Module) (name : String) : Option Func :=
  m.funcs.find? (·.name == name)

end Fir
