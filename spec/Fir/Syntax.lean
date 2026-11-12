import Fir.Basic
import Fir.Float
import Fir.OpDSL
import Fir.AArch64Syntax

/-!
# Syntax

The shape of a FIR-0 program. Following the structure decision, everything is an op: an op has a
kind, typed results, operands, nested regions, and a source location. A region has typed
parameters (block arguments) and a list of ops.

FIR-1 covers integers, structured control flow, memory, and calls between FIR functions, with
structs and arrays in memory, globals, and calls through function pointers; external functions
and floats (`f32`, `f64`) came after. Threads come later.
-/

namespace Fir

/-- A source location, `@line:col`. -/
structure Loc where
  line : Nat
  col : Nat
  deriving DecidableEq, Repr, Inhabited

/-- How a struct's fields are laid out (decision: Layout). -/
inductive Policy where
  /-- `struct<C>`: the platform C layout. -/
  | c
  /-- `struct<packed>`: no padding, alignment 1. -/
  | packed
  /-- `struct<auto>`: FIR picks the order (now: by decreasing alignment). -/
  | auto
  deriving DecidableEq, Repr, Inhabited

def Policy.name : Policy → String
  | .c => "C"
  | .packed => "packed"
  | .auto => "auto"

/-- A type. Values have the *value types*: signless integers `iN`, pointers, byte types `bN`
(raw memory, copied exactly), and floats. Structs and arrays describe memory, and function types
describe calls; neither is a value type (decision: Aggregates). -/
inductive Ty where
  | int (w : Nat)
  | ptr
  | byte (w : Nat)
  /-- `struct<C>{i32, ptr}` -/
  | struct (policy : Policy) (fields : List Ty)
  /-- `array<4 x i32>` -/
  | array (n : Nat) (elem : Ty)
  /-- `func<(i32, ptr) -> i32>` -/
  | func (params rets : List Ty)
  /-- `union<i32, ptr>`: an HFIR tagged union, holding one of its variants and a tag saying
  which. Unions are SSA values only: they have no layout. -/
  | union (variants : List Ty)
  /-- `slice`: an HFIR pointer and a length (an address-sized integer, counting elements), laid
  out as `struct<C>{ptr, iA}`. Like `ptr`, it doesn't name its element type; the ops do. -/
  | slice
  /-- `f32` or `f64`: an IEEE 754 float (decision: Floats). -/
  | float (f : FloatTy)
  deriving Repr, Inhabited

mutual
  /-- Equality of types, by structure. (`deriving` doesn't handle the nested lists.) -/
  def Ty.decEq : (a b : Ty) → Decidable (a = b)
    | .int w, .int w' =>
      if h : w = w' then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
    | .ptr, .ptr => isTrue rfl
    | .byte w, .byte w' =>
      if h : w = w' then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
    | .struct p fs, .struct p' fs' =>
      if hp : p = p' then
        match Ty.decEqList fs fs' with
        | isTrue h => isTrue (by rw [hp, h])
        | isFalse h => isFalse (by intro e; cases e; exact h rfl)
      else isFalse (by intro e; cases e; exact hp rfl)
    | .array n t, .array n' t' =>
      if hn : n = n' then
        match Ty.decEq t t' with
        | isTrue h => isTrue (by rw [hn, h])
        | isFalse h => isFalse (by intro e; cases e; exact h rfl)
      else isFalse (by intro e; cases e; exact hn rfl)
    | .func ps rs, .func ps' rs' =>
      match Ty.decEqList ps ps', Ty.decEqList rs rs' with
      | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
      | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | .union vs, .union vs' =>
      match Ty.decEqList vs vs' with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | .slice, .slice => isTrue rfl
    | .float f, .float f' =>
      if h : f = f' then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
    | .int _, .ptr | .int _, .byte _ | .int _, .struct .. | .int _, .array .. | .int _, .func ..
    | .int _, .union _ | .int _, .slice | .int _, .float _ | .ptr, .int _ | .ptr, .byte _
    | .ptr, .struct .. | .ptr, .array .. | .ptr, .func .. | .ptr, .union _ | .ptr, .slice
    | .ptr, .float _ | .byte _, .int _ | .byte _, .ptr | .byte _, .struct .. | .byte _, .array ..
    | .byte _, .func .. | .byte _, .union _ | .byte _, .slice | .byte _, .float _
    | .struct .., .int _ | .struct .., .ptr | .struct .., .byte _ | .struct .., .array ..
    | .struct .., .func .. | .struct .., .union _ | .struct .., .slice | .struct .., .float _
    | .array .., .int _ | .array .., .ptr | .array .., .byte _ | .array .., .struct ..
    | .array .., .func .. | .array .., .union _ | .array .., .slice | .array .., .float _
    | .func .., .int _ | .func .., .ptr | .func .., .byte _ | .func .., .struct ..
    | .func .., .array .. | .func .., .union _ | .func .., .slice | .func .., .float _
    | .union _, .int _ | .union _, .ptr | .union _, .byte _ | .union _, .struct ..
    | .union _, .array .. | .union _, .func .. | .union _, .slice | .union _, .float _
    | .slice, .int _ | .slice, .ptr | .slice, .byte _ | .slice, .struct .. | .slice, .array ..
    | .slice, .func .. | .slice, .union _ | .slice, .float _ | .float _, .int _ | .float _, .ptr
    | .float _, .byte _ | .float _, .struct .. | .float _, .array .. | .float _, .func ..
    | .float _, .union _ | .float _, .slice =>
      isFalse (by intro e; cases e)
  def Ty.decEqList : (a b : List Ty) → Decidable (a = b)
    | [], [] => isTrue rfl
    | t :: ts, t' :: ts' =>
      match Ty.decEq t t', Ty.decEqList ts ts' with
      | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
      | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
    | [], _ :: _ | _ :: _, [] => isFalse (by intro e; cases e)
end

instance : DecidableEq Ty := Ty.decEq

/-- The bit width of an integer or byte type. -/
def Ty.width : Ty → Nat
  | .int w | .byte w => w
  | .float f => f.width
  | _ => 0

def Ty.isInt : Ty → Bool
  | .int _ => true
  | _ => false

def Ty.isFloat : Ty → Bool
  | .float _ => true
  | _ => false

/-- The scalar value types, the only types SSA values can have outside HFIR. -/
def Ty.isValue : Ty → Bool
  | .int _ | .ptr | .byte _ | .float _ => true
  | _ => false

/-- The types HFIR values can have: everything but function types (decision: Aggregate values).
The verifier checks the parts. -/
def Ty.isHValue : Ty → Bool
  | .func .. => false
  | _ => true

/-- `-> T` or `-> (T, U)`, or nothing, as function headers and types write results. -/
def retsText (rs : List String) : String :=
  match rs with
  | [] => ""
  | [t] => s!" -> {t}"
  | ts => s!" -> ({", ".intercalate ts})"

mutual
  def Ty.render : Ty → String
    | .int w => s!"i{w}"
    | .ptr => "ptr"
    | .byte w => s!"b{w}"
    | .struct p fs => s!"struct<{p.name}>\{{", ".intercalate (Ty.renderList fs)}}"
    | .array n t => s!"array<{n} x {t.render}>"
    | .func ps rs => s!"func<({", ".intercalate (Ty.renderList ps)}){retsText (Ty.renderList rs)}>"
    | .union vs => s!"union<{", ".intercalate (Ty.renderList vs)}>"
    | .slice => "slice"
    | .float f => f.name
  def Ty.renderList : List Ty → List String
    | [] => []
    | t :: ts => t.render :: Ty.renderList ts
end

instance : ToString Ty := ⟨Ty.render⟩

/-- The default integer alignments, `(width in bits, alignment in bytes)`: x86-64 System V. -/
def defaultInts : List (Nat × Nat) := [(8, 1), (16, 2), (32, 4), (64, 8), (128, 16)]

/-- The largest power of two that is at most `n`, and at least 1. -/
def floorPow2 (n : Nat) : Nat := go n 1
where
  go : Nat → Nat → Nat
    | 0, p => p
    | k + 1, p => if p * 2 ≤ n then go k (p * 2) else p

/-- A memory space's data layout. The pointer size is how much memory a pointer takes, and the
address (index) size is what `ptr.addr`, offsets, and allocation sizes use, both in bits. Pointers
align to `ptrAlign` bytes; `iN` and `bN` to the alignment `ints` lists for the smallest width at
least `N`, or else for the largest (decision: Data layout). -/
structure SpaceCfg where
  ptrBits : Nat := 64
  addrBits : Nat := 64
  ptrAlign : Nat := 8
  /-- `(width in bits, alignment in bytes)`, by increasing width. -/
  ints : List (Nat × Nat) := defaultInts
  deriving DecidableEq, Repr, Inhabited

/-- A pointer's alignment when the `memspace` line doesn't give one. -/
def SpaceCfg.naturalAlign (ptrBits : Nat) : Nat := floorPow2 (ptrBits / 8)

/-- The alignment of `iN` and `bN`. -/
def SpaceCfg.intAlign (sp : SpaceCfg) (w : Nat) : Nat :=
  match sp.ints.find? (·.1 ≥ w) with
  | some (_, a) => a
  | none => (sp.ints.getLast?.map (·.2)).getD 1

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

/-- `float.add`, `float.sub`, `float.mul`, `float.div`, and `float.copysign` (the first operand's
magnitude with the second's sign). -/
inductive FBinOp where
  | add | sub | mul | div | copysign
  deriving DecidableEq, Repr

/-- `float.neg`, `float.abs`, `float.sqrt` -/
inductive FUnOp where
  | neg | abs | sqrt
  deriving DecidableEq, Repr

/-- Float comparisons: the ordered ones (`o…`) are false when either operand is NaN, the unordered
ones (`u…`) true; `ord` says neither is NaN, `uno` that one is. -/
inductive FPred where
  | oeq | one | olt | ole | ogt | oge | ord | ueq | une | ult | ule | ugt | uge | uno
  deriving DecidableEq, Repr

/-- What `float.to_int` does with a NaN or an integer part out of the result's range (decision:
Edge-case vocabulary): immediate UB, the nearest bound (NaN gives 0, as AArch64's `fcvtz` and
Rust's `as` do), or a trap with reason `convert`. -/
inductive CvtEdge where
  | ub | sat | trap
  deriving DecidableEq, Repr

/-- What `mem.alloc` does when allocation fails. -/
inductive AllocFail where
  /-- Return null, like C `malloc`. -/
  | null
  /-- Trap, like Rust and Java. -/
  | trap
  deriving DecidableEq, Repr

/-! ## Modifier vocabularies

How each modifier is spelled in op names (decision: Modifier spelling). The first spelling of a
value is the one printed. -/

instance : Spelled ArithOp := ⟨[sp "add" .add, sp "sub" .sub, sp "mul" .mul]⟩

instance : Spelled Ovf := ⟨[sp "wrap" .wrap, sp "nsw" .nsw, sp "nuw" .nuw, sp "nsw.nuw" .nswNuw,
  sp "s.trap" (.trap true), sp "u.trap" (.trap false), sp "s.sat" (.sat true),
  sp "u.sat" (.sat false), sp "s.ub" (.ub true), sp "u.ub" (.ub false)]⟩

instance : Spelled BitOp := ⟨[sp "and" .and, sp "or" .or, sp "xor" .xor]⟩

instance : Spelled ShiftOp := ⟨[sp "shl" .shl, sp "shr.u" .shrU, sp "shr.s" .shrS]⟩

instance : Spelled ShiftEdge := ⟨[sp "ub" .ub, sp "trap" .trap, sp "mask" .mask, sp "total" .total]⟩

instance : Spelled Pred := ⟨[sp "eq" .eq, sp "ne" .ne, sp "slt" .slt, sp "sle" .sle,
  sp "sgt" .sgt, sp "sge" .sge, sp "ult" .ult, sp "ule" .ule, sp "ugt" .ugt, sp "uge" .uge]⟩

instance : Spelled TruncMode := ⟨[sp "wrap" .wrap, sp "nsw" .nsw, sp "nuw" .nuw]⟩

instance : Spelled AllocFail := ⟨[sp "null" .null, sp "trap" .trap]⟩

instance : Spelled FBinOp := ⟨[sp "add" .add, sp "sub" .sub, sp "mul" .mul, sp "div" .div,
  sp "copysign" .copysign]⟩

instance : Spelled FUnOp := ⟨[sp "neg" .neg, sp "abs" .abs, sp "sqrt" .sqrt]⟩

instance : Spelled FPred := ⟨[sp "oeq" .oeq, sp "one" .one, sp "olt" .olt, sp "ole" .ole,
  sp "ogt" .ogt, sp "oge" .oge, sp "ord" .ord, sp "ueq" .ueq, sp "une" .une, sp "ult" .ult,
  sp "ule" .ule, sp "ugt" .ugt, sp "uge" .uge, sp "uno" .uno]⟩

instance : Spelled CvtEdge := ⟨[sp "ub" .ub, sp "sat" .sat, sp "trap" .trap]⟩

/-- `int.add.overflow.s` and `int.add.overflow.u` -/
def signs : List (Spelling Bool) := [sp "s" true, sp "u" false]

/-- What `union.get` and the slice accesses do on a bad tag or index: `.ub` or `.trap`
(decision: Edge-case vocabulary). -/
def edgeModes : List (Spelling Bool) := [sp "ub" false, sp "trap" true]

instance : Spelled TrapReason := ⟨[sp "div0" TrapReason.div0, sp "overflow" TrapReason.overflow,
  sp "shift" TrapReason.shift, sp "oom" TrapReason.oom, sp "bounds" TrapReason.bounds,
  sp "tag" TrapReason.tag, sp "convert" TrapReason.convert]⟩

/-- `ptr.offset.inbounds` and `ptr.offset.wrap` -/
def offsetModes : List (Spelling Bool) := [sp "inbounds" true, sp "wrap" false]

def Edge.all : List Edge := [.ub, .trap, .total, .wrap]

def Edge.name : Edge → String
  | .ub => "ub"
  | .trap => "trap"
  | .total => "total"
  | .wrap => "wrap"

/-- Signed division and remainder edges `(zero, overflow)`: one modifier when it covers both
cases, otherwise two. A zero edge of `wrap` or an overflow edge of `total` doesn't parse. -/
def signedEdges : List (Spelling (Edge × Edge)) :=
  [sp "ub" (.ub, .ub), sp "trap" (.trap, .trap), sp "total" (.total, .wrap)] ++
  Edge.all.flatMap fun z => Edge.all.map fun o =>
    sp s!"{z.name}.{o.name}" (z, o) (parses := z != .wrap && o != .total)

/-- Unsigned division and remainder name the zero edge only; the overflow edge follows from it. -/
def unsignedEdges : List (Spelling (Edge × Edge)) :=
  [sp "ub" (.ub, .ub), sp "trap" (.trap, .trap), sp "total" (.total, .wrap)] ++
  Edge.all.flatMap fun z => Edge.all.map fun o => sp z.name (z, o) (parses := false)

/-- A branch target: a block of the nearest enclosing `cf.blocks`, by label, and how many of the
branch's operands are its arguments. A branch's operands are its own (the condition, the switched
value), then each target's arguments, in the order the targets are written. -/
structure Succ where
  label : String
  nargs : Nat
  deriving DecidableEq, Repr, Inhabited

/-- `cf.switch`'s cases, in order: a key and its target. -/
abbrev Cases := List (Int × Succ)

/-- An op's immediate: a value written in its text that isn't an operand (`align 4`,
`c.malloc`, `@f`, a branch target `^b`). -/
inductive Imm where
  | int (n : Int)
  | nat (n : Nat)
  | str (s : String)
  | ty (t : Ty)
  | flag (b : Bool)
  | succ (s : Succ)
  | cases (cs : Cases)
  | reg (r : Reg)
  deriving DecidableEq, Repr

/-! ## Ops

Every op, declared once (see `Fir.OpDSL`). This generates `OpKind` and `OpKind.isTerminator`, and
the tables the parser, printer, and verifier read. -/

fir_ops
  /-- `int.const n` -/
  op const (n : Int)
    name "int.const"
    format "{n}"
    rule
      operands []
      results t "int.const has one result"
      ints t
      fits n t
  /-- `poison`: a `poison` value of a scalar type (`iN`, `ptr`, `bN` (whose bytes are all
  `poison`), or a float). -/
  op poison
    name "poison"
    dialect value
    format ""
    rule
      operands []
      results t "poison has one result"
      scalar t
  /-- `freeze %x`: `%x`, or an arbitrary value if it is `poison`; an integer or a float. -/
  op freeze
    name "freeze"
    dialect value
    format "%"
    rule
      operands t "freeze takes one operand"
      numeric t
      results [t]
  /-- `copy %x`: the same value, of any type. Rewrites produce it (store-to-load forwarding
  turns a load into a copy of the stored value), and copy propagation removes it. -/
  op copy
    name "copy"
    dialect value
    format "%"
    rule
      operands t "copy takes one operand"
      results [t]
  /-- `select %c, %a, %b` -/
  op select
    name "select"
    dialect value
    format "%, %, %"
    rule
      operands c a b "select takes three operands"
      same "select" [c, b] [i1, a]
      numeric a
      results [a]
  /-- `int.add.nsw %a, %b` and friends: `int.add`, `int.sub`, `int.mul` with an overflow
  modifier. -/
  op arith (op : ArithOp) (ovf : Ovf)
    name "int.{op}.{ovf}"
    format "%, %"
    effects trap
    rule
      operands a b "this op takes two operands"
      same "operands" [b] [a]
      ints a
      results [a]
  /-- `int.and`, `int.or`, `int.xor` -/
  op bit (op : BitOp)
    name "int.{op}"
    format "%, %"
    rule
      operands a b "this op takes two operands"
      same "operands" [b] [a]
      ints a
      results [a]
  /-- `int.div.s.ub %a, %b` and friends; see `Edge`. -/
  op div (op : DivOp) (zero ovf : Edge)
    name "int.div.s.{zero ovf : signedEdges}" with op := .divS
    name "int.div.u.{zero ovf : unsignedEdges}" with op := .divU
    name "int.rem.s.{zero ovf : signedEdges}" with op := .remS
    name "int.rem.u.{zero ovf : unsignedEdges}" with op := .remU
    format "%, %"
    effects trap
    rule
      operands a b "this op takes two operands"
      same "operands" [b] [a]
      ints a
      results [a]
  /-- `int.shl.mask %a, %b`, `int.shr.u`, `int.shr.s`; see `ShiftEdge`. -/
  op shift (op : ShiftOp) (edge : ShiftEdge)
    name "int.{op}.{edge}"
    format "%, %"
    effects trap
    rule
      operands a b "this op takes two operands"
      same "operands" [b] [a]
      ints a
      results [a]
  /-- `int.cmp.slt %a, %b` and friends. -/
  op cmp (p : Pred)
    name "int.cmp.{p}"
    format "%, %"
    rule
      operands a b "int.cmp takes two operands"
      same "operands" [b] [a]
      ints a
      results [i1]
  /-- `int.zext %a`: the result type is the wider type. -/
  op zext
    name "int.zext"
    format "%"
    rule
      operands a "this op takes one operand"
      results t "this op has one result"
      ints a t
      widens a t
  /-- `int.sext %a` -/
  op sext
    name "int.sext"
    format "%"
    rule
      operands a "this op takes one operand"
      results t "this op has one result"
      ints a t
      widens a t
  /-- `int.trunc.nsw %a`; see `TruncMode`. -/
  op trunc (mode : TruncMode)
    name "int.trunc.{mode}"
    format "%"
    rule
      operands a "int.trunc takes one operand"
      results t "int.trunc has one result"
      ints a t
      narrows a t
  /-- `mem.stack 16, align 4`: stack memory, freed when its region ends. -/
  op memStack (size : Nat) (align : Align)
    name "mem.stack"
    format "{size}, align {align}"
    effects alloc
    rule
      pow2 align
      operands []
      results [ptr]
  /-- `mem.alloc.null c.malloc %n, align 16`: heap memory from an allocator family. -/
  op memAlloc (fail : AllocFail) (family : Symbol) (align : Align)
    name "mem.alloc.{fail}"
    format "{family} %, align {align}"
    effects alloc trap
    rule
      pow2 align
      operands "mem.alloc size" [addr]
      results [ptr]
  /-- `mem.free c.malloc %p` -/
  op memFree (family : Symbol)
    name "mem.free"
    format "{family} %"
    effects free
    rule
      operands [ptr]
      noResults
  /-- `mem.load %p, align 4`: the result type is the accessed type. -/
  op load (align : Align)
    name "mem.load"
    format "%, align {align}"
    effects read
    rule
      pow2 align
      operands [ptr]
      results t "mem.load has one result"
      loadable t "loaded"
  /-- `mem.store i32 %v, %p, align 4` -/
  op store (ty : Ty) (align : Align)
    name "mem.store"
    format "{ty} %, %, align {align}"
    effects write
    rule
      pow2 align
      operands [ty, ptr]
      loadable ty "stored"
      noResults
  /-- `ptr.offset.inbounds %p, %n` (poison if it leaves the allocation) or `ptr.offset.wrap`. -/
  op ptrOffset (inbounds : Bool)
    name "ptr.offset.{inbounds : offsetModes}"
    format "%, %"
    rule
      operands [ptr, addr]
      results [ptr]
  /-- `ptr.addr %p`: the address, without exposing the allocation. -/
  op ptrAddr
    name "ptr.addr"
    format "%"
    rule
      operands [ptr]
      results [addr]
  /-- `ptr.expose %p`: the address, and `ptr.from_exposed` may reach the allocation from now on. -/
  op ptrExpose
    name "ptr.expose"
    format "%"
    effects write
    rule
      operands [ptr]
      results [addr]
  /-- `ptr.from_exposed %a`: a pointer to an exposed allocation at that address. -/
  op ptrFromExposed
    name "ptr.from_exposed"
    format "%"
    effects read
    rule
      operands [addr]
      results [ptr]
  /-- `ptr.with_addr %p, %a`: a new address in `%p`'s allocation. -/
  op ptrWithAddr
    name "ptr.with_addr"
    format "%, %"
    rule
      operands [ptr, addr]
      results [ptr]
  /-- `ptr.null` -/
  op ptrNull
    name "ptr.null"
    format ""
    rule
      operands []
      results [ptr]
  /-- `ptr.cmp.eq` and friends; ordered comparisons are unsigned. -/
  op ptrCmp (p : Pred)
    name "ptr.cmp.{p}"
    format "%, %"
    rule
      deny ["ptr.cmp.slt", "ptr.cmp.sle", "ptr.cmp.sgt", "ptr.cmp.sge"]
        "pointer comparisons are unsigned"
      operands [ptr, ptr]
      results [i1]
  /-- `func.call @f(%a, %b)` -/
  op call (callee : Func)
    name "func.call"
    format "{callee}(%*)"
    effects read write alloc free trap diverge unwind
    rule
      call callee
  /-- `cf.if %c { … } else { … }`: two regions. -/
  op if_
    name "cf.if"
    format "% region else region"
  /-- `cf.loop [progress] [iter(…)] { … }`: one region whose parameters are the loop state. -/
  op loop (progress : Flag)
    name "cf.loop"
    format "{progress} %iter region"
    effects diverge
  /-- `cf.yield`: ends a `cf.if` region with the `cf.if`'s results. -/
  op yield
    name "cf.yield"
    format "%*"
    terminator
  /-- `cf.break`: leaves the nearest loop with the loop's results. -/
  op brk
    name "cf.break"
    format "%*"
    terminator
    rust Break
  /-- `cf.continue`: starts the next iteration with new loop state. -/
  op cont
    name "cf.continue"
    format "%*"
    terminator
    rust Continue
  /-- `func.ret` -/
  op ret
    name "func.ret"
    format "%*"
    terminator
    layers hfir mfir lfir
  /-- `cf.blocks [progress] { ^entry: … ^b(%x: i32): … }`: labeled blocks, entered at the first
  (which has no parameters), with jumps between them. Each block ends with a terminator:
  `cf.yield` leaves with the op's results; `cf.br`, `cf.cond_br`, and `cf.switch` jump. With
  `progress`, control may be assumed to leave the op (as for `cf.loop progress`). -/
  op blocks (progress : Flag)
    name "cf.blocks"
    format "{progress} blocks"
    effects diverge
  /-- `cf.br ^b(%x, …)`: jump to a block of the nearest enclosing `cf.blocks`. -/
  op br (dest : Succ)
    name "cf.br"
    format "{dest}"
    terminator
  /-- `cf.cond_br %c, ^t(…), ^f(…)`: jump to `^t` if `%c` is 1, otherwise to `^f`. Branching on
  `poison` is UB. -/
  op condBr (t f : Succ)
    name "cf.cond_br"
    format "%, {t}, {f}"
    terminator
  /-- `cf.switch %v, default ^d(…), [k: ^b(…), …]`: jump to the case whose key is `%v` (keys are
  taken modulo `2^N`), or to the default. Branching on `poison` is UB. -/
  op switch (dflt : Succ) (cases : Cases)
    name "cf.switch"
    format "%, default {dflt}, {cases}"
    terminator
  /-- `ty.size T`: how many bytes a `T` takes, in the memory space's data layout. -/
  op tySize (ty : Ty)
    name "ty.size"
    format "{ty}"
    rule
      sized ty
      operands []
      results [addr]
  /-- `ty.align T`: a `T`'s alignment in bytes. -/
  op tyAlign (ty : Ty)
    name "ty.align"
    format "{ty}"
    rule
      sized ty
      operands []
      results [addr]
  /-- `ty.offset T, i`: the offset of field `i` in the struct `T`. -/
  op tyOffset (ty : Ty) (index : Index)
    name "ty.offset"
    format "{ty}, {index}"
    rule
      field ty index
      operands []
      results [addr]
  /-- `ptr.field.inbounds T %p, i`: field `i` of the struct `T` at `%p`, as `ptr.offset` by the
  field's offset (`.inbounds` or `.wrap`). -/
  op ptrField (inbounds : Bool) (ty : Ty) (index : Index)
    name "ptr.field.{inbounds : offsetModes}"
    format "{ty} %, {index}"
    layers hfir
    rule
      field ty index
      operands [ptr]
      results [ptr]
  /-- `ptr.index.inbounds T %p, %i`: element `%i` (signed) of an array of `T` at `%p`. The
  in-bounds form also gives `poison` when `%i` times `T`'s stride overflows a signed address;
  the `.wrap` form wraps it. -/
  op ptrIndex (inbounds : Bool) (ty : Ty)
    name "ptr.index.{inbounds : offsetModes}"
    format "{ty} %, %"
    layers hfir
    rule
      sized ty
      operands [ptr, addr]
      results [ptr]
  /-- `mem.stack.of T, align 1`: stack memory for a `T`, aligned to `align` or `T`'s alignment,
  whichever is larger; freed when its region ends. -/
  op memStackOf (ty : Ty) (align : Align)
    name "mem.stack.of"
    format "{ty}, align {align}"
    effects alloc
    rule
      pow2 align
      sized ty
      operands []
      results [ptr]
  /-- `mem.copy T %dst, %src, align 4`: copy a `T`'s bytes exactly, as loading and storing them
  as one byte value would: padding and pointers included, overlap allowed. -/
  op memCopy (ty : Ty) (align : Align)
    name "mem.copy"
    format "{ty} %, %, align {align}"
    effects read write
    rule
      pow2 align
      sized ty
      operands [ptr, ptr]
      noResults
  /-- `mem.global @g`: a pointer to the global `@g`. -/
  op memGlobal (global : Global)
    name "mem.global"
    format "{global}"
    rule
      global global
      operands []
      results [ptr]
  /-- `func.addr @f`: a pointer to the function `@f`, which only calls may use. -/
  op funcAddr (callee : Func)
    name "func.addr"
    format "{callee}"
    rule
      func callee
      operands []
      results [ptr]
  /-- `func.call.indirect func<(i32) -> i32> %p(%a)`: a call through a pointer, which must point
  at a function of this signature. -/
  op callIndirect (sig : Ty)
    name "func.call.indirect"
    format "{sig} %(%*)"
    effects read write alloc free trap diverge unwind
    rule
      sig sig
  -- Floats (decisions: Floats, Float ops). Semantics: `Fir.Float`, through `Fir.Sem`.
  /-- `float.const 1.5`: the result type's float with these bits, written as the shortest
  decimal that reads back to them, `inf`, `-inf`, `nan`, or `nan(0x…)` (see `Fir.FloatText`). -/
  op floatConst (value : FloatBits)
    name "float.const"
    format "{value}"
    rule
      operands []
      results t "float.const has one result"
      floats t
      floatBits value t
  /-- `float.add %a, %b`, `float.sub`, `float.mul`, `float.div`: the exact result, rounded to
  nearest (ties to even); `float.copysign %a, %b`: `%a`'s magnitude with `%b`'s sign. -/
  op floatBin (op : FBinOp)
    name "float.{op}"
    format "%, %"
    rule
      operands a b "this op takes two operands"
      same "operands" [b] [a]
      floats a
      results [a]
  /-- `float.neg %a`, `float.abs %a` (the sign bit flipped or cleared), `float.sqrt %a`
  (rounded). -/
  op floatUn (op : FUnOp)
    name "float.{op}"
    format "%"
    rule
      operands a "this op takes one operand"
      floats a
      results [a]
  /-- `float.fma %a, %b, %c`: `%a * %b + %c`, rounded once. -/
  op floatFma
    name "float.fma"
    format "%, %, %"
    rule
      operands a b c "float.fma takes three operands"
      same "operands" [b, c] [a, a]
      floats a
      results [a]
  /-- `float.cmp.olt %a, %b` and friends; see `FPred`. -/
  op floatCmp (p : FPred)
    name "float.cmp.{p}"
    format "%, %"
    rule
      operands a b "float.cmp takes two operands"
      same "operands" [b] [a]
      floats a
      results [i1]
  /-- `float.ext %a`: a float in a wider format, exactly. -/
  op floatExt
    name "float.ext"
    format "%"
    rule
      operands a "this op takes one operand"
      results t "this op has one result"
      floats a t
      widens a t
  /-- `float.trunc %a`: a float in a narrower format, rounded. -/
  op floatTrunc
    name "float.trunc"
    format "%"
    rule
      operands a "float.trunc takes one operand"
      results t "float.trunc has one result"
      floats a t
      narrows a t
  /-- `float.to_int.s.sat %a`: the integer part (toward zero), signed or unsigned, of the result
  type; a NaN or an integer part out of range is UB (`.ub`), the nearest bound (`.sat`, NaN
  gives 0), or a trap with reason `convert` (`.trap`). A `poison` input is UB for `.ub` and
  `.trap`. -/
  op floatToInt (signed : Bool) (edge : CvtEdge)
    name "float.to_int.{signed : signs}.{edge}"
    format "%"
    effects trap
    rule
      operands a "float.to_int takes one operand"
      results t "float.to_int has one result"
      floats a
      ints t
  /-- `int.to_float.s %a`: the integer, signed or unsigned, as the result type's float, rounded. -/
  op intToFloat (signed : Bool)
    name "int.to_float.{signed : signs}"
    format "%"
    rule
      operands a "int.to_float takes one operand"
      results t "int.to_float has one result"
      ints a
      floats t
  /-- `float.from_bits %a`: the float with an integer's bits (the same width). -/
  op floatFromBits
    name "float.from_bits"
    format "%"
    rule
      operands a "this op takes one operand"
      results t "this op has one result"
      ints a
      floats t
      sameWidth a t
  /-- `float.to_bits %a`: a float's bits, as an integer of the same width. -/
  op floatToBits
    name "float.to_bits"
    format "%"
    rule
      operands a "this op takes one operand"
      results t "this op has one result"
      floats a
      ints t
      sameWidth a t
  -- HFIR building blocks, lowered by `Fir.Lower`.
  /-- `agg.make %a, %b`: a struct value from its fields, or an array value from its elements;
  the result type says which. -/
  op aggMake
    name "agg.make"
    format "%*"
    layers hfir
    rule
      results t "agg.make has one result"
      parts t
  /-- `agg.extract %s, 1`: field `1` of a struct value, or element `1` of an array value. -/
  op aggExtract (index : Index)
    name "agg.extract"
    format "%, {index}"
    layers hfir
    rule
      operands a "agg.extract takes one operand"
      results t "agg.extract has one result"
      part a index t
  /-- `agg.insert %s, %v, 1`: `%s` with field or element `1` replaced by `%v`. -/
  op aggInsert (index : Index)
    name "agg.insert"
    format "%, %, {index}"
    layers hfir
    rule
      operands a v "agg.insert takes two operands"
      part a index v
      results [a]
  /-- `int.add.overflow.s %a, %b`: the wrapped result and whether the operation overflowed
  (signed, or unsigned with `.u`), as `int.add.s.trap` would trap; `int.sub` and `int.mul` too.
  `poison` in, `poison` out (both results). -/
  op overflow (op : ArithOp) (signed : Bool)
    name "int.{op}.overflow.{signed : signs}"
    format "%, %"
    layers hfir
    rule
      operands a b "this op takes two operands"
      same "operands" [b] [a]
      ints a
      results [a, i1]
  /-- `union.make %v, 1`: the union (the result type) holding variant `1`, `%v`. -/
  op unionMake (index : Index)
    name "union.make"
    format "%, {index}"
    layers hfir
    rule
      operands v "union.make takes one operand"
      results t "union.make has one result"
      variant t index v
  /-- `union.tag %u`: which variant `%u` holds, as an `i32`. -/
  op unionTag
    name "union.tag"
    format "%"
    layers hfir
    rule
      operands u "union.tag takes one operand"
      union u
      results [i32]
  /-- `union.get.trap %u, 1`: the payload of variant `1`; if `%u` holds another variant, UB
  (`.ub`) or a trap with reason `tag` (`.trap`). -/
  op unionGet (trap : Bool) (index : Index)
    name "union.get.{trap : edgeModes}"
    format "%, {index}"
    layers hfir
    effects trap
    rule
      operands u "union.get takes one operand"
      results t "union.get has one result"
      variant u index t
  /-- `slice.make %p, %n`: the slice of `%n` elements at `%p`. -/
  op sliceMake
    name "slice.make"
    format "%, %"
    layers hfir
    rule
      operands [ptr, addr]
      results [slice]
  /-- `slice.ptr %s` -/
  op slicePtr
    name "slice.ptr"
    format "%"
    layers hfir
    rule
      operands [slice]
      results [ptr]
  /-- `slice.len %s` -/
  op sliceLen
    name "slice.len"
    format "%"
    layers hfir
    rule
      operands [slice]
      results [addr]
  /-- `slice.get.trap %s, %i, align 4`: load element `%i` (unsigned) of the slice, of the result
  type. An index not below the length is UB (`.ub`) or traps with reason `bounds` (`.trap`); a
  `poison` index or length is UB. The element is at `ptr.offset.inbounds` by `%i` times the
  stride, wrapped. -/
  op sliceGet (trap : Bool) (align : Align)
    name "slice.get.{trap : edgeModes}"
    format "%, %, align {align}"
    layers hfir
    effects read trap
    rule
      pow2 align
      operands [slice, addr]
      results t "slice.get has one result"
      loadable t "loaded"
  /-- `slice.set.trap i32 %v, %s, %i, align 4`: store element `%i` of the slice, checked like
  `slice.get`. -/
  op sliceSet (trap : Bool) (ty : Ty) (align : Align)
    name "slice.set.{trap : edgeModes}"
    format "{ty} %, %, %, align {align}"
    layers hfir
    effects write trap
    rule
      pow2 align
      operands [ty, slice, addr]
      loadable ty "stored"
      noResults
  /-- `cf.check.bounds %ok`: nothing if `%ok` is 1; a trap with that reason if it is 0; UB if it
  is `poison`. The lowered form of HFIR's checks. -/
  op check (reason : TrapReason)
    name "cf.check.{reason}"
    format "%"
    effects trap
    rule
      operands [i1]
      noResults
  -- Exceptions (decision: Exceptions). An exception is a pointer: what it points to is the
  -- language's business. HFIR catches with `cf.try`; MFIR names each call's handler.
  /-- `cf.try { … } catch(%e: ptr) { … }`: run the first region; an exception thrown in it (by
  `exn.throw` there, or in a function it calls) that nothing inside catches unwinds to here, and
  the second region runs with the exception bound to its parameter. Either region's `cf.yield`
  gives the op's results. Jumps can't leave either region. -/
  op try_
    name "cf.try"
    format "region catch region"
    layers hfir
    effects unwind
    rust Try
  /-- `exn.throw %e`: throw the exception `%e`. Unwinding pops frames (ending their stack memory,
  and a call's `noalias` scopes) up to the nearest `cf.try` region or `func.invoke` handler, in
  this function or a calling one; an exception that leaves the function the run started in is
  the run's outcome, `threw`. -/
  op throw_
    name "exn.throw"
    format "%"
    terminator
    effects unwind
    rust Throw
    rule
      operands [ptr]
      noResults
  /-- `func.invoke @f(%a) unwind ^h`: `func.call`, except that an exception the callee throws
  jumps to block `^h` of the nearest `cf.blocks`, whose one parameter takes it, instead of going
  on to the caller (a plain `func.call` passes it on). -/
  op invoke (callee : Func) (unwind : Succ)
    name "func.invoke"
    format "{callee}(%*) unwind {unwind}"
    layers mfir
    effects read write alloc free trap diverge unwind
    rule
      call callee
  /-- `func.invoke.indirect func<(i32) -> i32> %p(%a) unwind ^h`: `func.call.indirect` with a
  handler, as `func.invoke`. -/
  op invokeIndirect (sig : Ty) (unwind : Succ)
    name "func.invoke.indirect"
    format "{sig} %(%*) unwind {unwind}"
    layers mfir
    effects read write alloc free trap diverge unwind
    rule
      sig sig
  -- AArch64 (LFIR): the `aarch64` dialect, in machine form. Instructions name their registers
  -- as immediates, a function's code is `aarch64.code`, and blocks end in explicit branches
  -- (decision: LFIR for AArch64). Semantics: `Fir.AArch64` (the instructions) and
  -- `Fir.AArch64Machine` (the machine that runs them).
  /-- `aarch64.code { ^entry: … ^b1: … }`: a function's machine code, as labeled blocks entered
  at the first. Each block ends with a branch, `aarch64.ret`, or `aarch64.trap`. It is the whole
  body of an LFIR function, which finds its arguments where the calling convention puts them. -/
  op a64Code
    name "aarch64.code"
    format "blocks"
    terminator
    layers lfir
  /-- `aarch64.add.x x0, x1, x2` and friends: three-register data processing; see `AluOp`. -/
  op a64Alu (op : AluOp) (sf : Sf) (d n m : Reg)
    name "aarch64.{op}.{sf}"
    format "{d}, {n}, {m}"
    layers lfir
    rule
      deny ["aarch64.smulh.w", "aarch64.umulh.w"] "smulh and umulh are 64-bit only"
      operands []
      noResults
  /-- `aarch64.add.imm.x x0, x1, 16`: data processing with an immediate; see `AluImmOp`. -/
  op a64AluImm (op : AluImmOp) (sf : Sf) (d n : Reg) (imm : Int)
    name "aarch64.{op}.imm.{sf}"
    format "{d}, {n}, {imm}"
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.lsl.imm.x x0, x1, 3`: a shift by an immediate below the size. -/
  op a64ShiftImm (op : ShiftImmOp) (sf : Sf) (d n : Reg) (amount : Index)
    name "aarch64.{op}.imm.{sf}"
    format "{d}, {n}, {amount}"
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.sbfx.x x0, x1, 8`: the low `width` bits (1 to the size), sign-extended (`sbfx`) or
  zero-extended (`ubfx`). -/
  op a64Ext (signed : Bool) (sf : Sf) (d n : Reg) (width : Index)
    name "aarch64.{signed : extModes}.{sf}"
    format "{d}, {n}, {width}"
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.mov.x x0, x1`: copy a register (`sp` included). -/
  op a64Mov (sf : Sf) (d n : Reg)
    name "aarch64.mov.{sf}"
    format "{d}, {n}"
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.movz.x x0, 4660, 16`: a 16-bit immediate shifted left by `hw` (0, 16, 32, or 48):
  zero elsewhere (`movz`), inverted (`movn`), or inserted into the register (`movk`). -/
  op a64MovWide (op : MovOp) (sf : Sf) (d : Reg) (imm hw : Index)
    name "aarch64.{op}.{sf}"
    format "{d}, {imm}, {hw}"
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.csel.eq.x x0, x1, x2`: `x1` if the condition holds, else `x2` (incremented,
  inverted, or negated for `csinc`, `csinv`, `csneg`). -/
  op a64Csel (op : CselOp) (c : Cond) (sf : Sf) (d n m : Reg)
    name "aarch64.{op}.{c}.{sf}"
    format "{d}, {n}, {m}"
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.ldr.w x0, x1, 8`: load 1, 2, 4, or 8 bytes from `x1 + 8`, zero-extended. -/
  op a64Ldr (size : MemSize) (d base : Reg) (off : Int)
    name "aarch64.ldr.{size}"
    format "{d}, {base}, {off}"
    effects read
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.str.w x0, x1, 8`: store the low 1, 2, 4, or 8 bytes of `x0` at `x1 + 8`. -/
  op a64Str (size : MemSize) (s base : Reg) (off : Int)
    name "aarch64.str.{size}"
    format "{s}, {base}, {off}"
    effects write
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.adrl x0, @g`: the address of a global (`adrp` and `add`). -/
  op a64Adrl (d : Reg) (global : Global)
    name "aarch64.adrl"
    format "{d}, {global}"
    layers lfir
    rule
      global global
      operands []
      noResults
  /-- `aarch64.adrl.func x0, @f`: the address of a function (`adrp` and `add`, or a GOT load for
  an external one). -/
  op a64AdrlFunc (d : Reg) (callee : Func)
    name "aarch64.adrl.func"
    format "{d}, {callee}"
    layers lfir
    rule
      func callee
      operands []
      noResults
  /-- `aarch64.b ^b`: jump to a block of the enclosing `aarch64.code`. -/
  op a64B (dest : Succ)
    name "aarch64.b"
    format "{dest}"
    terminator
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.b.eq ^t, ^f`: jump to `^t` if the condition holds, otherwise to `^f`. -/
  op a64BCond (c : Cond) (t f : Succ)
    name "aarch64.b.{c}"
    format "{t}, {f}"
    terminator
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.ret`: return to the caller, with the results where the calling convention puts
  them. -/
  op a64Ret
    name "aarch64.ret"
    format ""
    terminator
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.trap.div0`: trap with a reason (a call to `__fir_trap` with the reason and the
  op's location). -/
  op a64Trap (reason : TrapReason)
    name "aarch64.trap.{reason}"
    format ""
    terminator
    effects trap
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.bl @f`: call a function; the arguments and results are where the calling
  convention puts them for `@f`'s signature, and the call clobbers the caller-saved
  registers. -/
  op a64Bl (callee : Func)
    name "aarch64.bl"
    format "{callee}"
    effects read write alloc free trap diverge
    layers lfir
    rule
      func callee
      operands []
      noResults
  /-- `aarch64.blr func<(i32) -> i32> x9`: call the function `x9` points to, which has that
  signature. -/
  op a64Blr (sig : Ty) (n : Reg)
    name "aarch64.blr"
    format "{sig} {n}"
    effects read write alloc free trap diverge
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.bl.alloc c.malloc, align 16`: allocate `x0` bytes from the family's allocator;
  `x0` is the memory, or null if allocation failed (a call to `malloc` or `aligned_alloc`). -/
  op a64BlAlloc (family : Symbol) (align : Align)
    name "aarch64.bl.alloc"
    format "{family}, align {align}"
    effects alloc
    layers lfir
    rule
      pow2 align
      operands []
      noResults
  /-- `aarch64.exn.set x0`: make `x0` the pending exception (decision: Exceptions at run time):
  store it in the thread's exception slot, `__fir_exn`. A function that throws sets it, then
  returns. -/
  op a64ExnSet (n : Reg)
    name "aarch64.exn.set"
    format "{n}"
    effects write unwind
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.exn.take x0`: `x0` gets the pending exception, which is no longer pending. -/
  op a64ExnTake (d : Reg)
    name "aarch64.exn.take"
    format "{d}"
    effects read write
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.b.exn ^t, ^f`: jump to `^t` if an exception is pending, otherwise to `^f`. -/
  op a64BExn (t f : Succ)
    name "aarch64.b.exn"
    format "{t}, {f}"
    terminator
    effects read
    layers lfir
    rule
      operands []
      noResults
  /-- `aarch64.bl.free c.malloc`: free `x0` (a call to `free`). -/
  op a64BlFree (family : Symbol)
    name "aarch64.bl.free"
    format "{family}"
    effects free
    layers lfir
    rule
      operands []
      noResults

/-- The op's name with its modifiers, as printed. -/
def OpKind.name (k : OpKind) : String :=
  let e := k.erase
  match opNames.find? (·.value == e) with
  | some s => s.text
  | none => "?"

/-! ## Layers

A module's layer (decision: Layers): `layer hfir`, `layer mfir`, or `layer lfir aarch64`, where
LFIR names its target. Each op's declaration lists the layers that allow it; HFIR and MFIR allow
today's core ops, except that `ptr.field` and `ptr.index` are HFIR only (MFIR addresses with
`ptr.offset` by computed offsets; decision: Layout). LFIR allows its target's dialect and, of the
core ops, only `func.ret`, which ends a function. -/

/-- The LFIR target dialects. A target's ops are declared with `fir_ops`, in its dialect and with
`layers lfir`. -/
def targets : List String := ["aarch64"]

/-- A module's layer. -/
inductive Layer where
  | hfir
  | mfir
  /-- LFIR for a target, one of `targets`. -/
  | lfir (target : String)
  deriving DecidableEq, Repr, Inhabited

def Layer.kind : Layer → LayerKind
  | .hfir => .hfir
  | .mfir => .mfir
  | .lfir _ => .lfir

/-- The types values can have in a layer: HFIR's include aggregates, unions, and slices
(decision: Aggregate values); MFIR's and LFIR's are the scalars. -/
def Layer.valueTy : Layer → Ty → Bool
  | .hfir, t => t.isHValue
  | _, t => t.isValue

def Layer.render : Layer → String
  | .lfir t => s!"lfir {t}"
  | l => l.kind.name

/-- Whether a module of layer `l` may contain the op: the op lists the layer, and in LFIR, an op
of a target's dialect belongs to the module's target. -/
def Layer.allows (l : Layer) (d : OpDecl) : Bool :=
  d.layers.contains l.kind &&
    match l with
    | .lfir t => d.dialect == t || !targets.contains d.dialect
    | _ => true

/-- The layers that allow the op, for messages: `hfir, mfir`, or `lfir aarch64` for a target's
op. -/
def OpDecl.layersText (d : OpDecl) : String :=
  ", ".intercalate <| d.layers.map fun
    | .lfir => if targets.contains d.dialect then s!"lfir {d.dialect}" else "lfir"
    | k => k.name

/-! The target rule, on a made-up AArch64 op and a real one: allowed only in LFIR for AArch64,
while LFIR for any target keeps `func.ret` and nothing else of the core. -/

private def aarch64Op : OpDecl :=
  { ctor := "nop", rust := "Nop", doc := "", fields := [], format := "", terminator := false,
    rule := none, effects := [], tier := .verified, layers := [.lfir], dialect := "aarch64" }

#guard (Layer.lfir "aarch64").allows aarch64Op
#guard !(Layer.lfir "x86").allows aarch64Op
#guard !Layer.mfir.allows aarch64Op && !Layer.hfir.allows aarch64Op
#guard aarch64Op.layersText == "lfir aarch64"
#guard (Layer.lfir "aarch64").allows OpKind.ret.decl
#guard !(Layer.lfir "aarch64").allows (OpKind.const 0).decl
#guard (Layer.lfir "aarch64").allows OpKind.a64Ret.decl && !Layer.mfir.allows OpKind.a64Ret.decl
#guard OpKind.a64Ret.decl.dialect == "aarch64"

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
  /-- A region's parameters are written like results, and can carry facts. A block of
  `cf.blocks` is a region with a label (`^name`); other regions have none. -/
  inductive Region where
    | mk (params : List Result) (ops : List Op) (label : Option String)
end

instance : Inhabited Op := ⟨.mk .poison [] [] [] none⟩
instance : Inhabited Region := ⟨.mk [] [] none⟩

def Op.kind : Op → OpKind | .mk k .. => k
def Op.results : Op → List Result | .mk _ rs .. => rs
def Op.args : Op → List Operand | .mk _ _ as .. => as
def Op.regions : Op → List Region | .mk _ _ _ rs _ => rs
def Op.loc : Op → Option Loc | .mk _ _ _ _ l => l
def Region.params : Region → List Result | .mk ps _ _ => ps
def Region.ops : Region → List Op | .mk _ ops _ => ops
def Region.label : Region → Option String | .mk _ _ l => l

/-- A function. Its parameters are the parameters of its body region. -/
structure Func where
  name : String
  rets : List Ty
  file : Option String
  body : Region
  deriving Inhabited

def Func.params (f : Func) : List Result := f.body.params

/-- A global's initial contents. -/
inductive Init where
  /-- `zero`: every byte zero. -/
  | zero
  /-- An integer, for an `iN` or `bN`. -/
  | int (n : Int)
  /-- `null` -/
  | null
  /-- `@g`: the address of a global or a function. -/
  | sym (name : String)
  /-- `bytes "0aff"`: the whole object's bytes. -/
  | bytes (bs : List Nat)
  /-- `{a, b}`: one initializer per struct field or array element; padding is zero. -/
  | list (items : List Init)
  deriving Repr, Inhabited

/-- `global [const] @name: T [align N] = INIT`: memory allocated before the program starts and
never freed. Its alignment is the larger of `align` and `T`'s. -/
structure Global where
  name : String
  ty : Ty
  const : Bool := false
  align : Nat := 1
  init : Init
  deriving Inhabited

/-- Memory an external function's effects can name: the allocations its pointer arguments point
into (`args`), every exposed allocation (`exposed`), or the module's globals (`globals`). -/
inductive MemClass where
  | args | exposed | globals
  deriving DecidableEq, Repr

def MemClass.name : MemClass → String
  | .args => "args"
  | .exposed => "exposed"
  | .globals => "globals"

/-- What an external function may do (decision: Call effects). Anything not listed, it doesn't. -/
inductive ExtEffect where
  | read (m : MemClass)
  | write (m : MemClass)
  | alloc
  | free
  | trap
  | diverge
  | unwind
  deriving DecidableEq, Repr

def ExtEffect.render : ExtEffect → String
  | .read m => s!"read({m.name})"
  | .write m => s!"write({m.name})"
  | .alloc => "alloc"
  | .free => "free"
  | .trap => "trap"
  | .diverge => "diverge"
  | .unwind => "unwind"

instance : Inhabited Trust := ⟨.assume⟩

/-- `extern func @puts(ptr) -> i32 effects[read(args)] assume`: a function outside the module.
Its effects are a trust-tagged fact about it. -/
structure Extern where
  name : String
  params : List Ty
  rets : List Ty
  effects : List ExtEffect
  trust : Trust
  deriving Inhabited

/-- The function type of an external function. -/
def Extern.ty (x : Extern) : Ty := .func x.params x.rets

structure Module where
  /-- `layer …`; HFIR when the module doesn't say. -/
  layer : Layer := .hfir
  /-- The default memory space. -/
  space : SpaceCfg := {}
  globals : List Global := []
  externs : List Extern := []
  funcs : List Func

def Module.find? (m : Module) (name : String) : Option Func :=
  m.funcs.find? (·.name == name)

end Fir
