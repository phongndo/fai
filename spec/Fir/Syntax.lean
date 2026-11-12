import Fir.OpDSL

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

/-- An op's immediate: a value written in its text that isn't an operand (`align 4`,
`c.malloc`, `@f`). -/
inductive Imm where
  | int (n : Int)
  | nat (n : Nat)
  | str (s : String)
  | ty (t : Ty)
  | flag (b : Bool)
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
  /-- `poison`: an integer `poison` value. -/
  op poison
    name "poison"
    format ""
    rule
      operands []
      results t "poison has one result"
      ints t
  /-- `freeze %x`: `%x`, or an arbitrary value if it is `poison`. -/
  op freeze
    name "freeze"
    format "%"
    rule
      operands t "freeze takes one operand"
      ints t
      results [t]
  /-- `copy %x`: the same value, of any type. Rewrites produce it (store-to-load forwarding
  turns a load into a copy of the stored value), and copy propagation removes it. -/
  op copy
    name "copy"
    format "%"
    rule
      operands t "copy takes one operand"
      results [t]
  /-- `select %c, %a, %b` -/
  op select
    name "select"
    format "%, %, %"
    rule
      operands c a b "select takes three operands"
      same "select" [c, b] [i1, a]
      ints a
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
    effects read write alloc free trap diverge
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

/-- The op's name with its modifiers, as printed. -/
def OpKind.name (k : OpKind) : String :=
  let e := k.erase
  match opNames.find? (·.value == e) with
  | some s => s.text
  | none => "?"

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
