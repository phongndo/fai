import Fir.OpDSL

/-!
# Syntax

The shape of a FIR-0 program. Following the structure decision, everything is an op: an op has a
kind, typed results, operands, nested regions, and a source location. A region has typed
parameters (block arguments) and a list of ops.

FIR-1 covers integers, structured control flow, memory, and calls between FIR functions, with
structs and arrays in memory, globals, and calls through function pointers. Floats, external
calls, and threads come later.
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

/-- A type. Values have the *value types*: signless integers `iN`, pointers, and byte types
`bN` (raw memory, copied exactly). Structs and arrays describe memory, and function types
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
    | .int _, .ptr | .int _, .byte _ | .int _, .struct .. | .int _, .array .. | .int _, .func ..
    | .ptr, .int _ | .ptr, .byte _ | .ptr, .struct .. | .ptr, .array .. | .ptr, .func ..
    | .byte _, .int _ | .byte _, .ptr | .byte _, .struct .. | .byte _, .array .. | .byte _, .func ..
    | .struct .., .int _ | .struct .., .ptr | .struct .., .byte _ | .struct .., .array ..
    | .struct .., .func .. | .array .., .int _ | .array .., .ptr | .array .., .byte _
    | .array .., .struct .. | .array .., .func .. | .func .., .int _ | .func .., .ptr
    | .func .., .byte _ | .func .., .struct .. | .func .., .array .. =>
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
  | _ => 0

def Ty.isInt : Ty → Bool
  | .int _ => true
  | _ => false

/-- The types SSA values can have. -/
def Ty.isValue : Ty → Bool
  | .int _ | .ptr | .byte _ => true
  | _ => false

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
    effects read write alloc free trap diverge
    rule
      sig sig

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

structure Module where
  /-- The default memory space. -/
  space : SpaceCfg := {}
  globals : List Global := []
  funcs : List Func

def Module.find? (m : Module) (name : String) : Option Func :=
  m.funcs.find? (·.name == name)

end Fir
