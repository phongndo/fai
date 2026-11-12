import Std.Data.HashMap
import Std.Data.ExtTreeMap
import Fir.Basic
import Fir.Syntax
import Fir.Sem
import Fir.Mem

/-!
# Reference interpreter

A small-step machine: `step` runs one op. The machine is a *core* (the environment, memory,
scopes, and the oracle) plus an explicit stack of frames, so every intermediate state can be
inspected. `Fir.Behavior` uses that to define divergence and the `progress` rule precisely.

The split is for proofs. Ops on values and memory are computations on the core alone (`CM`), so
they can't depend on the stack. Only the control-flow layer (`step`, `execOp`, `terminate`)
touches the stack, and it is written as plain functions on machines. Two machines that run
different code over the same core then provably compute the same core.

Every free choice (what `freeze` of `poison` gives, allocation ids, tags, addresses, whether an
allocation fails, comparisons of one-past-the-end pointers) comes from an *oracle*. The semantics
quantifies over every oracle; the command-line tool uses one that always answers `0`, which
means: `freeze` gives `0`, allocations succeed, ids count up from 1, and addresses are assigned
first-fit from `0x1000`.
-/

namespace Fir

abbrev Env := Std.HashMap String RVal

/-- A stack frame. The top of the stack is always a `block`. -/
inductive Frame where
  /-- The ops left to run in the current region, and the stack allocations it made. -/
  | block (ops : List Op) (allocs : List Nat)
  /-- A `cf.if` waiting for its region to `cf.yield`. -/
  | ifJoin (results : List Result) (loc : Option Loc)
  /-- A running `cf.loop`. Its body runs in the frames above it. -/
  | loop (progress : Bool) (body : Region) (results : List Result) (loc : Option Loc)
  /-- A function call: the caller's environment, where the results go, the return types, and
  the `noalias` scopes the call opened. -/
  | call (saved : Env) (results : List Result) (rets : List Ty) (scopes : List Nat)
      (loc : Option Loc)

/-- An active `noalias` or `readonly` scope: one function parameter during one call. -/
structure Scope where
  alloc : Nat
  tag : Nat
  noalias : Bool
  readonly : Bool

/-- What a `noalias` scope records per byte: accessed through a pointer derived from the
parameter, accessed through another pointer, written. All three is UB. -/
abbrev Mark := Bool × Bool × Bool

abbrev Marks := Std.ExtTreeMap Nat Mark

/-- Everything but the frame stack. -/
structure Core where
  env : Env
  funcs : Std.HashMap String Func
  space : SpaceCfg
  oracle : Nat → Int
  /-- How many oracle choices have been used. -/
  choices : Nat := 0
  allocs : Std.ExtTreeMap Nat Alloc := ∅
  /-- Each allocation's bytes. -/
  mem : Std.ExtTreeMap Nat Bytes := ∅
  /-- Every tag, with its parent. Each allocation's first tag is a root. -/
  tags : Std.ExtTreeMap Nat (Option Nat) := ∅
  scopes : Std.ExtTreeMap Nat Scope := ∅
  /-- Each `noalias` scope's marks, by byte offset. -/
  marks : Std.ExtTreeMap Nat Marks := ∅
  nextScope : Nat := 0

structure Machine where
  core : Core
  stack : List Frame

/-- How a run ends: its behavior, the location of the op that ended it, a note for people, and
(for a return from the outermost call) the heap allocations still live. -/
structure Halt where
  behavior : Behavior
  loc : Option Loc
  note : String := ""
  leaks : List String := []

/-- A computation on the core. -/
abbrev CM := StateT Core (Except Halt)

def halt {μ : Type → Type} [MonadExcept Halt μ] (b : Behavior) (loc : Option Loc)
    (note : String := "") : μ α :=
  throw { behavior := b, loc, note }

def ub {μ : Type → Type} [MonadExcept Halt μ] (k : UBKind) (loc : Option Loc)
    (note : String := "") : μ α :=
  halt (.ub k) loc note

def renderLoc : Option Loc → String
  | some l => s!"@{l.line}:{l.col}"
  | none => "@?"

/-! ## Choices -/

/-- The oracle's next answer. -/
def choose : CM Int := do
  let c ← get
  set { c with choices := c.choices + 1 }
  pure (c.oracle c.choices)

/-- A fresh id: the oracle's answer if it is positive and unused, otherwise the next one up. -/
def freshId (used : Nat → Bool) (keys : List Nat) : CM Nat := do
  let c ← choose
  if c > 0 && !used c.toNat then pure c.toNat
  else pure (keys.foldl max 0 + 1)

def freshTag (parent : Option Nat) : CM Nat := do
  let c ← get
  let t ← freshId c.tags.contains c.tags.keys
  modify fun c => { c with tags := c.tags.insert t parent }
  pure t

/-! ## Environment -/

/-- An operand's value. Reads only the environment. -/
def operandIn (env : Env) (loc : Option Loc) : Operand → Except Halt RVal
  | .var n => match env[n]? with
    | some v => pure v
    | none => halt (.stuck s!"%{n} is not defined") loc
  | .hole n _ => halt (.hole n) loc

def evalOperand (loc : Option Loc) (o : Operand) : CM RVal :=
  fun c => (operandIn c.env loc o).map (·, c)

def RVal.hasTy : RVal → Ty → Bool
  | .int w _, .int w' => w == w'
  | .ptr _, .ptr => true
  | .bytes bs, .byte w => bs.length * 8 == w
  | _, _ => false

def bindAll (loc : Option Loc) : List Result → List RVal → CM Unit
  | [], [] => pure ()
  | r :: rs, v :: vs => do
    unless v.hasTy r.ty do halt (.stuck s!"%{r.name} has type {r.ty} but got another type") loc
    modify fun c => { c with env := c.env.insert r.name v }
    bindAll loc rs vs
  | _, _ => halt (.stuck "wrong number of values") loc

def allocIn (c : Core) (loc : Option Loc) (a : Nat) : Except Halt Alloc :=
  match c.allocs[a]? with
  | some al => pure al
  | none => halt (.stuck s!"no allocation #{a}") loc

def getAlloc (loc : Option Loc) (a : Nat) : CM Alloc := do allocIn (← get) loc a

def setAlloc (a : Nat) (al : Alloc) : CM Unit :=
  modify fun c => { c with allocs := c.allocs.insert a al }

/-! ## Addresses -/

def alignUp (x a : Nat) : Nat := if a ≤ 1 then x else (x + a - 1) / a * a

/-- Give an allocation its address, if it doesn't have one yet: the oracle's answer if it fits,
otherwise the lowest free address from `0x1000`. -/
def realize (loc : Option Loc) (a : Nat) : CM Nat := do
  let al ← getAlloc loc a
  if let some b := al.base then return b
  let c ← get
  let limit := 2 ^ c.space.addrBits
  let span := max al.size 1
  let taken := c.allocs.foldl (init := []) fun acc _ x =>
    match x.live, x.base with
    | true, some b => (b, b + max x.size 1) :: acc
    | _, _ => acc
  let fits (b : Nat) : Bool :=
    b > 0 && b % al.align == 0 && b + span ≤ limit &&
      taken.all fun (lo, hi) => b + span ≤ lo || hi ≤ b
  let o ← choose
  let candidates := (alignUp 0x1000 al.align :: taken.map fun (_, hi) => alignUp hi al.align)
  let base ←
    if o > 0 && fits o.toNat then pure o.toNat
    else match (candidates.filter fits).min? with
      | some b => pure b
      | none => ub .addressSpace loc s!"no room for {al.size} bytes"
  setAlloc a { al with base := some base }
  pure base

def addrMod (c : Core) (x : Int) : Nat := (x % (2 ^ c.space.addrBits : Int)).toNat

/-- A pointer's address. Gives its allocation an address if needed; doesn't expose it. -/
def ptrAddr (loc : Option Loc) : Ptr → CM Nat
  | .rel a _ off => do
    let b ← realize loc a
    pure (addrMod (← get) (b + off))
  | .abs addr _ => pure addr

/-- A pointer's address, exposing its allocation and tag to `ptr.from_exposed`. -/
def ptrExpose (loc : Option Loc) (p : Ptr) : CM Nat := do
  let addr ← ptrAddr loc p
  if let .rel a t _ := p then
    let al ← getAlloc loc a
    unless al.exposed.contains t do setAlloc a { al with exposed := t :: al.exposed }
  pure addr

/-- A pointer from an address: it may belong to any live exposed allocation whose range
(including one past the end) contains the address. -/
def fromExposed (n : Nat) : CM Ptr := do
  let c ← get
  let cands := c.allocs.foldl (init := []) fun acc a al =>
    match al.live, al.base with
    | true, some b =>
      if b ≤ n && n ≤ b + al.size then acc ++ al.exposed.map (a, ·) else acc
    | _, _ => acc
  pure (.abs n cands)

/-! ## Accesses -/

/-- Whether tag `t` is `anc` or derived from it. -/
def isDerived (tags : Std.ExtTreeMap Nat (Option Nat)) (anc t : Nat) : Bool :=
  go tags.size t
where
  go : Nat → Nat → Bool
    | 0, _ => false
    | fuel + 1, t => t == anc || match tags[t]? with
      | some (some p) => go fuel p
      | _ => false

/-- The allocation, tag, and offset a pointer accesses. A bare address may fit several exposed
`(allocation, tag)` pairs. The intended rule picks the one that avoids UB. Until that is
implemented, the run halts as `ambiguous` whenever the choice could matter: the pairs name
different allocations, or an active `noalias` or `readonly` scope tells their tags apart. (Tags
matter only to scopes, and a fresh scope's tag is never an ancestor of an older tag.) Reporting
`ambiguous` instead of picking one keeps the reference tool from reporting UB that the intended
rule wouldn't, which would hide miscompiles in differential testing. -/
def resolveIn (c : Core) (loc : Option Loc) (p : Ptr) (size : Nat) :
    Except Halt (Nat × Nat × Int) := do
  match p with
  | .rel a t off => pure (a, t, off)
  | .abs addr cands =>
    let fitsIn (x : Nat × Nat) : Bool :=
      match c.allocs[x.1]? with
      | some al => match al.base with
        | some b => al.live && b ≤ addr && addr + size ≤ b + al.size
        | none => false
      | none => false
    match cands.filter fitsIn with
    | [] =>
      if cands.isEmpty then ub .noProvenance loc s!"address {addr} belongs to no exposed allocation"
      else ub .outOfBounds loc s!"address {addr} is outside every allocation it may belong to"
    | (a, t) :: rest =>
      if let some (a', _) := rest.find? (·.1 != a) then
        halt .ambiguous loc s!"address {addr} may belong to #{a} or #{a'}"
      let tellApart (t' : Nat) : Bool := c.scopes.toList.any fun (_, s) =>
        s.alloc == a && isDerived c.tags s.tag t != isDerived c.tags s.tag t'
      if let some (_, t') := rest.find? (tellApart ·.2) then
        halt .ambiguous loc s!"address {addr} may carry tag {t} or {t'} of #{a}, and an active noalias or readonly scope tells them apart"
      let b := ((c.allocs[a]?.bind (·.base)).getD 0 : Int)
      pure (a, t, addr - b)

def resolve (loc : Option Loc) (p : Ptr) (size : Nat) : CM (Nat × Nat × Int) := do
  resolveIn (← get) loc p size

def deadNote (al : Alloc) : String :=
  match al.kind with
  | .stack => s!"stack memory from {renderLoc al.site}, whose region has ended"
  | .heap _ => s!"allocated at {renderLoc al.site}, freed at {renderLoc al.freedAt}"

/-- Where an access goes (allocation, tag, offset), after checking lifetime, bounds, and
alignment. Changes nothing. -/
def checkAccess (c : Core) (loc : Option Loc) (p : Ptr) (size align : Nat) :
    Except Halt (Nat × Nat × Nat) := do
  let (a, t, off) ← resolveIn c loc p size
  let al ← allocIn c loc a
  unless al.live do ub .useAfterFree loc (deadNote al)
  unless 0 ≤ off && off + size ≤ al.size do
    ub .outOfBounds loc s!"offset {off}, {size} bytes, allocation size {al.size}"
  unless al.alignedAt off align do
    ub .misaligned loc <| match al.base with
      | some b => s!"address {b + off} is not a multiple of {align}"
      | none => s!"offset {off} in an allocation aligned to {al.align} with no address yet, access needs {align}"
  pure (a, t, off.toNat)

def markByte (derived write : Bool) (mk : Mark) : Mark :=
  (mk.1 || derived, mk.2.1 || !derived, mk.2.2 || write)

def Mark.bad (mk : Mark) : Bool := mk.1 && mk.2.1 && mk.2.2

/-- Mark `n` bytes from `off`. -/
def markScope (derived write : Bool) (ms : Marks) (off : Nat) : Nat → Marks
  | 0 => ms
  | n + 1 =>
    markScope derived write (ms.insert off (markByte derived write (ms.getD off (false, false, false))))
      (off + 1) n

/-- The first of `n` bytes from `off` whose mark would become bad. -/
def firstBad (derived write : Bool) (ms : Marks) (off n : Nat) : Option Nat :=
  (List.range n).find? fun i => (markByte derived write (ms.getD (off + i) (false, false, false))).bad

/-- Record an access to allocation `a` through tag `t` in each active scope. -/
def markAll (tags : Std.ExtTreeMap Nat (Option Nat)) (loc : Option Loc) (a t off size : Nat)
    (write : Bool) : List (Nat × Scope) → Std.ExtTreeMap Nat Marks →
    Except Halt (Std.ExtTreeMap Nat Marks)
  | [], mm => pure mm
  | (id, s) :: rest, mm =>
    if s.alloc != a then markAll tags loc a t off size write rest mm
    else
      let derived := isDerived tags s.tag t
      if s.readonly && write && derived then
        ub .readonly loc "write through a pointer derived from a readonly parameter"
      else if !s.noalias then markAll tags loc a t off size write rest mm
      else
        let ms := mm.getD id ∅
        match firstBad derived write ms off size with
        | some i => ub .noalias loc s!"byte {off + i} of #{a} is accessed both through a noalias parameter and another pointer, and written"
        | none => markAll tags loc a t off size write rest (mm.insert id (markScope derived write ms off size))

/-- Check an access, record it in the active scopes, and return the allocation and offset it
reads or writes. -/
def access (loc : Option Loc) (p : Ptr) (size align : Nat) (write : Bool) : CM (Nat × Nat) :=
  fun c => do
    let (a, t, off) ← checkAccess c loc p size align
    let marks ← markAll c.tags loc a t off size write c.scopes.toList c.marks
    pure ((a, off), { c with marks })

/-- Turn pointer fragments into address bytes, exposing their pointers. -/
def fragToBits (loc : Option Loc) : Byte → CM Byte
  | .frag p i => do
    let addr ← ptrExpose loc p
    let c ← get
    let digit := if i < c.space.addrBits / 8 then addr / 256 ^ i % 256 else 0
    pure (.bits (BitVec.ofNat 8 digit))
  | b => pure b

def decodeAs (loc : Option Loc) (ty : Ty) (bs : List Byte) : CM RVal := do
  let c ← get
  match ty with
  | .byte _ => pure (.bytes bs)
  | .int w =>
    let bs ← bs.mapM (fragToBits loc)
    pure (.int w ((decodeInt? w bs).getD .poison))
  | .ptr =>
    if bs.contains .poison then return .ptr none
    match ptrOfFrags? bs.length bs with
    | some p => pure (.ptr (some p))
    | none =>
      let bs ← bs.mapM (fragToBits loc)
      match decodeInt? c.space.ptrBits bs with
      | some (.bits b) => pure (.ptr (some (← fromExposed (b.toNat % 2 ^ c.space.addrBits))))
      | _ => pure (.ptr none)

def loadC (loc : Option Loc) (ty : Ty) (align : Nat) : Option Ptr → CM RVal
  | none => ub .poison loc "load through a poison pointer"
  | some p => do
    let size := ty.size (← get).space
    let (a, off) ← access loc p size align false
    decodeAs loc ty (readBytes ((← get).mem.getD a ∅) off size)

/-- Store `v`, which must have type `ty`, through `p`. -/
def storeC (loc : Option Loc) (ty : Ty) (align : Nat) (v : RVal) : Option Ptr → CM Unit
  | none => ub .poison loc "store through a poison pointer"
  | some p => fun c => do
    unless v.hasTy ty do halt (.stuck s!"the stored value isn't a {ty}") loc
    let bs := v.encode c.space
    let ((a, off), c) ← access loc p bs.length align true c
    pure ((), { c with mem := c.mem.insert a (writeBytes (c.mem.getD a ∅) off bs) })

/-! ## Allocation -/

def newAlloc (loc : Option Loc) (size align : Nat) (kind : AllocKind) : CM Ptr := do
  let c ← get
  let a ← freshId c.allocs.contains c.allocs.keys
  setAlloc a { size, align, kind, site := loc }
  let t ← freshTag none
  pure (.rel a t 0)

/-- End the lifetime of stack allocations. -/
def releaseIds (ids : List Nat) : CM Unit := do
  for a in ids do
    if let some al := (← get).allocs[a]? then setAlloc a { al with live := false }

def freePtr (loc : Option Loc) (family : String) : Option Ptr → CM Unit
  | none => ub .poison loc
  | some (.abs 0 _) => pure ()
  | some p => do
    let (a, t, off) ← resolve loc p 0
    let al ← getAlloc loc a
    unless al.live do
      if al.kind == .stack then ub .badFree loc (deadNote al) else ub .doubleFree loc (deadNote al)
    unless al.kind == .heap family do
      ub .badFree loc s!"allocated at {renderLoc al.site} by {match al.kind with | .heap f => f | .stack => "mem.stack"}"
    unless off == 0 do ub .badFree loc s!"offset {off} is not the start of the allocation"
    let c ← get
    let marks ← markAll c.tags loc a t 0 al.size true c.scopes.toList c.marks
    set { c with marks }
    setAlloc a { al with live := false, freedAt := loc }

/-! ## Pointer comparison -/

/-- The allocation and offset a pointer points into, if any. -/
def ptrView (p : Ptr) : CM (Option (Nat × Int)) := do
  match p with
  | .rel a _ off => pure (some (a, off))
  | .abs addr cands =>
    let c ← get
    let inRange (x : Nat × Nat) (strict : Bool) : Option (Nat × Int) := do
      let al ← c.allocs[x.1]?
      let b ← al.base
      if al.live && b ≤ addr && (addr < b + al.size || (!strict && addr == b + al.size)) then
        some (x.1, (addr : Int) - b)
      else none
    pure ((cands.filterMap (inRange · true)).head? <|> (cands.filterMap (inRange · false)).head?)

def cmpInt (p : Pred) (x y : Int) : Bool :=
  match p with
  | .eq => x == y | .ne => x != y
  | .ult | .slt => x < y | .ule | .sle => x ≤ y
  | .ugt | .sgt => x > y | .uge | .sge => x ≥ y

def cmpPtrs (loc : Option Loc) (pred : Pred) (p q : Ptr) : CM Bool := do
  let isEq := pred == .eq || pred == .ne
  match ← ptrView p, ← ptrView q with
  | some (a, o), some (b, o') =>
    if a == b then return cmpInt pred o o'
    unless isEq do ub .ptrCompare loc "ordered comparison of pointers into different allocations"
    let al ← getAlloc loc a
    let bl ← getAlloc loc b
    let inside (o : Int) (x : Alloc) := 0 ≤ o && o < x.size
    let equal ← if inside o al && inside o' bl then pure false else do pure ((← choose) != 0)
    pure (if pred == .eq then equal else !equal)
  | _, _ =>
    unless isEq do ub .ptrCompare loc "ordered comparison of pointers outside allocations"
    let x ← ptrAddr loc p
    let y ← ptrAddr loc q
    pure (cmpInt pred x y)

/-! ## Facts -/

def ptrFactHolds (loc : Option Loc) (f : Fact) (p : Ptr) : CM Bool := do
  match f, p with
  | .nonnull, .abs 0 _ => pure false
  | .align n, .rel a _ off => do pure ((← getAlloc loc a).alignedAt off n)
  | .align n, .abs addr _ => pure (addr % n == 0)
  | _, _ => pure true

def factHolds (loc : Option Loc) (f : Fact) : RVal → CM Bool
  | .int _ v => pure (f.holds v)
  | .ptr (some p) => ptrFactHolds loc f p
  | _ => pure true

/-- Bind results, then check their facts: a violated fact is UB. -/
def bindResults (loc : Option Loc) (rs : List Result) (vs : List RVal) : CM Unit := do
  bindAll loc rs vs
  for (r, v) in rs.zip vs do
    for f in r.facts do
      unless ← factHolds loc f.fact v do ub .fact loc s!"%{r.name} breaks a fact"

/-! ## Ops -/

def asInt (loc : Option Loc) (w : Nat) : RVal → CM (Val w)
  | .int w' v => if h : w' = w then pure (h ▸ v) else
      halt (.stuck s!"expected an i{w} but got an i{w'}") loc
  | _ => halt (.stuck s!"expected an i{w}") loc

def asPtr (loc : Option Loc) : RVal → CM (Option Ptr)
  | .ptr p => pure p
  | _ => halt (.stuck "expected a ptr") loc

def fromOut (loc : Option Loc) : OpOut w → CM (Val w)
  | .ok v => pure v
  | .trap r => halt (.trap r) loc
  | .ub k => ub k loc

def intWidth : RVal → Nat
  | .int w _ => w
  | _ => 0

def addrInt (c : Core) (n : Nat) : RVal := .int c.space.addrBits (.bits (BitVec.ofNat _ n))

/-- Evaluate an op without regions that doesn't touch the stack. -/
def evalSimple (loc : Option Loc) (k : OpKind) (rs : List Result) (vs : List RVal) :
    CM (List RVal) := do
  let c ← get
  let aw := c.space.addrBits
  match k, rs, vs with
  | .const n, [r], [] => pure [.int _ (Sem.const r.ty.width n)]
  | .poison, [r], [] => pure [.int r.ty.width .poison]
  | .freeze, [_], [.int w .poison] => pure [.int w (.bits (BitVec.ofInt w (← choose)))]
  | .freeze, [_], [v] => pure [v]
  | .copy, [_], [v] => pure [v]
  | .select, [r], [c, a, b] =>
    pure [.int _ (Sem.select (← asInt loc 1 c) (← asInt loc r.ty.width a) (← asInt loc r.ty.width b))]
  | .arith op ovf, [r], [a, b] =>
    pure [.int _ (← fromOut loc (Sem.arith op ovf (← asInt loc r.ty.width a) (← asInt loc r.ty.width b)))]
  | .bit op, [r], [a, b] =>
    pure [.int _ (Sem.bit op (← asInt loc r.ty.width a) (← asInt loc r.ty.width b))]
  | .div op zero ovf, [r], [a, b] =>
    pure [.int _ (← fromOut loc (Sem.div op zero ovf (← asInt loc r.ty.width a) (← asInt loc r.ty.width b)))]
  | .shift op edge, [r], [a, b] =>
    pure [.int _ (← fromOut loc (Sem.shift op edge (← asInt loc r.ty.width a) (← asInt loc r.ty.width b)))]
  | .cmp p, [_], [.int w x, b] => pure [.int _ (Sem.cmp p x (← asInt loc w b))]
  | .zext, [r], [.int _ v] => pure [.int _ (Sem.zext r.ty.width v)]
  | .sext, [r], [.int _ v] => pure [.int _ (Sem.sext r.ty.width v)]
  | .trunc mode, [r], [.int _ v] => pure [.int _ (Sem.trunc mode r.ty.width v)]
  -- Memory
  | .memAlloc fail family align, [_], [n] => do
    let .bits size ← asInt loc aw n | ub .poison loc "allocation size is poison"
    if (← choose) != 0 then
      match fail with
      | .null => return [.ptr (some .null)]
      | .trap => halt (.trap .oom) loc
    pure [.ptr (some (← newAlloc loc size.toNat align (.heap family)))]
  | .memFree family, [], [p] => do freePtr loc family (← asPtr loc p); pure []
  | .load align, [r], [p] => do pure [← loadC loc r.ty align (← asPtr loc p)]
  | .store ty align, [], [v, p] => do storeC loc ty align v (← asPtr loc p); pure []
  -- Pointers
  | .ptrNull, [_], [] => pure [.ptr (some .null)]
  | .ptrOffset inbounds, [_], [p, n] => do
    let some p ← asPtr loc p | return [.ptr none]
    let .bits n ← asInt loc aw n | return [.ptr none]
    let n := n.toInt
    if n == 0 then return [.ptr (some p)]
    match p with
    | .rel a t off =>
      let al ← getAlloc loc a
      let ok := al.live && 0 ≤ off && off ≤ al.size && 0 ≤ off + n && off + n ≤ al.size
      pure [.ptr (if inbounds && !ok then none else some (.rel a t (off + n)))]
    | .abs addr cands =>
      let addr' := addrMod c (addr + n)
      if !inbounds then return [.ptr (some (.abs addr' cands))]
      let keep := cands.filter fun (a, _) =>
        match c.allocs[a]? with
        | some al => match al.base with
          | some b => al.live && b ≤ addr && addr ≤ b + al.size && (b : Int) ≤ addr + n &&
              addr + n ≤ (b + al.size : Int)
          | none => false
        | none => false
      pure [.ptr (if keep.isEmpty then none else some (.abs addr' keep))]
  | .ptrAddr, [_], [p] => do
    let some p ← asPtr loc p | return [.int aw .poison]
    pure [addrInt c (← ptrAddr loc p)]
  | .ptrExpose, [_], [p] => do
    let some p ← asPtr loc p | return [.int aw .poison]
    pure [addrInt c (← ptrExpose loc p)]
  | .ptrFromExposed, [_], [n] => do
    let .bits n ← asInt loc aw n | return [.ptr none]
    pure [.ptr (some (← fromExposed n.toNat))]
  | .ptrWithAddr, [_], [p, n] => do
    let some p ← asPtr loc p | return [.ptr none]
    let .bits n ← asInt loc aw n | return [.ptr none]
    match p with
    | .rel a t _ => pure [.ptr (some (.rel a t (n.toNat - (← realize loc a : Int))))]
    | .abs _ cands => pure [.ptr (some (.abs n.toNat cands))]
  | .ptrCmp pred, [_], [p, q] => do
    let (some p, some q) := (← asPtr loc p, ← asPtr loc q) | return [.int 1 .poison]
    pure [.int 1 (.bits (BitVec.ofBool (← cmpPtrs loc pred p q)))]
  | _, _, _ => halt (.stuck "malformed op") loc

/-- Run an op without regions that doesn't touch the stack: evaluate its operands, compute, and
bind its results. -/
def simpleOp (loc : Option Loc) (k : OpKind) (results : List Result) (args : List Operand) :
    CM Unit := do
  let vs ← args.mapM (evalOperand loc)
  bindResults loc results (← evalSimple loc k results vs)

/-- Bind a callee's parameters and open its `noalias` and `readonly` scopes. A pointer
parameter with either fact gets a fresh tag derived from the argument's. -/
def enterCall (loc : Option Loc) (params : List Result) (vs : List RVal) : CM (List Nat) := do
  bindResults loc params vs
  let mut opened := []
  for (r, v) in params.zip vs do
    let noalias := r.facts.any (·.fact == .noalias)
    let readonly := r.facts.any (·.fact == .readonly)
    if !(noalias || readonly) then continue
    let .ptr (some p) := v | continue
    -- A pointer that can't access memory (null, dangling) opens no scope. An ambiguous one halts.
    let some (a, t, off) ← tryCatch (some <$> resolve loc p 0)
        (fun h => if h.behavior matches .ub _ then pure none else throw h) | continue
    let t' ← freshTag (some t)
    let c ← get
    let id := c.nextScope
    set { c with
      env := c.env.insert r.name (.ptr (some (.rel a t' off))),
      scopes := c.scopes.insert id { alloc := a, tag := t', noalias, readonly },
      nextScope := id + 1 }
    opened := id :: opened
  pure opened

/-- Close the scopes a call opened. -/
def closeScopes (ids : List Nat) : CM Unit :=
  modify fun c => { c with
    scopes := ids.foldl (·.erase ·) c.scopes, marks := ids.foldl (·.erase ·) c.marks }

/-- The heap allocations still live, for the leak report. -/
def leaks (c : Core) : List String :=
  (c.allocs.toList.filter fun (_, al) => al.live && al.kind != .stack).map fun (_, al) =>
    s!"leak: {al.size} bytes from {match al.kind with | .heap f => f | .stack => "stack"} at {renderLoc al.site}"

/-! ## Control flow

These functions take and return whole machines. Core computations run through `Machine.exec`. -/

/-- Run a core computation on a machine's core. -/
def Machine.exec (m : Machine) (c : CM α) : Except Halt (α × Machine) :=
  match c.run m.core with
  | .ok (a, core) => .ok (a, { m with core })
  | .error h => .error h

def Frame.isCall : Frame → Bool
  | .call .. => true
  | _ => false

/-- Record a new stack allocation in the top block. -/
def addAllocId (id : Nat) : List Frame → List Frame
  | .block ops ids :: rest => .block ops (id :: ids) :: rest
  | s => s

/-- Split the stack at the first frame `pick` accepts: the frames above it, its answer, and the
frames below it. Stops at a call frame unless `pick` accepts it. -/
def splitStack (pick : Frame → Option α) : List Frame → Option (List Frame × α × List Frame)
  | [] => none
  | f :: rest =>
    match pick f with
    | some x => some ([], x, rest)
    | none =>
      if f.isCall then none
      else (splitStack pick rest).map fun (above, x, below) => (f :: above, x, below)

def pickLoop : Frame → Option (Bool × Region × List Result × Option Loc)
  | .loop p body rs loc => some (p, body, rs, loc)
  | _ => none

def pickCall : Frame → Option (Env × List Result × List Ty × List Nat × Option Loc)
  | .call saved rs rets scopes loc => some (saved, rs, rets, scopes, loc)
  | _ => none

/-- The stack allocations made by these frames' blocks. -/
def blockIds : List Frame → List Nat
  | [] => []
  | .block _ ids :: fs => ids ++ blockIds fs
  | _ :: fs => blockIds fs

/-- Start a loop iteration: bind the loop state and push the body. -/
def enterBody (m : Machine) (loc : Option Loc) (body : Region) (vs : List RVal) :
    Except Halt Machine := do
  let ((), m) ← m.exec (bindResults loc body.params vs)
  pure { m with stack := .block body.ops [] :: m.stack }

/-- Run a terminator. The current block has already been popped. -/
def terminate (m : Machine) (loc : Option Loc) (k : OpKind) (vs : List RVal) :
    Except Halt Machine :=
  match k with
  | .yield =>
    match m.stack with
    | .ifJoin rs loc' :: rest => do
      let ((), m) ← { m with stack := rest }.exec (bindResults loc' rs vs)
      pure m
    | .loop .. :: _ => halt (.stuck "a loop body must end with cf.break or cf.continue") loc
    | _ => halt (.stuck "the function ended without func.ret") loc
  | .brk =>
    match splitStack pickLoop m.stack with
    | some (above, (_, _, rs, loc'), below) => do
      let ((), m) ← { m with stack := below }.exec
        (do releaseIds (blockIds above); bindResults loc' rs vs)
      pure m
    | none => halt (.stuck "cf.break outside a loop") loc
  | .cont =>
    match splitStack pickLoop m.stack with
    | some (above, (p, body, rs, loc'), below) => do
      let ((), m) ← { m with stack := .loop p body rs loc' :: below }.exec
        (releaseIds (blockIds above))
      enterBody m loc body vs
    | none => halt (.stuck "cf.continue outside a loop") loc
  | .ret =>
    match splitStack pickCall m.stack with
    | some (above, (saved, rs, rets, scopes, loc'), below) =>
      if !(vs.length == rets.length && (vs.zip rets).all (fun (v, t) => v.hasTy t)) then
        halt (.stuck "func.ret values don't match the function's return types") loc
      else do
        let ((), m) ← m.exec (do releaseIds (blockIds above); closeScopes scopes)
        if below.isEmpty then
          throw { behavior := .ret vs, loc, leaks := leaks m.core }
        let ((), m) ← { core := { m.core with env := saved }, stack := below : Machine }.exec
          (bindResults loc' rs vs)
        pure m
    | none => halt (.stuck "func.ret outside a function") loc
  | _ => halt (.stuck "not a terminator") loc

def OpKind.callee? : OpKind → Option String
  | .call callee => some callee
  | _ => none

def OpKind.stackAlloc? : OpKind → Option (Nat × Nat)
  | .memStack size align => some (size, align)
  | _ => none

def OpKind.loopProgress? : OpKind → Option Bool
  | .loop p => some p
  | _ => none

def OpKind.isIf : OpKind → Bool
  | .if_ => true
  | _ => false

/-- Run an op without regions. The current block, with the op removed, is on top of the stack. -/
def execFlat (m : Machine) (kind : OpKind) (results : List Result) (args : List Operand)
    (loc : Option Loc) : Except Halt Machine :=
  match kind.callee? with
  | some callee => do
    let (vs, m) ← m.exec (args.mapM (evalOperand loc))
    let some f := m.core.funcs[callee]? | halt (.stuck s!"no function @{callee}") loc
    let saved := m.core.env
    let (scopes, m) ← { m with core := { m.core with env := {} } }.exec (enterCall loc f.params vs)
    pure { m with stack := .block f.body.ops [] :: .call saved results f.rets scopes loc :: m.stack }
  | none =>
  match kind.stackAlloc? with
  | some (size, align) => do
    let (p, m) ← m.exec (do
      let p ← newAlloc loc size align .stack
      bindResults loc results [.ptr (some p)]
      pure p)
    let id := match p with | .rel a .. => a | _ => 0
    pure { m with stack := addAllocId id m.stack }
  | none =>
  if kind.isTerminator then do
    let (vs, m) ← m.exec (args.mapM (evalOperand loc))
    match m.stack with
    | f :: rest => do
      let ((), m) ← { m with stack := rest }.exec (releaseIds (blockIds [f]))
      terminate m loc kind vs
    | [] => terminate m loc kind vs
  else do
    let ((), m) ← m.exec (simpleOp loc kind results args)
    pure m

/-- Run one op. The current block, with the op removed, is on top of the stack. -/
def execOp (m : Machine) : Op → Except Halt Machine
  | .mk kind results args regions loc =>
    match regions with
    | [] => execFlat m kind results args loc
    | [body] =>
      match kind.loopProgress? with
      | some p => do
        let (vs, m) ← m.exec (args.mapM (evalOperand loc))
        enterBody { m with stack := .loop p body results loc :: m.stack } loc body vs
      | none => halt (.stuck "malformed op") loc
    | [thn, els] =>
      if kind.isIf then do
        let (c, m) ← m.exec (do asInt loc 1 ((← args.mapM (evalOperand loc)).headD (.int 1 .poison)))
        match c with
        | .poison => ub .poison loc "branch on poison"
        | .bits b =>
          pure { m with stack := .block (if b = 1 then thn else els).ops [] :: .ifJoin results loc :: m.stack }
      else halt (.stuck "malformed op") loc
    | _ => halt (.stuck "malformed op") loc

/-- One step of the machine. -/
def step (m : Machine) : Except Halt Machine :=
  match m.stack with
  | .block [] ids :: rest => do
    -- Falling off the end of a region is an implicit `cf.yield` with no values.
    let ((), m) ← { m with stack := rest }.exec (releaseIds ids)
    terminate m none .yield []
  | .block (op :: ops) ids :: rest => execOp { m with stack := .block ops ids :: rest } op
  | _ => halt (.stuck "no block to run") none

/-- The core before a call from outside the module. -/
def Core.initial (oracle : Nat → Int) (mod : Module) : Core :=
  { env := {}, oracle, space := mod.space,
    funcs := mod.funcs.foldl (fun acc g => acc.insert g.name g) {} }

/-- The machine at the start of a call to `f`. -/
def Machine.init (oracle : Nat → Int) (mod : Module) (f : Func) (args : List RVal) :
    Except Halt Machine := do
  let (scopes, core) ← (enterCall none f.params args).run (Core.initial oracle mod)
  pure { core, stack := [.block f.body.ops [], .call {} [] f.rets scopes none] }

/-- Run `n` steps. An `error` is a halted run. -/
def runSteps : Nat → Machine → Except Halt Machine
  | 0, m => .ok m
  | n + 1, m =>
    match step m with
    | .ok m' => runSteps n m'
    | .error h => .error h

/-- The state after `n` steps of a call. -/
def stateAt (oracle : Nat → Int) (mod : Module) (f : Func) (args : List RVal) (n : Nat) :
    Except Halt Machine :=
  (Machine.init oracle mod f args).bind (runSteps n)

def Frame.isProgressLoop : Frame → Bool
  | .loop true .. => true
  | _ => false

/-- Which frames are `progress` loops, from the top of the stack down. -/
def Machine.shape (m : Machine) : List Bool := m.stack.map Frame.isProgressLoop

/-- The frame `d` from the bottom of the stack is a `progress` loop. -/
def Machine.inProgressLoopAt (m : Machine) (d : Nat) : Prop := m.shape.reverse[d]? = some true

/-- Whether any active loop is a `progress` loop. -/
def Machine.inProgressLoop (m : Machine) : Bool := m.shape.any id

end Fir
