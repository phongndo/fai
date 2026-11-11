import Std.Data.HashMap
import Fir.Basic
import Fir.Syntax
import Fir.Sem
import Fir.Mem

/-!
# Reference interpreter

A small-step machine: `step` runs one op. The machine keeps the environment, the memory, and an
explicit stack of frames, so every intermediate state can be inspected. `Fir.Behavior` uses that
to define divergence and the `progress` rule precisely.

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
  /-- Per byte offset: accessed through a derived pointer, accessed through another, written. -/
  marks : Std.HashMap Nat (Bool × Bool × Bool) := {}

structure Machine where
  env : Env
  stack : List Frame
  funcs : Std.HashMap String Func
  space : SpaceCfg
  oracle : Nat → Int
  /-- How many oracle choices have been used. -/
  choices : Nat := 0
  allocs : Std.HashMap Nat Alloc := {}
  /-- Every tag, with its parent. Each allocation's first tag is a root. -/
  tags : Std.HashMap Nat (Option Nat) := {}
  scopes : Std.HashMap Nat Scope := {}
  nextScope : Nat := 0

/-- How a run ends: its behavior, the location of the op that ended it, a note for people, and
(for a return from the outermost call) the heap allocations still live. -/
structure Halt where
  behavior : Behavior
  loc : Option Loc
  note : String := ""
  leaks : List String := []

abbrev SM := StateT Machine (Except Halt)

def halt (b : Behavior) (loc : Option Loc) (note : String := "") : SM α :=
  throw { behavior := b, loc, note }

def ub (k : UBKind) (loc : Option Loc) (note : String := "") : SM α := halt (.ub k) loc note

def renderLoc : Option Loc → String
  | some l => s!"@{l.line}:{l.col}"
  | none => "@?"

/-! ## Choices -/

/-- The oracle's next answer. -/
def choose : SM Int := do
  let m ← get
  set { m with choices := m.choices + 1 }
  pure (m.oracle m.choices)

/-- A fresh id: the oracle's answer if it is positive and unused, otherwise the next one up. -/
def freshId (used : Nat → Bool) (keys : List Nat) : SM Nat := do
  let c ← choose
  if c > 0 && !used c.toNat then pure c.toNat
  else pure (keys.foldl max 0 + 1)

def freshTag (parent : Option Nat) : SM Nat := do
  let m ← get
  let t ← freshId m.tags.contains m.tags.keys
  modify fun m => { m with tags := m.tags.insert t parent }
  pure t

/-! ## Environment -/

def lookup (loc : Option Loc) (n : String) : SM RVal := do
  match (← get).env[n]? with
  | some v => pure v
  | none => halt (.stuck s!"%{n} is not defined") loc

def evalOperand (loc : Option Loc) : Operand → SM RVal
  | .var n => lookup loc n
  | .hole n _ => halt (.hole n) loc

def RVal.hasTy : RVal → Ty → Bool
  | .int w _, .int w' => w == w'
  | .ptr _, .ptr => true
  | .bytes bs, .byte w => bs.length * 8 == w
  | _, _ => false

def bindAll (loc : Option Loc) : List Result → List RVal → SM Unit
  | [], [] => pure ()
  | r :: rs, v :: vs => do
    unless v.hasTy r.ty do halt (.stuck s!"%{r.name} has type {r.ty} but got another type") loc
    modify fun m => { m with env := m.env.insert r.name v }
    bindAll loc rs vs
  | _, _ => halt (.stuck "wrong number of values") loc

def getAlloc (loc : Option Loc) (a : Nat) : SM Alloc := do
  match (← get).allocs[a]? with
  | some al => pure al
  | none => halt (.stuck s!"no allocation #{a}") loc

def setAlloc (a : Nat) (al : Alloc) : SM Unit :=
  modify fun m => { m with allocs := m.allocs.insert a al }

/-! ## Addresses -/

def alignUp (x a : Nat) : Nat := if a ≤ 1 then x else (x + a - 1) / a * a

/-- Give an allocation its address, if it doesn't have one yet: the oracle's answer if it fits,
otherwise the lowest free address from `0x1000`. -/
def realize (loc : Option Loc) (a : Nat) : SM Nat := do
  let al ← getAlloc loc a
  if let some b := al.base then return b
  let m ← get
  let limit := 2 ^ m.space.addrBits
  let span := max al.size 1
  let taken := m.allocs.fold (init := []) fun acc _ x =>
    match x.live, x.base with
    | true, some b => (b, b + max x.size 1) :: acc
    | _, _ => acc
  let fits (b : Nat) : Bool :=
    b > 0 && b % al.align == 0 && b + span ≤ limit &&
      taken.all fun (lo, hi) => b + span ≤ lo || hi ≤ b
  let c ← choose
  let candidates := (alignUp 0x1000 al.align :: taken.map fun (_, hi) => alignUp hi al.align)
  let base ←
    if c > 0 && fits c.toNat then pure c.toNat
    else match (candidates.filter fits).min? with
      | some b => pure b
      | none => ub .addressSpace loc s!"no room for {al.size} bytes"
  setAlloc a { al with base := some base }
  pure base

def addrMod (m : Machine) (x : Int) : Nat := (x % (2 ^ m.space.addrBits : Int)).toNat

/-- A pointer's address. Gives its allocation an address if needed; doesn't expose it. -/
def ptrAddr (loc : Option Loc) : Ptr → SM Nat
  | .rel a _ off => do
    let b ← realize loc a
    pure (addrMod (← get) (b + off))
  | .abs addr _ => pure addr

/-- A pointer's address, exposing its allocation and tag to `ptr.from_exposed`. -/
def ptrExpose (loc : Option Loc) (p : Ptr) : SM Nat := do
  let addr ← ptrAddr loc p
  if let .rel a t _ := p then
    let al ← getAlloc loc a
    unless al.exposed.contains t do setAlloc a { al with exposed := t :: al.exposed }
  pure addr

/-- A pointer from an address: it may belong to any live exposed allocation whose range
(including one past the end) contains the address. -/
def fromExposed (n : Nat) : SM Ptr := do
  let m ← get
  let cands := m.allocs.fold (init := []) fun acc a al =>
    match al.live, al.base with
    | true, some b =>
      if b ≤ n && n ≤ b + al.size then acc ++ al.exposed.map (a, ·) else acc
    | _, _ => acc
  pure (.abs n cands)

/-! ## Accesses -/

/-- Whether tag `t` is `anc` or derived from it. -/
def isDerived (tags : Std.HashMap Nat (Option Nat)) (anc t : Nat) : Bool :=
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
def resolve (loc : Option Loc) (p : Ptr) (size : Nat) : SM (Nat × Nat × Int) := do
  match p with
  | .rel a t off => pure (a, t, off)
  | .abs addr cands =>
    let m ← get
    let fitsIn (c : Nat × Nat) : Bool :=
      match m.allocs[c.1]? with
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
      let tellApart (t' : Nat) : Bool := m.scopes.toList.any fun (_, s) =>
        s.alloc == a && isDerived m.tags s.tag t != isDerived m.tags s.tag t'
      if let some (_, t') := rest.find? (tellApart ·.2) then
        halt .ambiguous loc s!"address {addr} may carry tag {t} or {t'} of #{a}, and an active noalias or readonly scope tells them apart"
      let b := ((m.allocs[a]?.bind (·.base)).getD 0 : Int)
      pure (a, t, addr - b)

/-- Record an access in the active `noalias` and `readonly` scopes. -/
def checkScopes (loc : Option Loc) (a t : Nat) (off size : Nat) (write : Bool) : SM Unit := do
  let m ← get
  for (id, s) in m.scopes.toList do
    if s.alloc != a then continue
    let derived := isDerived m.tags s.tag t
    if s.readonly && write && derived then
      ub .readonly loc "write through a pointer derived from a readonly parameter"
    if s.noalias then
      let mut marks := s.marks
      for i in List.range size do
        let (d, f, w) := marks.getD (off + i) (false, false, false)
        let mark := (d || derived, f || !derived, w || write)
        if mark.1 && mark.2.1 && mark.2.2 then
          ub .noalias loc s!"byte {off + i} of #{a} is accessed both through a noalias parameter and another pointer, and written"
        marks := marks.insert (off + i) mark
      modify fun m => { m with scopes := m.scopes.insert id { s with marks } }

def deadNote (al : Alloc) : String :=
  match al.kind with
  | .stack => s!"stack memory from {renderLoc al.site}, whose region has ended"
  | .heap _ => s!"allocated at {renderLoc al.site}, freed at {renderLoc al.freedAt}"

/-- Check an access and return the allocation and offset it reads or writes. -/
def access (loc : Option Loc) (p : Ptr) (size align : Nat) (write : Bool) : SM (Nat × Nat) := do
  let (a, t, off) ← resolve loc p size
  let al ← getAlloc loc a
  unless al.live do ub .useAfterFree loc (deadNote al)
  unless 0 ≤ off && off + size ≤ al.size do
    ub .outOfBounds loc s!"offset {off}, {size} bytes, allocation size {al.size}"
  unless al.alignedAt off align do
    ub .misaligned loc <| match al.base with
      | some b => s!"address {b + off} is not a multiple of {align}"
      | none => s!"offset {off} in an allocation aligned to {al.align} with no address yet, access needs {align}"
  checkScopes loc a t off.toNat size write
  pure (a, off.toNat)

/-- Turn pointer fragments into address bytes, exposing their pointers. -/
def fragToBits (loc : Option Loc) : Byte → SM Byte
  | .frag p i => do
    let addr ← ptrExpose loc p
    let m ← get
    let digit := if i < m.space.addrBits / 8 then addr / 256 ^ i % 256 else 0
    pure (.bits (BitVec.ofNat 8 digit))
  | b => pure b

def decodeAs (loc : Option Loc) (ty : Ty) (bs : List Byte) : SM RVal := do
  let m ← get
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
      match decodeInt? m.space.ptrBits bs with
      | some (.bits b) => pure (.ptr (some (← fromExposed (b.toNat % 2 ^ m.space.addrBits))))
      | _ => pure (.ptr none)

/-! ## Allocation -/

def newAlloc (loc : Option Loc) (size align : Nat) (kind : AllocKind) : SM Ptr := do
  let m ← get
  let a ← freshId m.allocs.contains m.allocs.keys
  setAlloc a { size, align, kind, site := loc }
  let t ← freshTag none
  pure (.rel a t 0)

/-- End the lifetime of the stack allocations of blocks being popped. -/
def release (frames : List Frame) : SM Unit := do
  for f in frames do
    if let .block _ ids := f then
      for a in ids do
        if let some al := (← get).allocs[a]? then setAlloc a { al with live := false }

def freePtr (loc : Option Loc) (family : String) : Option Ptr → SM Unit
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
    checkScopes loc a t 0 al.size true
    setAlloc a { al with live := false, freedAt := loc }

/-! ## Pointer comparison -/

/-- The allocation and offset a pointer points into, if any. -/
def ptrView (p : Ptr) : SM (Option (Nat × Int)) := do
  match p with
  | .rel a _ off => pure (some (a, off))
  | .abs addr cands =>
    let m ← get
    let inRange (c : Nat × Nat) (strict : Bool) : Option (Nat × Int) := do
      let al ← m.allocs[c.1]?
      let b ← al.base
      if al.live && b ≤ addr && (addr < b + al.size || (!strict && addr == b + al.size)) then
        some (c.1, (addr : Int) - b)
      else none
    pure ((cands.filterMap (inRange · true)).head? <|> (cands.filterMap (inRange · false)).head?)

def cmpInt (p : Pred) (x y : Int) : Bool :=
  match p with
  | .eq => x == y | .ne => x != y
  | .ult | .slt => x < y | .ule | .sle => x ≤ y
  | .ugt | .sgt => x > y | .uge | .sge => x ≥ y

def cmpPtrs (loc : Option Loc) (pred : Pred) (p q : Ptr) : SM Bool := do
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

def ptrFactHolds (loc : Option Loc) (f : Fact) (p : Ptr) : SM Bool := do
  match f, p with
  | .nonnull, .abs 0 _ => pure false
  | .align n, .rel a _ off => do pure ((← getAlloc loc a).alignedAt off n)
  | .align n, .abs addr _ => pure (addr % n == 0)
  | _, _ => pure true

def factHolds (loc : Option Loc) (f : Fact) : RVal → SM Bool
  | .int _ v => pure (f.holds v)
  | .ptr (some p) => ptrFactHolds loc f p
  | _ => pure true

/-- Bind results, then check their facts: a violated fact is UB. -/
def bindResults (loc : Option Loc) (rs : List Result) (vs : List RVal) : SM Unit := do
  bindAll loc rs vs
  for (r, v) in rs.zip vs do
    for f in r.facts do
      unless ← factHolds loc f.fact v do ub .fact loc s!"%{r.name} breaks a fact"

/-! ## Ops -/

def asInt (loc : Option Loc) (w : Nat) : RVal → SM (Val w)
  | .int w' v => if h : w' = w then pure (h ▸ v) else
      halt (.stuck s!"expected an i{w} but got an i{w'}") loc
  | _ => halt (.stuck s!"expected an i{w}") loc

def asPtr (loc : Option Loc) : RVal → SM (Option Ptr)
  | .ptr p => pure p
  | _ => halt (.stuck "expected a ptr") loc

def fromOut (loc : Option Loc) : OpOut w → SM (Val w)
  | .ok v => pure v
  | .trap r => halt (.trap r) loc
  | .ub k => ub k loc

def intWidth : RVal → Nat
  | .int w _ => w
  | _ => 0

def addrInt (m : Machine) (n : Nat) : RVal := .int m.space.addrBits (.bits (BitVec.ofNat _ n))

/-- Evaluate an op without regions. -/
def evalSimple (loc : Option Loc) (k : OpKind) (rs : List Result) (vs : List RVal) :
    SM (List RVal) := do
  let m ← get
  let aw := m.space.addrBits
  match k, rs, vs with
  | .const n, [r], [] => pure [.int _ (Sem.const r.ty.width n)]
  | .poison, [r], [] => pure [.int r.ty.width .poison]
  | .freeze, [_], [.int w .poison] => pure [.int w (.bits (BitVec.ofInt w (← choose)))]
  | .freeze, [_], [v] => pure [v]
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
  | .memStack size align, [_], [] => do
    let p ← newAlloc loc size align .stack
    let id := match p with | .rel a .. => a | _ => 0
    modify fun m => { m with stack := match m.stack with
      | .block ops ids :: rest => .block ops (id :: ids) :: rest
      | s => s }
    pure [.ptr (some p)]
  | .memAlloc fail family align, [_], [n] => do
    let .bits size ← asInt loc aw n | ub .poison loc "allocation size is poison"
    if (← choose) != 0 then
      match fail with
      | .null => return [.ptr (some .null)]
      | .trap => halt (.trap .oom) loc
    pure [.ptr (some (← newAlloc loc size.toNat align (.heap family)))]
  | .memFree family, [], [p] => do freePtr loc family (← asPtr loc p); pure []
  | .load align, [r], [p] => do
    let some p ← asPtr loc p | ub .poison loc "load through a poison pointer"
    let size := r.ty.size m.space
    let (a, off) ← access loc p size align false
    pure [← decodeAs loc r.ty ((← getAlloc loc a).read off size)]
  | .store _ align, [], [v, p] => do
    let some p ← asPtr loc p | ub .poison loc "store through a poison pointer"
    let bs := v.encode m.space
    let (a, off) ← access loc p bs.length align true
    setAlloc a ((← getAlloc loc a).write off bs)
    pure []
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
      let addr' := addrMod m (addr + n)
      if !inbounds then return [.ptr (some (.abs addr' cands))]
      let keep := cands.filter fun (a, _) =>
        match m.allocs[a]? with
        | some al => match al.base with
          | some b => al.live && b ≤ addr && addr ≤ b + al.size && (b : Int) ≤ addr + n &&
              addr + n ≤ (b + al.size : Int)
          | none => false
        | none => false
      pure [.ptr (if keep.isEmpty then none else some (.abs addr' keep))]
  | .ptrAddr, [_], [p] => do
    let some p ← asPtr loc p | return [.int aw .poison]
    pure [addrInt m (← ptrAddr loc p)]
  | .ptrExpose, [_], [p] => do
    let some p ← asPtr loc p | return [.int aw .poison]
    pure [addrInt m (← ptrExpose loc p)]
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

/-! ## Control flow -/

def push (f : Frame) : SM Unit := modify fun m => { m with stack := f :: m.stack }

/-- Split the stack at the first frame `pick` accepts: the frames above it, its answer, and the
frames below it. Stops at a call frame unless `pick` accepts it. -/
def splitStack (pick : Frame → Option α) : List Frame → Option (List Frame × α × List Frame)
  | [] => none
  | f :: rest =>
    match pick f with
    | some x => some ([], x, rest)
    | none =>
      if f matches .call .. then none
      else (splitStack pick rest).map fun (above, x, below) => (f :: above, x, below)

def pickLoop : Frame → Option (Bool × Region × List Result × Option Loc)
  | .loop p body rs loc => some (p, body, rs, loc)
  | _ => none

def pickCall : Frame → Option (Env × List Result × List Ty × List Nat × Option Loc)
  | .call saved rs rets scopes loc => some (saved, rs, rets, scopes, loc)
  | _ => none

/-- Start a loop iteration: bind the loop state and push the body. -/
def enterBody (loc : Option Loc) (body : Region) (vs : List RVal) : SM Unit := do
  bindResults loc body.params vs
  push (.block body.ops [])

/-- The heap allocations still live, for the leak report. -/
def leaks (m : Machine) : List String :=
  let live := m.allocs.toList.filter fun (_, al) => al.live && al.kind != .stack
  (live.mergeSort (fun a b => a.1 ≤ b.1)).map fun (_, al) =>
    s!"leak: {al.size} bytes from {match al.kind with | .heap f => f | .stack => "stack"} at {renderLoc al.site}"

/-- Run a terminator. The current block has already been popped. -/
def terminate (loc : Option Loc) (k : OpKind) (vs : List RVal) : SM Unit := do
  let m ← get
  match k with
  | .yield =>
    match m.stack with
    | .ifJoin rs loc' :: rest =>
      set { m with stack := rest }
      bindResults loc' rs vs
    | .loop .. :: _ => halt (.stuck "a loop body must end with cf.break or cf.continue") loc
    | _ => halt (.stuck "the function ended without func.ret") loc
  | .brk =>
    match splitStack pickLoop m.stack with
    | some (above, (_, _, rs, loc'), below) =>
      release above
      modify fun m => { m with stack := below }
      bindResults loc' rs vs
    | none => halt (.stuck "cf.break outside a loop") loc
  | .cont =>
    match splitStack pickLoop m.stack with
    | some (above, (p, body, rs, loc'), below) =>
      release above
      modify fun m => { m with stack := .loop p body rs loc' :: below }
      enterBody loc body vs
    | none => halt (.stuck "cf.continue outside a loop") loc
  | .ret =>
    match splitStack pickCall m.stack with
    | some (above, (saved, rs, rets, scopes, loc'), below) =>
      unless vs.length == rets.length && (vs.zip rets).all (fun (v, t) => v.hasTy t) do
        halt (.stuck "func.ret values don't match the function's return types") loc
      release above
      modify fun m => { m with scopes := scopes.foldl (·.erase ·) m.scopes }
      if below.isEmpty then
        throw { behavior := .ret vs, loc, leaks := leaks (← get) }
      modify fun m => { m with env := saved, stack := below }
      bindResults loc' rs vs
    | none => halt (.stuck "func.ret outside a function") loc
  | _ => halt (.stuck "not a terminator") loc

/-- Bind a callee's parameters and open its `noalias` and `readonly` scopes. A pointer
parameter with either fact gets a fresh tag derived from the argument's. -/
def enterCall (loc : Option Loc) (params : List Result) (vs : List RVal) : SM (List Nat) := do
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
    let m ← get
    let id := m.nextScope
    set { m with
      env := m.env.insert r.name (.ptr (some (.rel a t' off))),
      scopes := m.scopes.insert id { alloc := a, tag := t', noalias, readonly },
      nextScope := id + 1 }
    opened := id :: opened
  pure opened

/-- Run one op. The current block (with the op removed) is on top of the stack. -/
def execOp : Op → SM Unit
  | .mk kind results args regions loc => do
    let vs ← args.mapM (evalOperand loc)
    match kind, regions with
    | .if_, [thn, els] => do
      match ← asInt loc 1 (vs.headD (.int 1 .poison)) with
      | .poison => ub .poison loc "branch on poison"
      | .bits b =>
        push (.ifJoin results loc)
        push (.block (if b = 1 then thn else els).ops [])
    | .loop p, [body] => do
      push (.loop p body results loc)
      enterBody loc body vs
    | .call callee, [] => do
      let m ← get
      let some f := m.funcs[callee]? | halt (.stuck s!"no function @{callee}") loc
      set { m with env := {} }
      let scopes ← enterCall loc f.params vs
      push (.call m.env results f.rets scopes loc)
      push (.block f.body.ops [])
    | k, [] =>
      if k.isTerminator then do
        let m ← get
        match m.stack with
        | f :: rest =>
          set { m with stack := rest }
          release [f]
        | [] => pure ()
        terminate loc k vs
      else
        bindResults loc results (← evalSimple loc k results vs)
    | _, _ => halt (.stuck "malformed op") loc

/-- One step of the machine. -/
def step : SM Unit := do
  let m ← get
  match m.stack with
  | .block [] ids :: rest =>
    -- Falling off the end of a region is an implicit `cf.yield` with no values.
    set { m with stack := rest }
    release [.block [] ids]
    terminate none .yield []
  | .block (op :: ops) ids :: rest =>
    set { m with stack := .block ops ids :: rest }
    execOp op
  | _ => halt (.stuck "no block to run") none

/-- The machine at the start of a call to `f`. -/
def Machine.init (oracle : Nat → Int) (mod : Module) (f : Func) (args : List RVal) :
    Except Halt Machine :=
  let m : Machine := {
    env := {}, stack := [], oracle, space := mod.space,
    funcs := mod.funcs.foldl (fun acc g => acc.insert g.name g) {} }
  let start : SM Unit := do
    let scopes ← enterCall none f.params args
    push (.call {} [] f.rets scopes none)
    push (.block f.body.ops [])
  match start.run m with
  | .ok ((), m') => .ok m'
  | .error h => .error h

/-- Run `n` steps. An `error` is a halted run. -/
def runSteps : Nat → Machine → Except Halt Machine
  | 0, m => .ok m
  | n + 1, m =>
    match step.run m with
    | .ok ((), m') => runSteps n m'
    | .error h => .error h

/-- The state after `n` steps of a call. -/
def stateAt (oracle : Nat → Int) (mod : Module) (f : Func) (args : List RVal) (n : Nat) :
    Except Halt Machine :=
  (Machine.init oracle mod f args).bind (runSteps n)

/-- Whether any active loop is a `progress` loop. -/
def Machine.inProgressLoop (m : Machine) : Bool :=
  m.stack.any fun | .loop true .. => true | _ => false

end Fir
