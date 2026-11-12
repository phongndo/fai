import Std.Data.HashMap
import Std.Data.ExtTreeMap
import Fir.Basic
import Fir.Syntax
import Fir.Sem
import Fir.Mem

/-!
# Reference interpreter

A small-step machine: `step` runs one op. The machine is a *core* (memory, scopes, and the
oracle) plus an explicit stack of frames, so every intermediate state can be inspected.
`Fir.Behavior` uses that to define divergence and the `progress` rule precisely.

Values are bound in the frames, not the core. Each region's block frame holds the bindings its
ops made, and they go when the frame is popped; a call starts a fresh environment holding only
its parameters. A name is looked up in the current call's block frames, innermost first. So a
value is visible exactly where the verifier allows it to be used, and a use of anything else
gets stuck.

A `cf.blocks` op runs like a loop whose iterations may start at any of its blocks: its frame
stays on the stack while its blocks run above it, one at a time. A jump (`cf.br`, `cf.cond_br`,
`cf.switch`) pops the frames above the nearest `cf.blocks` frame, ending their stack memory, and
starts the target block with only its parameters bound, as `cf.continue` starts an iteration.

The split is for proofs. Ops on values and memory are computations on the core alone (`CM`):
they take their operands' values and return their results' values, and never see the stack or
the environment. Only the control-flow layer (`step`, `execOp`, `terminate`) evaluates operands
and binds results, and it is written as plain functions on machines. Two machines that run
different code over the same core then provably compute the same core, and machines whose
environments differ can be related name by name.

Every free choice (what `freeze` of `poison` gives, allocation ids, tags, addresses, whether an
allocation fails, comparisons of one-past-the-end pointers) comes from an *oracle*. The semantics
quantifies over every oracle; the command-line tool uses one that always answers `0`, which
means: `freeze` gives `0`, allocations succeed, ids count up from 1, and addresses are assigned
first-fit from `0x1000`.

A call to an external function is an *event*: the core keeps the trace of events so far. The
*world* answers each call (`World`), from the events so far, what the callee is shown, and one
oracle answer; refinement holds the world fixed and quantifies over it (`Fir.Behavior`). The tool
uses the world that answers every call with zeros and changes nothing.
-/

namespace Fir

/-- The values bound in one region frame, by name. -/
abbrev Env := Std.HashMap String RVal

/-- A stack frame. The top of the stack is always a `block`. -/
inductive Frame where
  /-- The ops left to run in the current region, the stack allocations it made, and the values
  it bound (its parameters and its ops' results). -/
  | block (ops : List Op) (allocs : List Nat) (env : Env)
  /-- A `cf.if` waiting for its region to `cf.yield`. -/
  | ifJoin (results : List Result) (loc : Option Loc)
  /-- A running `cf.loop`. Its body runs in the frames above it. -/
  | loop (progress : Bool) (body : Region) (results : List Result) (loc : Option Loc)
  /-- A function call: where the results go, the return types, and the `noalias` scopes the
  call opened. Lookups stop here: a callee sees only its own frames. -/
  | call (results : List Result) (rets : List Ty) (scopes : List Nat) (loc : Option Loc)
  /-- A running `cf.blocks`. Its current block runs in the frames above it. -/
  | blocks (progress : Bool) (blocks : List Region) (results : List Result) (loc : Option Loc)

/-- An active `noalias` or `readonly` scope: one function parameter during one call, or a
`const` global for the whole run (a `readonly` scope on its first tag, which every pointer to it
is derived from). -/
structure Scope where
  alloc : Nat
  tag : Nat
  noalias : Bool
  readonly : Bool
  const : Bool := false

/-- What a `noalias` scope records per byte: accessed through a pointer derived from the
parameter, accessed through another pointer, written. All three is UB. -/
abbrev Mark := Bool × Bool × Bool

abbrev Marks := Std.ExtTreeMap Nat Mark

/-! ## The environment -/

/-- What an external function is shown when it is called: its name and result types, its
arguments, and the bytes of every allocation its effects let it read, by allocation id (after the
call has exposed everything it can reach). -/
structure Call where
  callee : String
  rets : List Ty
  args : List RVal
  mem : List (Nat × List Byte)

/-- An allocation the environment makes: its id and first tag (both unused so far), size,
alignment, allocator family, and contents. -/
structure NewAlloc where
  id : Nat
  tag : Nat
  size : Nat
  align : Nat
  family : String
  bytes : List Byte

/-- How an external function answers a call. -/
inductive Answer where
  /-- Return `results`, after writing `bytes` at `off` in allocation `a` for each `(a, off, bytes)`
  in `writes`, freeing the allocations `frees`, and making `news`. -/
  | ret (results : List RVal) (writes : List (Nat × Nat × List Byte)) (frees : List Nat)
      (news : List NewAlloc)
  /-- Never return: the callee ends the program (`exit`, `abort`) or runs forever. -/
  | never

/-- The world outside the program, its environment: how each external call is answered, from the events so
far, the call, and one oracle answer, so one environment can answer a call in many ways. The
semantics quantifies over every oracle and holds the environment fixed: refinement is checked
against each environment (`Func.Refines`). An answer the callee's declared effects don't allow
is never given (`Answer.valid`); the call returns zeros instead. -/
structure World where
  answer : List Event → Call → Int → Answer

/-- The zero value of a value type. -/
def Ty.zero : Ty → RVal
  | .int w => .int w (.bits 0)
  | .ptr => .ptr (some .null)
  | .byte w => .bytes (List.replicate (w / 8) (.bits 0))
  | _ => .bytes []

/-- The environment `fir-ref run` uses: every external call returns zeros and changes nothing. -/
def World.zero : World := { answer := fun _ call _ => .ret (call.rets.map Ty.zero) [] [] [] }

/-- Everything but the frame stack. -/
structure Core where
  funcs : Std.HashMap String Func
  externs : Std.HashMap String Extern := {}
  space : SpaceCfg
  oracle : Nat → Int
  world : World
  /-- The events so far, oldest first. Only the control layer adds to it (`Machine.record`). -/
  trace : List Event := []
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
  /-- Pointers to the globals, and to the functions whose address has been taken. -/
  addrs : Std.ExtTreeMap String Ptr := ∅

structure Machine where
  core : Core
  stack : List Frame

/-- How a run ends: its behavior, the location of the op that ended it, a note for people, and
(for a return from the outermost call) the heap allocations still live. -/
structure Halt where
  outcome : Outcome
  loc : Option Loc
  note : String := ""
  leaks : List String := []

/-- A computation on the core. -/
abbrev CM := StateT Core (Except Halt)

def halt {μ : Type → Type} [MonadExcept Halt μ] (b : Outcome) (loc : Option Loc)
    (note : String := "") : μ α :=
  throw { outcome := b, loc, note }

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

/-! ## Environments -/

/-- A name's value: from the innermost block frame of the current call that binds it. Lookups
stop at the call frame. -/
def lookup (n : String) : List Frame → Option RVal
  | [] => none
  | .block _ _ env :: fs => match env[n]? with
    | some v => some v
    | none => lookup n fs
  | .call .. :: _ => none
  | _ :: fs => lookup n fs

/-- An operand's value. Reads only the stack's environments. -/
def operandIn (fs : List Frame) (loc : Option Loc) : Operand → Except Halt RVal
  | .var n => match lookup n fs with
    | some v => pure v
    | none => halt (.stuck s!"%{n} is not defined") loc
  | .hole n _ => halt (.hole n) loc

/-- The values of an op's operands. -/
def operands (fs : List Frame) (loc : Option Loc) (args : List Operand) : Except Halt (List RVal) :=
  args.mapM (operandIn fs loc)

/-- Bind values to names; a later binding of a name replaces an earlier one. -/
def Env.bindAll (env : Env) : List Result → List RVal → Env
  | r :: rs, v :: vs => Env.bindAll (env.insert r.name v) rs vs
  | _, _ => env

/-- Bind values in the current region: the top frame, which is a block in a running machine. -/
def bindTop (rs : List Result) (vs : List RVal) : List Frame → List Frame
  | .block ops ids env :: fs => .block ops ids (env.bindAll rs vs) :: fs
  | fs => fs

mutual
  /-- Whether a value has a type. An aggregate has its type's shape: a struct's fields, an
  array's elements, a slice's pointer and integer length, or a union's `i32` tag and the payload of
  the variant it names. -/
  def RVal.hasTy : RVal → Ty → Bool
    | .int w _, .int w' => w == w'
    | .ptr _, .ptr => true
    | .bytes bs, .byte w => bs.length * 8 == w
    | .agg vs, .struct _ fs => RVal.hasTys vs fs
    | .agg vs, .array n e => vs.length == n && RVal.allHaveTy vs e
    | .agg [.ptr _, .int _ _], .slice => true
    | .agg [.int 32 (.bits t), v], .union ts =>
      match ts[t.toNat]? with
      | some u => RVal.hasTy v u
      | none => false
    | _, _ => false
  def RVal.hasTys : List RVal → List Ty → Bool
    | [], [] => true
    | v :: vs, t :: ts => RVal.hasTy v t && RVal.hasTys vs ts
    | _, _ => false
  def RVal.allHaveTy : List RVal → Ty → Bool
    | [], _ => true
    | v :: vs, t => RVal.hasTy v t && RVal.allHaveTy vs t
end

mutual
  /-- An aggregate's scalars, depth first; a scalar is its own. -/
  def RVal.leaves : RVal → List RVal
    | .agg vs => RVal.leavesList vs
    | v => [v]
  def RVal.leavesList : List RVal → List RVal
    | [] => []
    | v :: vs => RVal.leaves v ++ RVal.leavesList vs
end

/-- `n` values of one shape, each built by `f` from the front of a list of scalars. -/
def buildN (f : List RVal → Option (RVal × List RVal)) : Nat → List RVal → Option (List RVal × List RVal)
  | 0, vs => some ([], vs)
  | n + 1, vs => do
    let (x, vs) ← f vs
    let (xs, vs) ← buildN f n vs
    pure (x :: xs, vs)

mutual
  /-- A value of a type with a layout, from the front of a list of its scalars (`Ty.leaves`), and
  the scalars left over. -/
  def Ty.build : Ty → List RVal → Option (RVal × List RVal)
    | .struct _ fs, vs => (Ty.buildList fs vs).map fun (xs, rest) => (.agg xs, rest)
    | .array n e, vs => (buildN (Ty.build e) n vs).map fun (xs, rest) => (.agg xs, rest)
    | .slice, p :: n :: rest => some (.agg [p, n], rest)
    | .slice, _ => none
    | _, v :: rest => some (v, rest)
    | _, [] => none
  def Ty.buildList : List Ty → List RVal → Option (List RVal × List RVal)
    | [], vs => some ([], vs)
    | t :: ts, vs => do
      let (x, vs) ← Ty.build t vs
      let (xs, vs) ← Ty.buildList ts vs
      pure (x :: xs, vs)
end

/-- Check that there is one value per result, of the result's type. -/
def checkTypes (loc : Option Loc) : List Result → List RVal → CM Unit
  | [], [] => pure ()
  | r :: rs, v :: vs => do
    unless v.hasTy r.ty do halt (.stuck s!"%{r.name} has type {r.ty} but got another type") loc
    checkTypes loc rs vs
  | _, _ => halt (.stuck "wrong number of values") loc

def allocIn (c : Core) (loc : Option Loc) (a : Nat) : Except Halt Alloc :=
  match c.allocs[a]? with
  | some al => pure al
  | none => halt (.stuck s!"no allocation #{a}") loc

def getAlloc (loc : Option Loc) (a : Nat) : CM Alloc := do allocIn (← get) loc a

def setAlloc (a : Nat) (al : Alloc) : CM Unit :=
  modify fun c => { c with allocs := c.allocs.insert a al }

/-! ## Addresses -/

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
  | .global g _ => s!"@{g} is a global"
  | .func f => s!"@{f} is a function"

/-- Where an access goes (allocation, tag, offset), after checking lifetime, bounds, and
alignment. Changes nothing. -/
def checkAccess (c : Core) (loc : Option Loc) (p : Ptr) (size align : Nat) :
    Except Halt (Nat × Nat × Nat) := do
  let (a, t, off) ← resolveIn c loc p size
  let al ← allocIn c loc a
  unless al.live do ub .useAfterFree loc (deadNote al)
  if let .func f := al.kind then ub .funcAccess loc s!"@{f} is a function"
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
        ub (if s.const then .constWrite else .readonly) loc (if s.const then
          "write to a const global" else "write through a pointer derived from a readonly parameter")
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
  | _ => halt (.stuck s!"{ty} is not a value type") loc

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
      ub .badFree loc <| match al.kind with
        | .heap f => s!"allocated at {renderLoc al.site} by {f}"
        | .stack => s!"allocated at {renderLoc al.site} by mem.stack"
        | .global g _ => s!"@{g} is a global"
        | .func f => s!"@{f} is a function"
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

/-- Check values about to be bound to results: their types, then their facts (a violated fact is
UB). Reads the core and changes nothing. -/
def checkResults (loc : Option Loc) (rs : List Result) (vs : List RVal) : CM Unit := do
  checkTypes loc rs vs
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

/-- `p` moved by `n` bytes (`ptr.offset`). In bounds, it is `none` (`poison`) when `p` or the
result is outside `[0, size]` of a live allocation; an offset of 0 always gives `p`. -/
def offsetBy (loc : Option Loc) (inbounds : Bool) (p : Ptr) (n : Int) : CM (Option Ptr) := do
  let c ← get
  if n == 0 then return some p
  match p with
  | .rel a t off =>
    let al ← getAlloc loc a
    let ok := al.live && 0 ≤ off && off ≤ al.size && 0 ≤ off + n && off + n ≤ al.size
    pure (if inbounds && !ok then none else some (.rel a t (off + n)))
  | .abs addr cands =>
    let addr' := addrMod c (addr + n)
    if !inbounds then return some (.abs addr' cands)
    let keep := cands.filter fun (a, _) =>
      match c.allocs[a]? with
      | some al => match al.base with
        | some b => al.live && b ≤ addr && addr ≤ b + al.size && (b : Int) ≤ addr + n &&
            addr + n ≤ (b + al.size : Int)
        | none => false
      | none => false
    pure (if keep.isEmpty then none else some (.abs addr' keep))

/-! ## Aggregates, unions, and slices -/

/-- Where the leaf at offset `off` of an aggregate at `p` is: `p` moved by `off`, as
`ptr.offset.wrap` by the address-sized integer `off`. -/
def leafPtr (loc : Option Loc) (p : Option Ptr) (off : Nat) : CM (Option Ptr) := do
  let c ← get
  match p with
  | none => pure none
  | some p => offsetBy loc false p (BitVec.ofInt c.space.addrBits off).toInt

/-- Load leaves `(offset, type)` of an aggregate at `p`, each as `mem.load` of its scalar type
with the alignment its offset keeps. -/
def loadLeaves (loc : Option Loc) (align : Nat) (p : Option Ptr) :
    List (Nat × Ty) → CM (List RVal)
  | [] => pure []
  | (off, t) :: ls => do
    let v ← loadC loc t (Nat.gcd align off) (← leafPtr loc p off)
    let vs ← loadLeaves loc align p ls
    pure (v :: vs)

/-- Store scalars at leaves `(offset, type)` of an aggregate at `p`, each as `mem.store`. -/
def storeLeaves (loc : Option Loc) (align : Nat) (p : Option Ptr) :
    List (Nat × Ty) → List RVal → CM Unit
  | (off, t) :: ls, v :: vs => do
    storeC loc t (Nat.gcd align off) v (← leafPtr loc p off)
    storeLeaves loc align p ls vs
  | _, _ => pure ()

/-- Load a value of type `ty`: a scalar as itself, an aggregate leaf by leaf, in order, padding
untouched (decision: Aggregate values). -/
def loadAny (loc : Option Loc) (ty : Ty) (align : Nat) (p : Option Ptr) : CM RVal := do
  if ty.isValue then loadC loc ty align p else
  let vs ← loadLeaves loc align p (ty.leaves (← get).space)
  match ty.build vs with
  | some (v, []) => pure v
  | _ => halt (.stuck s!"{ty} is not a value type") loc

/-- Store a value of type `ty`: a scalar as itself, an aggregate leaf by leaf. -/
def storeAny (loc : Option Loc) (ty : Ty) (align : Nat) (v : RVal) (p : Option Ptr) : CM Unit := do
  if ty.isValue then storeC loc ty align v p else
  unless v.hasTy ty do halt (.stuck s!"the stored value isn't a {ty}") loc
  storeLeaves loc align p (ty.leaves (← get).space) v.leaves

/-- Where element `i` of slice `s` of `ty`s is, after checking `i` against the length: an index
not below it traps (`trap`) or is UB, and a `poison` index or length is UB. The element is at
`ptr.offset.inbounds` by `i` times the stride, wrapped to the address size. -/
def sliceElem (loc : Option Loc) (trap : Bool) (ty : Ty) (s i : RVal) : CM (Option Ptr) := do
  let c ← get
  let aw := c.space.addrBits
  let .agg [pv, nv] := s | halt (.stuck "expected a slice") loc
  let p ← asPtr loc pv
  let n ← asInt loc aw nv
  let i ← asInt loc aw i
  match i, n with
  | .bits x, .bits m =>
    unless x.ult m do
      if trap then halt (.trap .bounds) loc else ub .bounds loc s!"index {x.toNat}, length {m.toNat}"
    match p with
    | none => pure none
    | some p => offsetBy loc true p (x * BitVec.ofInt aw (ty.stride c.space)).toInt
  | _, _ => ub .poison loc "slice index or length is poison"

/-- Evaluate an op without regions that doesn't touch the stack. -/
def evalSimple (loc : Option Loc) (k : OpKind) (rs : List Result) (vs : List RVal) :
    CM (List RVal) := do
  let c ← get
  let aw := c.space.addrBits
  match k, rs, vs with
  | .const n, [r], [] => pure [.int _ (Sem.const r.ty.width n)]
  | .poison, [r], [] =>
    match r.ty with
    | .ptr => pure [.ptr none]
    | .byte w => pure [.bytes (List.replicate (w / 8) .poison)]
    | t => pure [.int t.width .poison]
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
  | .load align, [r], [p] => do pure [← loadAny loc r.ty align (← asPtr loc p)]
  | .store ty align, [], [v, p] => do storeAny loc ty align v (← asPtr loc p); pure []
  -- Pointers
  | .ptrNull, [_], [] => pure [.ptr (some .null)]
  | .ptrOffset inbounds, [_], [p, n] => do
    let some p ← asPtr loc p | return [.ptr none]
    let .bits n ← asInt loc aw n | return [.ptr none]
    pure [.ptr (← offsetBy loc inbounds p n.toInt)]
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
  -- Layout
  | .tySize ty, [_], [] => pure [addrInt c (ty.size c.space)]
  | .tyAlign ty, [_], [] => pure [addrInt c (ty.align c.space)]
  | .tyOffset ty i, [_], [] => pure [addrInt c ((ty.fieldOffset? c.space i).getD 0)]
  | .ptrField inbounds ty i, [_], [p] => do
    let some p ← asPtr loc p | return [.ptr none]
    pure [.ptr (← offsetBy loc inbounds p ((ty.fieldOffset? c.space i).getD 0))]
  | .ptrIndex inbounds ty, [_], [p, i] => do
    let i ← asInt loc aw i
    let some p ← asPtr loc p | return [.ptr none]
    let .bits i := i | return [.ptr none]
    let n := i.toInt * ty.stride c.space
    let wrapped := (BitVec.ofInt aw n).toInt
    if inbounds && wrapped != n then return [.ptr none]
    pure [.ptr (← offsetBy loc inbounds p wrapped)]
  | .memCopy ty align, [], [d, s] => do
    let w := 8 * ty.size c.space
    let v ← loadC loc (.byte w) align (← asPtr loc s)
    storeC loc (.byte w) align v (← asPtr loc d)
    pure []
  -- Globals and functions
  | .memGlobal g, [_], [] =>
    match c.addrs[g]? with
    | some p => pure [.ptr (some p)]
    | none => halt (.stuck s!"no global @{g}") loc
  | .funcAddr f, [_], [] => do
    if let some p := c.addrs[f]? then return [.ptr (some p)]
    unless c.funcs.contains f || c.externs.contains f do halt (.stuck s!"no function @{f}") loc
    let p ← newAlloc loc 0 1 (.func f)
    modify fun c => { c with addrs := c.addrs.insert f p }
    pure [.ptr (some p)]
  -- Building blocks
  | .aggMake, [_], vs => pure [.agg vs]
  | .aggExtract i, [_], [.agg vs] =>
    match vs[i]? with
    | some v => pure [v]
    | none => halt (.stuck s!"no part {i}") loc
  | .aggInsert i, [_], [.agg vs, v] =>
    if i < vs.length then pure [.agg (vs.set i v)] else halt (.stuck s!"no part {i}") loc
  | .overflow op signed, [r, _], [a, b] => do
    match ← asInt loc r.ty.width a, ← asInt loc r.ty.width b with
    | .bits x, .bits y =>
      pure [.int _ (.bits (Sem.wrapOp op x y)),
        .int 1 (.bits (BitVec.ofBool (Sem.overflow signed op x y)))]
    | _, _ => pure [.int r.ty.width .poison, .int 1 .poison]
  | .unionMake i, [_], [v] => pure [.agg [.int 32 (.bits (BitVec.ofNat 32 i)), v]]
  | .unionTag, [_], [.agg [.int 32 t, _]] => pure [.int 32 t]
  | .unionGet trap i, [_], [.agg [.int 32 (.bits t), v]] =>
    if t.toNat = i then pure [v]
    else if trap then halt (.trap .tag) loc
    else ub .tag loc s!"the union holds variant {t.toNat}"
  | .sliceMake, [_], [p, n] => do
    let p ← asPtr loc p
    let n ← asInt loc aw n
    pure [.agg [.ptr p, .int aw n]]
  | .slicePtr, [_], [.agg [p@(.ptr _), _]] => pure [p]
  | .sliceLen, [_], [.agg [_, n@(.int _ _)]] => pure [n]
  | .sliceGet trap align, [r], [sv, i] => do
    pure [← loadAny loc r.ty align (← sliceElem loc trap r.ty sv i)]
  | .sliceSet trap ty align, [], [v, sv, i] => do
    storeAny loc ty align v (← sliceElem loc trap ty sv i)
    pure []
  | .check reason, [], [x] => do
    match ← asInt loc 1 x with
    | .poison => ub .poison loc "check of poison"
    | .bits b => if b = 1 then pure [] else halt (.trap reason) loc
  | _, _, _ => halt (.stuck "malformed op") loc

/-- Compute an op without regions that doesn't touch the stack, from its operands' values, and
check its results. -/
def simpleOp (loc : Option Loc) (k : OpKind) (results : List Result) (vs : List RVal) :
    CM (List RVal) := do
  let outs ← evalSimple loc k results vs
  checkResults loc results outs
  pure outs

/-- Open a parameter's `noalias` or `readonly` scope, if it has one: the pointer gets a fresh tag
derived from the argument's. Gives the parameter's value and the scope opened. -/
def openScope (loc : Option Loc) (r : Result) (v : RVal) : CM (RVal × Option Nat) := do
  let noalias := r.facts.any (·.fact == .noalias)
  let readonly := r.facts.any (·.fact == .readonly)
  if !(noalias || readonly) then return (v, none)
  let .ptr (some p) := v | return (v, none)
  -- A pointer that can't access memory (null, dangling) opens no scope. An ambiguous one halts.
  let some (a, t, off) ← tryCatch (some <$> resolve loc p 0)
      (fun h => if h.outcome matches .ub _ then pure none else throw h) | return (v, none)
  let t' ← freshTag (some t)
  let c ← get
  let id := c.nextScope
  set { c with
    scopes := c.scopes.insert id { alloc := a, tag := t', noalias, readonly },
    nextScope := id + 1 }
  pure (.ptr (some (.rel a t' off)), some id)

/-- Check a callee's parameters and open their `noalias` and `readonly` scopes. Gives the values
to bind to the parameters and the scopes opened. -/
def enterCall (loc : Option Loc) (params : List Result) (vs : List RVal) :
    CM (List RVal × List Nat) := do
  checkResults loc params vs
  let opened ← (params.zip vs).mapM fun (r, v) => openScope loc r v
  pure (opened.map (·.1), (opened.filterMap (·.2)).reverse)

/-- Close the scopes a call opened. -/
def closeScopes (ids : List Nat) : CM Unit :=
  modify fun c => { c with
    scopes := ids.foldl (·.erase ·) c.scopes, marks := ids.foldl (·.erase ·) c.marks }

/-- The heap allocations still live, for the leak report. -/
def leaks (c : Core) : List String :=
  c.allocs.toList.filterMap fun (_, al) =>
    match al.live, al.kind with
    | true, .heap f => some s!"leak: {al.size} bytes from {f} at {renderLoc al.site}"
    | _, _ => none

/-! ## External calls -/

/-- The `(allocation, tag)` pairs a pointer may access memory through. -/
def Ptr.pairs : Ptr → List (Nat × Nat)
  | .rel a t _ => [(a, t)]
  | .abs _ cands => cands

def RVal.pairs : RVal → List (Nat × Nat)
  | .ptr (some p) => p.pairs
  | _ => []

def Byte.pairs : Byte → List (Nat × Nat)
  | .frag p _ => p.pairs
  | _ => []

/-- `xs`, then the elements of `ys` it doesn't have yet, in order. -/
def addNew [BEq α] (xs ys : List α) : List α :=
  ys.foldl (fun acc y => if acc.contains y then acc else acc ++ [y]) xs

/-- Whether an external function with effects `fx` may access allocation `a` in the way `how`
names (`.read` or `.write`): `a` is live and not a function, and one of its classes is listed.
`argAllocs` are the allocations its pointer arguments point into, `reach` what it can reach. A
callee never writes a `const` global. -/
def mayAccess (c : Core) (fx : List ExtEffect) (how : MemClass → ExtEffect) (argAllocs : List Nat)
    (reach : List (Nat × Nat)) (a : Nat) : Bool :=
  match c.allocs[a]? with
  | some al =>
    let isGlobal := al.kind matches .global ..
    al.live && !(al.kind matches .func _) && !(how .args == .write .args && al.kind matches .global _ true) &&
      ((fx.contains (how .args) && argAllocs.contains a) ||
       (fx.contains (how .globals) && isGlobal) ||
       (fx.contains (how .exposed) && reach.any (·.1 == a)))
  | none => false

/-- Where an external call's reach starts: its pointer arguments' pairs, then the globals (their
first tags) if its effects name `globals`, then every exposed pair if they name `exposed`. -/
def externRoots (c : Core) (fx : List ExtEffect) (vs : List RVal) : List (Nat × Nat) :=
  let names (m : MemClass) := fx.contains (.read m) || fx.contains (.write m)
  let globals := if names .globals then
      c.allocs.foldl (init := []) fun acc a al => if al.kind matches .global .. then acc ++ [(a, a)] else acc
    else []
  let exposed := if names .exposed then
      c.allocs.foldl (init := []) fun acc a al => if al.live then acc ++ al.exposed.map (a, ·) else acc
    else []
  addNew [] (vs.flatMap RVal.pairs ++ globals ++ exposed)

/-- One round of growing an external call's reach: add the pointers stored in every allocation
in reach that it may read. -/
def growReach (c : Core) (fx : List ExtEffect) (argAllocs : List Nat) (reach : List (Nat × Nat)) :
    List (Nat × Nat) :=
  addNew reach ((addNew [] (reach.map (·.1))).flatMap fun a =>
    match c.allocs[a]? with
    | some al => if mayAccess c fx .read argAllocs reach a then
        (readBytes (c.mem.getD a ∅) 0 al.size).flatMap Byte.pairs else []
    | none => [])

/-- The pairs an external call can reach: from its roots, everything stored in memory it may read,
until nothing new is found. Each round adds a pair or changes nothing, and every pair holds a tag,
so as many rounds as there are tags, plus one, reach the end. -/
def externReach (c : Core) (fx : List ExtEffect) (vs : List RVal) : List (Nat × Nat) :=
  Nat.repeat (growReach c fx ((vs.flatMap RVal.pairs).map (·.1))) (c.tags.size + 1)
    (externRoots c fx vs)

def Ptr.okIn (reach : List (Nat × Nat)) : Ptr → Bool
  | .rel a t _ => reach.contains (a, t)
  | .abs _ cands => cands.isEmpty

def Byte.okIn (reach : List (Nat × Nat)) : Byte → Bool
  | .frag p _ => p.okIn reach
  | _ => true

/-- A value the environment may hand back: its pointers are ones it can reach, or addresses with
no provenance. -/
def RVal.okIn (reach : List (Nat × Nat)) : RVal → Bool
  | .ptr (some p) => p.okIn reach
  | .bytes bs => bs.all (Byte.okIn reach)
  | _ => true

/-- Whether an answer stays within the callee's declared effects: results of its types, writes
and frees only of memory it may write (frees only of heap memory, if it may `free`), new
allocations only if it may `alloc`, with fresh ids and tags, and pointers only to what it can
reach (or makes). It may not return only if it may `trap` or `diverge`. -/
def Answer.valid (c : Core) (x : Extern) (argAllocs : List Nat) (reach : List (Nat × Nat)) :
    Answer → Bool
  | .never => x.effects.contains .trap || x.effects.contains .diverge
  | .ret results writes frees news =>
    let reach' := reach ++ news.map fun n => (n.id, n.tag)
    let writable (a : Nat) := mayAccess c x.effects .write argAllocs reach a
    let size (a : Nat) := (c.allocs[a]?.map (·.size)).getD 0
    results.length == x.rets.length &&
    (results.zip x.rets).all (fun (v, t) => v.hasTy t && v.okIn reach') &&
    writes.all (fun (a, off, bs) => writable a && off + bs.length ≤ size a && bs.all (Byte.okIn reach')) &&
    (frees.isEmpty || x.effects.contains .free) &&
    frees.all (fun a => writable a && (c.allocs[a]?.map (·.kind matches .heap _)) == some true) &&
    (news.isEmpty || x.effects.contains .alloc) &&
    (news.map (·.id)).eraseDups.length == news.length &&
    (news.map (·.tag)).eraseDups.length == news.length &&
    news.all (fun n => !c.allocs.contains n.id && !c.tags.contains n.tag &&
      n.bytes.length == n.size && n.align > 0 && n.bytes.all (Byte.okIn reach'))

/-- Carry out what the environment did: write, free, and make allocations. -/
def applyAnswer (loc : Option Loc) (writes : List (Nat × Nat × List Byte)) (frees : List Nat)
    (news : List NewAlloc) : CM Unit := do
  for (a, off, bs) in writes do
    modify fun c => { c with mem := c.mem.insert a (writeBytes (c.mem.getD a ∅) off bs) }
  for a in frees do
    let al ← getAlloc loc a
    setAlloc a { al with live := false, freedAt := loc }
  for n in news do
    let al : Alloc := { size := n.size, align := n.align, kind := .heap n.family }
    setAlloc n.id { al with site := loc, exposed := [n.tag] }
    modify fun c =>
      { c with tags := c.tags.insert n.tag none, mem := c.mem.insert n.id (writeBytes ∅ 0 n.bytes) }

/-- Call an external function: check the arguments, expose everything the callee can reach (it
may turn any pointer it holds into an integer), show it what it may read, and carry out its answer.
Gives the call's event; the control layer records it. -/
def callExtern (loc : Option Loc) (x : Extern) (vs : List RVal) : CM Event := do
  unless vs.length == x.params.length && (vs.zip x.params).all (fun (v, t) => v.hasTy t) do
    halt (.stuck s!"wrong arguments for @{x.name}") loc
  let c ← get
  let argAllocs := (vs.flatMap RVal.pairs).map (·.1)
  let reach := externReach c x.effects vs
  for (a, t) in reach do
    if ((← get).allocs[a]?.map (·.live)) == some true then
      let _ ← ptrExpose loc (.rel a t 0)
  let c ← get
  let mem := (addNew [] (reach.map (·.1))).filterMap fun a =>
    match c.allocs[a]? with
    | some al => if mayAccess c x.effects .read argAllocs reach a then
        some (a, readBytes (c.mem.getD a ∅) 0 al.size) else none
    | none => none
  let k ← choose
  let c ← get
  let answer := c.world.answer c.trace { callee := x.name, rets := x.rets, args := vs, mem } k
  let answer := if answer.valid c x argAllocs reach then answer
    else .ret (x.rets.map Ty.zero) [] [] []
  match answer with
  | .never => pure { callee := x.name, args := vs, results := none }
  | .ret results writes frees news => do
    applyAnswer loc writes frees news
    pure { callee := x.name, args := vs, results := some results }

/-- The code an external call returns through: `func.ret` of its results, bound in a frame of
their own (`%0`, `%1`, …), so the caller checks them as it checks any callee's. -/
def externRet (loc : Option Loc) (vs : List RVal) : Frame :=
  .block [.mk .ret [] ((List.range vs.length).map fun i => .var (toString i)) [] loc] []
    (vs.zipIdx.foldl (fun env (v, i) => env.insert (toString i) v) {})

/-- What runs after a call that never returns: a loop that does nothing forever. It replaces the
whole stack, so no `progress` loop of the caller's is still running. -/
def hang : Frame :=
  .block [.mk (.loop false) [] [] [.mk [] [.mk .cont [] [] [] none] none] none] [] {}

/-! ## Control flow

These functions take and return whole machines. Core computations run through `Machine.exec`. -/

/-- Add an event to the trace. -/
def Machine.record (m : Machine) (e : Event) : Machine :=
  { m with core := { m.core with trace := m.core.trace ++ [e] } }

/-- Run a core computation on a machine's core. -/
def Machine.exec (m : Machine) (c : CM α) : Except Halt (α × Machine) :=
  match c.run m.core with
  | .ok (a, core) => .ok (a, { m with core })
  | .error h => .error h

/-- Check values for results on the core, then bind them in the current region. -/
def Machine.bindResults (m : Machine) (loc : Option Loc) (rs : List Result) (vs : List RVal) :
    Except Halt Machine := do
  let ((), m) ← m.exec (checkResults loc rs vs)
  pure { m with stack := bindTop rs vs m.stack }

def Frame.isCall : Frame → Bool
  | .call .. => true
  | _ => false

/-- Record a new stack allocation in the top block. -/
def addAllocId (id : Nat) : List Frame → List Frame
  | .block ops ids env :: rest => .block ops (id :: ids) env :: rest
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

def pickCall : Frame → Option (List Result × List Ty × List Nat × Option Loc)
  | .call rs rets scopes loc => some (rs, rets, scopes, loc)
  | _ => none

def pickBlocks : Frame → Option (Bool × List Region × List Result × Option Loc)
  | .blocks p bs rs loc => some (p, bs, rs, loc)
  | _ => none

/-- The stack allocations made by these frames' blocks. -/
def blockIds : List Frame → List Nat
  | [] => []
  | .block _ ids _ :: fs => ids ++ blockIds fs
  | _ :: fs => blockIds fs

/-- Start a loop iteration: push the body, with the loop state bound to its parameters. -/
def enterBody (m : Machine) (loc : Option Loc) (body : Region) (vs : List RVal) :
    Except Halt Machine := do
  let ((), m) ← m.exec (checkResults loc body.params vs)
  pure { m with stack := .block body.ops [] (Env.bindAll {} body.params vs) :: m.stack }

/-- Jump to block `s` of the nearest `cf.blocks`, with arguments `vs`: pop the frames above it,
ending their stack memory, and start the block. -/
def jump (m : Machine) (loc : Option Loc) (s : Succ) (vs : List RVal) : Except Halt Machine :=
  match splitStack pickBlocks m.stack with
  | some (above, (p, bs, rs, loc'), below) =>
    match bs.find? (·.label == some s.label) with
    | some b => do
      let ((), m) ← { m with stack := .blocks p bs rs loc' :: below }.exec
        (releaseIds (blockIds above))
      enterBody m loc b vs
    | none => halt (.stuck s!"no block ^{s.label}") loc
  | none => halt (.stuck "a jump outside cf.blocks") loc

/-- `cf.switch`'s target for the value `n` of a `w`-bit integer, with its arguments: the first
case whose key is `n` modulo `2^w`, or the default. `vs` are the targets' arguments in order. -/
def switchTarget (w n : Nat) (d : Succ) (cs : Cases) (vs : List RVal) : Succ × List RVal :=
  go cs (vs.drop d.nargs)
where
  go : Cases → List RVal → Succ × List RVal
    | [], _ => (d, vs.take d.nargs)
    | (k, s) :: cs, rest =>
      if (k % (2 ^ w : Int)).toNat == n then (s, rest.take s.nargs) else go cs (rest.drop s.nargs)

/-- Run a terminator. The current block has already been popped. -/
def terminate (m : Machine) (loc : Option Loc) (k : OpKind) (vs : List RVal) :
    Except Halt Machine :=
  match k with
  | .yield =>
    match m.stack with
    | .ifJoin rs loc' :: rest => { m with stack := rest }.bindResults loc' rs vs
    | .blocks _ _ rs loc' :: rest => { m with stack := rest }.bindResults loc' rs vs
    | .loop .. :: _ => halt (.stuck "a loop body must end with cf.break or cf.continue") loc
    | _ => halt (.stuck "the function ended without func.ret") loc
  | .br dest => jump m loc dest vs
  | .condBr t f => do
    let (c, m) ← m.exec (asInt loc 1 (vs.headD (.int 1 .poison)))
    match c with
    | .poison => ub .poison loc "branch on poison"
    | .bits b =>
      if b = 1 then jump m loc t ((vs.drop 1).take t.nargs)
      else jump m loc f ((vs.drop 1).drop t.nargs)
  | .switch d cs =>
    match vs with
    | .int w (.bits b) :: rest =>
      let (s, args) := switchTarget w b.toNat d cs rest
      jump m loc s args
    | .int _ .poison :: _ => ub .poison loc "branch on poison"
    | _ => halt (.stuck "cf.switch needs an integer") loc
  | .brk =>
    match splitStack pickLoop m.stack with
    | some (above, (_, _, rs, loc'), below) => do
      let ((), m) ← { m with stack := below }.exec (releaseIds (blockIds above))
      m.bindResults loc' rs vs
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
    | some (above, (rs, rets, scopes, loc'), below) =>
      if !(vs.length == rets.length && (vs.zip rets).all (fun (v, t) => v.hasTy t)) then
        halt (.stuck "func.ret values don't match the function's return types") loc
      else do
        let ((), m) ← m.exec (do releaseIds (blockIds above); closeScopes scopes)
        if below.isEmpty then
          throw { outcome := .ret vs, loc, leaks := leaks m.core }
        { m with stack := below }.bindResults loc' rs vs
    | none => halt (.stuck "func.ret outside a function") loc
  | _ => halt (.stuck "not a terminator") loc

/-- What a call op calls: a function by name, or the function its first operand points at,
which must have the given type. Either can be a function of the module or an external one. -/
inductive Callee where
  | direct (name : String)
  | indirect (sig : Ty)

def OpKind.callee? : OpKind → Option Callee
  | .call callee => some (.direct callee)
  | .callIndirect sig => some (.indirect sig)
  | _ => none

/-- A function a call can run. -/
inductive Target where
  | func (f : Func)
  | extern (x : Extern)

/-- The function a call runs, and the arguments it passes. An indirect call's pointer must
resolve to the start of a function whose parameter and result types are the signature's. -/
def callTarget (loc : Option Loc) : Callee → List RVal → CM (Target × List RVal)
  | .direct name, vs => do
    let c ← get
    match c.funcs[name]?, c.externs[name]? with
    | some f, _ => pure (.func f, vs)
    | none, some x => pure (.extern x, vs)
    | none, none => halt (.stuck s!"no function @{name}") loc
  | .indirect sig, v :: vs => do
    let some p ← asPtr loc v | ub .poison loc "call through a poison pointer"
    let (a, _, off) ← resolve loc p 0
    let al ← getAlloc loc a
    let .func name := al.kind | ub .badCall loc s!"#{a} is not a function"
    unless off == 0 do ub .badCall loc s!"offset {off} is not the start of @{name}"
    let c ← get
    let (tgt, t) ← match c.funcs[name]?, c.externs[name]? with
      | some f, _ => pure (Target.func f, Ty.func (f.params.map (·.ty)) f.rets)
      | none, some x => pure (.extern x, x.ty)
      | none, none => halt (.stuck s!"no function @{name}") loc
    unless t == sig do ub .badCall loc s!"@{name} has type {t}"
    pure (tgt, vs)
  | .indirect _, [] => halt (.stuck "malformed op") loc

/-- A stack allocation's size and alignment, in a memory space. -/
def OpKind.stackAlloc? : OpKind → Option (SpaceCfg → Nat × Nat)
  | .memStack size align => some fun _ => (size, align)
  | .memStackOf ty align => some fun sp => (ty.size sp, max align (ty.align sp))
  | _ => none

def OpKind.loopProgress? : OpKind → Option Bool
  | .loop p => some p
  | _ => none

def OpKind.isIf : OpKind → Bool
  | .if_ => true
  | _ => false

def OpKind.blocksProgress? : OpKind → Option Bool
  | .blocks p => some p
  | _ => none

/-- Run an op without regions. The current block, with the op removed, is on top of the stack. -/
def execFlat (m : Machine) (kind : OpKind) (results : List Result) (args : List Operand)
    (loc : Option Loc) : Except Halt Machine :=
  match kind.callee? with
  | some callee => do
    let vs ← operands m.stack loc args
    let ((tgt, vs), m) ← m.exec (callTarget loc callee vs)
    match tgt with
    | .func f => do
      let ((vs, scopes), m) ← m.exec (enterCall loc f.params vs)
      pure { m with
        stack := .block f.body.ops [] (Env.bindAll {} f.params vs) ::
          .call results f.rets scopes loc :: m.stack }
    | .extern x => do
      -- The call is an event: the environment answers it, and it is recorded at once.
      let (e, m) ← m.exec (callExtern loc x vs)
      let m := m.record e
      match e.results with
      | some rs => pure { m with stack := externRet loc rs :: .call results x.rets [] loc :: m.stack }
      | none => pure { m with stack := [hang] }
  | none =>
  match kind.stackAlloc? with
  | some dims => do
    let (size, align) := dims m.core.space
    let (p, m) ← m.exec (do
      let p ← newAlloc loc size align .stack
      checkResults loc results [.ptr (some p)]
      pure p)
    let id := match p with | .rel a .. => a | _ => 0
    pure { m with stack := bindTop results [.ptr (some p)] (addAllocId id m.stack) }
  | none =>
  if kind.isTerminator then do
    let vs ← operands m.stack loc args
    match m.stack with
    | f :: rest => do
      let ((), m) ← { m with stack := rest }.exec (releaseIds (blockIds [f]))
      terminate m loc kind vs
    | [] => terminate m loc kind vs
  else do
    let vs ← operands m.stack loc args
    let (outs, m) ← m.exec (simpleOp loc kind results vs)
    pure { m with stack := bindTop results outs m.stack }

/-- Run one op. The current block, with the op removed, is on top of the stack. -/
def execOp (m : Machine) : Op → Except Halt Machine
  | .mk kind results args regions loc =>
    match regions, kind.blocksProgress? with
    | [], _ => execFlat m kind results args loc
    | entry :: rest, some p =>
      enterBody { m with stack := .blocks p (entry :: rest) results loc :: m.stack } loc entry []
    | [body], none =>
      match kind.loopProgress? with
      | some p => do
        let vs ← operands m.stack loc args
        enterBody { m with stack := .loop p body results loc :: m.stack } loc body vs
      | none => halt (.stuck "malformed op") loc
    | [thn, els], none =>
      if kind.isIf then do
        let vs ← operands m.stack loc args
        let (c, m) ← m.exec (asInt loc 1 (vs.headD (.int 1 .poison)))
        match c with
        | .poison => ub .poison loc "branch on poison"
        | .bits b =>
          pure { m with
            stack := .block (if b = 1 then thn else els).ops [] {} :: .ifJoin results loc :: m.stack }
      else halt (.stuck "malformed op") loc
    | _, _ => halt (.stuck "malformed op") loc

/-- One step of the machine. -/
def step (m : Machine) : Except Halt Machine :=
  match m.stack with
  | .block [] ids _ :: rest => do
    -- Falling off the end of a region is an implicit `cf.yield` with no values.
    let ((), m) ← { m with stack := rest }.exec (releaseIds ids)
    terminate m none .yield []
  | .block (op :: ops) ids env :: rest => execOp { m with stack := .block ops ids env :: rest } op
  | _ => halt (.stuck "no block to run") none

/-! ## Globals -/

mutual
  /-- The names an initializer takes the address of, in order. -/
  def Init.syms : Init → List String
    | .sym s => [s]
    | .list items => Init.symsList items
    | _ => []
  def Init.symsList : List Init → List String
    | [] => []
    | i :: is => i.syms ++ Init.symsList is
end

/-- `bs` written over `base` from offset `off`. -/
def overlay (base : List Byte) : List (Nat × List Byte) → List Byte
  | [] => base
  | (off, bs) :: rest => overlay (base.take off ++ bs ++ base.drop (off + bs.length)) rest

mutual
  /-- The bytes an object of type `t` starts with. Padding is zero; an initializer that doesn't
  fit the type (which the verifier rejects) gives `poison`. -/
  def initBytes (sp : SpaceCfg) (addrs : Std.ExtTreeMap String Ptr) : Ty → Init → List Byte
    | t, .zero => List.replicate (t.size sp) (.bits 0)
    | .int w, .int n | .byte w, .int n => encodeInt w (Sem.const w n)
    | .ptr, .null => encodePtr sp (some .null)
    | .ptr, .sym s => encodePtr sp addrs[s]?
    | _, .bytes bs => bs.map fun b => .bits (BitVec.ofNat 8 b)
    | t@(.struct p fs), .list items =>
      overlay (List.replicate (t.size sp) (.bits 0))
        ((placeFields p (Ty.strides sp fs)).1.zip (initList sp addrs fs items))
    | t@(.array n e), .list items =>
      overlay (List.replicate (t.size sp) (.bits 0))
        (((List.range n).map (· * e.stride sp)).zip (initList sp addrs (List.replicate n e) items))
    | t, _ => List.replicate (t.size sp) .poison
  def initList (sp : SpaceCfg) (addrs : Std.ExtTreeMap String Ptr) :
      List Ty → List Init → List (List Byte)
    | t :: ts, i :: is => initBytes sp addrs t i :: initList sp addrs ts is
    | _, _ => []
end

/-- The core before a call from outside the module. Globals are allocations `1, 2, …`, in order,
each with its first tag numbered like it; next come the functions that initializers take the
address of, in the order they are first named (other functions get an allocation when `func.addr`
first names them). A `const` global gets a `readonly` scope for the whole run. -/
def Core.initial (oracle : Nat → Int) (world : World) (mod : Module) : Core :=
  let sp := mod.space
  let gs : List (Global × Nat) := mod.globals.zipIdx.map fun (g, i) => (g, i + 1)
  let fs : List (String × Nat) :=
    ((mod.globals.flatMap (·.init.syms)).eraseDups.filter fun n =>
      !mod.globals.any (·.name == n)).zipIdx.map fun (f, i) => (f, gs.length + i + 1)
  let globalAlloc (g : Global) : Alloc :=
    { size := g.ty.size sp, align := max g.align (g.ty.align sp), kind := .global g.name g.const }
  let funcAlloc (f : String) : Alloc := { size := 0, align := 1, kind := .func f }
  let allocs : List (Nat × Alloc) :=
    gs.map (fun x => (x.2, globalAlloc x.1)) ++ fs.map fun x => (x.2, funcAlloc x.1)
  let names : List (String × Nat) := gs.map (fun x => (x.1.name, x.2)) ++ fs
  let addrs : Std.ExtTreeMap String Ptr := names.foldl (fun m x => m.insert x.1 (.rel x.2 x.2 0)) ∅
  let consts : List (Nat × Scope) := ((gs.filter (·.1.const)).map (·.2)).zipIdx.map fun (a, id) =>
    (id, { alloc := a, tag := a, noalias := false, readonly := true, const := true })
  { oracle, world, space := sp,
    funcs := mod.funcs.foldl (fun acc g => acc.insert g.name g) {},
    externs := mod.externs.foldl (fun acc x => acc.insert x.name x) {},
    allocs := allocs.foldl (fun m x => m.insert x.1 x.2) ∅,
    mem := gs.foldl (fun m x => m.insert x.2 (writeBytes ∅ 0 (initBytes sp addrs x.1.ty x.1.init))) ∅,
    tags := allocs.foldl (fun m x => m.insert x.1 none) ∅,
    scopes := consts.foldl (fun m x => m.insert x.1 x.2) ∅,
    nextScope := consts.length,
    addrs }

/-- The machine at the start of a call to `f`. -/
def Machine.init (oracle : Nat → Int) (world : World) (mod : Module) (f : Func) (args : List RVal) :
    Except Halt Machine := do
  let ((vs, scopes), core) ← (enterCall none f.params args).run (Core.initial oracle world mod)
  pure { core, stack := [.block f.body.ops [] (Env.bindAll {} f.params vs), .call [] f.rets scopes none] }

/-- Run `n` steps. An `error` is a halted run. -/
def runSteps : Nat → Machine → Except Halt Machine
  | 0, m => .ok m
  | n + 1, m =>
    match step m with
    | .ok m' => runSteps n m'
    | .error h => .error h

/-- The state after `n` steps of a call. -/
def stateAt (oracle : Nat → Int) (world : World) (mod : Module) (f : Func) (args : List RVal)
    (n : Nat) : Except Halt Machine :=
  (Machine.init oracle world mod f args).bind (runSteps n)

/-- A `cf.loop progress` or `cf.blocks progress`: one that control may be assumed to leave. -/
def Frame.isProgressLoop : Frame → Bool
  | .loop true .. => true
  | .blocks true .. => true
  | _ => false

/-- Which frames are `progress` loops (or `progress` blocks), from the top of the stack down. -/
def Machine.shape (m : Machine) : List Bool := m.stack.map Frame.isProgressLoop

/-- The frame `d` from the bottom of the stack is a `progress` loop. -/
def Machine.inProgressLoopAt (m : Machine) (d : Nat) : Prop := m.shape.reverse[d]? = some true

/-- Whether any active loop is a `progress` loop. -/
def Machine.inProgressLoop (m : Machine) : Bool := m.shape.any id

end Fir
