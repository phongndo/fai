import Fir.AArch64
import Fir.Interp
import Fir.Layout
import Fir.Print

/-!
# The AArch64 LFIR machine

How `fir-ref run` runs an LFIR module for AArch64 (`layer lfir aarch64`). It is a register
machine over FIR's core: the memory, allocations, events, and oracle of `Fir.Interp` stay as they
are, and the machine adds the general-purpose registers `x0`…`x30`, `sp`, the flags NZCV, and a
stack of call frames, each with its own virtual registers. The instructions' bit-level meaning is
`Fir.AArch64`'s; this file adds what FIR needs on top:

* **Registers hold words**: 64 bits, or a pointer with its provenance. Adding or subtracting an
  integer keeps a pointer a pointer, as do moves, `csel`, and 64-bit loads and stores of all eight
  of its fragments; every other instruction reads a pointer as its address (which gives the
  allocation one if it has none yet, as `ptr.addr` does). Registers are never `poison`: where FIR
  has `poison` (an uninitialized byte, a `poison` argument), the machine takes an oracle choice,
  as `freeze` does.
* **Memory is flat**: an access through a pointer goes to its allocation; an access through an
  integer goes to whichever live allocation holds those bytes at that address, exposed or not.
  Lifetimes and bounds are checked; alignment, `noalias`, and `readonly` scopes are not (LFIR has
  no facts).
* **The stack** is one allocation of `stackSize` bytes; `sp` starts at its end.
* **Calls** follow AAPCS64 (decision: LFIR for AArch64): arguments in `x0`…`x7` and then in 8-byte
  stack slots from `sp`; one or two results in `x0` and `x1`, more in 8-byte slots at the address
  the caller passes in `x8`. A narrow integer travels in the low bits of its register. `bl`
  enters an LFIR function, which must leave `x19`…`x29` and `sp` as it found them, or calls an
  external function: one event, its results placed as above, and the caller-saved registers
  (`x0`…`x18`, `x30`) and flags then hold oracle choices. `ret` returns to the frame below,
  whatever `x30` holds: return addresses aren't modeled.
* **Runtime calls**: `aarch64.bl.alloc` and `aarch64.bl.free` allocate and free like `mem.alloc`
  and `mem.free`, without an event; `aarch64.trap.R` traps with reason `R`.

A function whose body is a plain `func.ret` of its parameters also runs: it returns those
values where the calling convention puts results.
-/

namespace Fir.AArch64

/-- What a register holds. -/
inductive Word where
  | bits (b : BitVec 64)
  | ptr (p : Ptr)
  deriving DecidableEq, Repr, Inhabited

/-- One running function: its blocks, the rest of the current block, its virtual registers, and
what `x19`…`x29` and `sp` held on entry. -/
structure LFrame where
  func : Func
  blocks : List Region
  ops : List Op
  vregs : Std.HashMap Nat Word := {}
  saved : List Word

structure LMachine where
  core : Core
  /-- `x0`…`x30`. -/
  regs : Array Word := Array.replicate 31 (.bits 0)
  sp : Word := .bits 0
  nzcv : BitVec 4 := 0
  frames : List LFrame := []
  /-- Where the outermost call's results go when it has more than two. -/
  resArea : Word := .bits 0
  /-- An external call didn't return: the machine runs on without doing anything. -/
  hung : Bool := false

abbrev LM := StateT LMachine (Except Halt)

/-- The machine stack's size in bytes. -/
def stackSize : Nat := 2 ^ 20

def liftCM (c : CM α) : LM α := fun m =>
  match c.run m.core with
  | .ok (a, core) => .ok (a, { m with core })
  | .error h => .error h

def stuckL (loc : Option Loc) (msg : String) : LM α := halt (.stuck msg) loc

/-! ## Registers -/

def frame (loc : Option Loc) : LM LFrame := do
  match (← get).frames with
  | f :: _ => pure f
  | [] => stuckL loc "no running function"

def readReg (loc : Option Loc) : Reg → LM Word
  | .xzr => pure (.bits 0)
  | .sp => do pure (← get).sp
  | .x n => do pure ((← get).regs.getD n (.bits 0))
  | .v n => do
    match (← frame loc).vregs[n]? with
    | some w => pure w
    | none => stuckL loc s!"v{n} is read before it is written"

def writeReg (r : Reg) (w : Word) : LM Unit :=
  modify fun m => match r with
    | .xzr => m
    | .sp => { m with sp := w }
    | .x n => { m with regs := m.regs.set! n w }
    | .v n => { m with frames := match m.frames with
      | f :: fs => { f with vregs := f.vregs.insert n w } :: fs
      | [] => [] }

/-- A word's bits: a pointer's address, given an address if it has none. -/
def toBits (loc : Option Loc) : Word → LM (BitVec 64)
  | .bits b => pure b
  | .ptr p => do pure (BitVec.ofNat 64 (← liftCM (ptrAddr loc p)))

def readBits (loc : Option Loc) (r : Reg) : LM (BitVec 64) := do toBits loc (← readReg loc r)

/-- A word moved by `k` bytes: a pointer stays one (`ptr.offset.wrap`). -/
def offsetWord (loc : Option Loc) (w : Word) (k : Int) : LM Word :=
  match w with
  | .bits b => pure (.bits (b + BitVec.ofInt 64 k))
  | .ptr p => do pure (.ptr ((← liftCM (offsetBy loc false p k)).getD p))

/-- An oracle choice of 64 bits. -/
def chooseBits : LM (BitVec 64) := do pure (BitVec.ofInt 64 (← liftCM choose))

/-! ## Memory -/

/-- The allocation and offset of the `size` bytes at `w`. A pointer reaches its allocation; an
integer, the live allocation that holds those bytes at that address. -/
def locate (loc : Option Loc) (w : Word) (size : Nat) : LM (Nat × Nat) := do
  let c := (← get).core
  let inAlloc (a : Nat) (off : Int) : LM (Nat × Nat) := do
    let al ← liftCM (getAlloc loc a)
    unless al.live do ub .useAfterFree loc (deadNote al)
    if let .func f := al.kind then ub .funcAccess loc s!"@{f} is a function"
    unless 0 ≤ off && off + size ≤ al.size do
      ub .outOfBounds loc s!"offset {off}, {size} bytes, allocation size {al.size}"
    pure (a, off.toNat)
  let flat (addr : Nat) : LM (Nat × Nat) := do
    let hit := c.allocs.toList.find? fun (_, al) =>
      match al.base with
      | some b => al.live && b ≤ addr && addr + size ≤ b + al.size
      | none => false
    match hit with
    | some (a, al) => pure (a, addr - al.base.getD 0)
    | none => ub .outOfBounds loc s!"address {addr} is in no live allocation"
  match w with
  | .ptr (.rel a _ off) => inAlloc a off
  | .ptr (.abs addr _) => flat addr
  | .bits b => flat b.toNat

/-- Bytes as a word: a pointer if they are its eight fragments in order, otherwise their bits,
little-endian, with a pointer fragment read as an address byte and a `poison` byte as an oracle
choice. -/
def wordOfBytes (loc : Option Loc) (bs : List Byte) : LM Word := do
  if bs.length == 8 then
    if let some p := ptrOfFrags? 8 bs then return .ptr p
  let mut n := 0
  let mut scale := 1
  for b in bs do
    let d ← match b with
      | .bits x => pure x.toNat
      | .poison => do pure ((← liftCM choose) % 256).toNat
      | f@(.frag ..) => do
        match ← liftCM (fragToBits loc f) with
        | .bits x => pure x.toNat
        | _ => pure 0
    n := n + d * scale
    scale := scale * 256
  pure (.bits (BitVec.ofNat 64 n))

/-- A word's `size` bytes in memory: a pointer's fragments when all eight are stored, otherwise
the low bytes of its bits. -/
def bytesOfWord (loc : Option Loc) (size : Nat) (w : Word) : LM (List Byte) := do
  match w, size with
  | .ptr p, 8 => pure (encodePtr (← get).core.space (some p))
  | w, _ => do
    let b ← toBits loc w
    pure ((digits size b.toNat).map fun d => .bits (BitVec.ofNat 8 d))

def loadWord (loc : Option Loc) (size : Nat) (addr : Word) : LM Word := do
  let (a, off) ← locate loc addr size
  wordOfBytes loc (readBytes ((← get).core.mem.getD a ∅) off size)

def storeWord (loc : Option Loc) (size : Nat) (addr v : Word) : LM Unit := do
  let bs ← bytesOfWord loc size v
  let (a, off) ← locate loc addr size
  modify fun m => { m with core := { m.core with
    mem := m.core.mem.insert a (writeBytes (m.core.mem.getD a ∅) off bs) } }

/-! ## The calling convention -/

/-- A value of type `t` from the word that carries it. -/
def valOfWord (loc : Option Loc) (t : Ty) (w : Word) : LM RVal := do
  match t with
  | .int n =>
    if n > 64 then stuckL loc s!"{t} is wider than a register"
    else pure (.int n (.bits ((← toBits loc w).setWidth n)))
  | .ptr => match w with
    | .ptr p => pure (.ptr (some p))
    | .bits b => pure (.ptr (some (.abs b.toNat [])))
  | .byte n =>
    if n > 64 then stuckL loc s!"{t} is wider than a register"
    else pure (.bytes ((← bytesOfWord loc 8 w).take (n / 8)))
  | _ => stuckL loc s!"{t} is not a value type"

/-- The word that carries a value: an integer zero-extended, a pointer as it is, bytes as a word
(`wordOfBytes`), and `poison` as an oracle choice. -/
def wordOfVal (loc : Option Loc) : RVal → LM Word
  | .int _ (.bits b) => pure (.bits (b.setWidth 64))
  | .int _ .poison => do pure (.bits (← chooseBits))
  | .ptr (some p) => pure (.ptr p)
  | .ptr none => do pure (.bits (← chooseBits))
  | .bytes bs => wordOfBytes loc bs

/-- The arguments of a call with parameter types `ps`: `x0`…`x7`, then 8-byte stack slots from
`sp`. -/
def argVals (loc : Option Loc) (ps : List Ty) : LM (List RVal) :=
  ps.zipIdx.mapM fun (t, i) => do
    let w ← if i < 8 then readReg loc (.x i)
      else loadWord loc 8 (← offsetWord loc (← get).sp (8 * (i - 8)))
    valOfWord loc t w

/-- Place a call's results: one or two in `x0` and `x1`, more in 8-byte slots at `x8`. -/
def setResults (loc : Option Loc) (rets : List Ty) (vs : List RVal) : LM Unit := do
  if rets.length ≤ 2 then
    for (v, i) in vs.zipIdx do writeReg (.x i) (← wordOfVal loc v)
  else
    let area ← readReg loc (.x 8)
    for (v, i) in vs.zipIdx do
      storeWord loc 8 (← offsetWord loc area (8 * i)) (← wordOfVal loc v)

/-- After a call outside LFIR: the caller-saved registers other than `keep`, and the flags, hold
oracle choices. -/
def clobber (keep : Nat) : LM Unit := do
  for i in List.range 19 do
    if i ≥ keep then writeReg (.x i) (.bits (← chooseBits))
  writeReg (.x 30) (.bits (← chooseBits))
  let f ← chooseBits
  modify fun m => { m with nzcv := f.setWidth 4 }

/-! ## Calls and returns -/

/-- What a function must preserve: `x19`…`x29`, then `sp`. -/
def calleeSaved : List Reg := (List.range 11).map (fun i => .x (19 + i)) ++ [.sp]

def savedWords : LM (List Word) := calleeSaved.mapM (readReg none)

/-- End the outermost call: its results, by its signature, and the leaks. -/
def finish (loc : Option Loc) (f : Func) : LM Unit := do
  let ws ← if f.rets.length ≤ 2 then (List.range f.rets.length).mapM fun i => readReg loc (.x i)
    else (List.range f.rets.length).mapM fun i => do
      loadWord loc 8 (← offsetWord loc (← get).resArea (8 * i : Nat))
  let vs ← (f.rets.zip ws).mapM fun (t, w) => valOfWord loc t w
  throw { outcome := .ret vs, loc, leaks := leaks (← get).core }

/-- Start running `f`: push a frame for its code, or, for a `func.ret` of its parameters, place
those values as results at once. -/
def enter (loc : Option Loc) (f : Func) : LM Unit := do
  match f.body.ops with
  | [.mk .a64Code _ _ (entry :: rest) _] =>
    let saved ← savedWords
    modify fun m => { m with
      frames := { func := f, blocks := entry :: rest, ops := entry.ops, saved } :: m.frames }
  | [.mk .ret _ args _ rloc] =>
    let vs ← argVals loc (f.params.map (·.ty))
    let env := Env.bindAll {} f.params vs
    let outs ← args.mapM fun
      | .var n => match env[n]? with
        | some v => pure v
        | none => stuckL rloc s!"%{n} is not defined"
      | .hole n _ => halt (.hole n) rloc
    setResults rloc f.rets outs
  | _ => stuckL loc s!"@{f.name}'s body must be aarch64.code or func.ret"

/-- Call an external function: one event, then its results where the convention puts them. -/
def callExt (loc : Option Loc) (x : Extern) : LM Unit := do
  let vs ← argVals loc x.params
  let e ← liftCM (callExtern loc x vs)
  modify fun m => { m with core := { m.core with trace := m.core.trace ++ [e] } }
  match e.results with
  | none => modify fun m => { m with hung := true }
  | some rs =>
    setResults loc x.rets rs
    clobber (if x.rets.length ≤ 2 then x.rets.length else 0)

def callNamed (loc : Option Loc) (name : String) : LM Unit := do
  let c := (← get).core
  match c.funcs[name]?, c.externs[name]? with
  | some f, _ =>
    writeReg (.x 30) (.bits 0)
    enter loc f
  | none, some x => callExt loc x
  | none, none => stuckL loc s!"no function @{name}"

/-- The function a word points to the start of. -/
def funcAt (loc : Option Loc) (w : Word) : LM String := do
  let c := (← get).core
  let byAlloc (a : Nat) (off : Int) : LM String := do
    match c.allocs[a]?.map Alloc.kind with
    | some (AllocKind.func name) =>
      if off == 0 then pure name else ub .badCall loc s!"offset {off} is not the start of @{name}"
    | _ => ub .badCall loc s!"#{a} is not a function"
  match w with
  | .ptr (.rel a _ off) => byAlloc a off
  | w =>
    let addr := (← toBits loc w).toNat
    let hit := c.allocs.toList.find? fun (_, al) => al.kind matches .func _ && al.base == some addr
    match hit with
    | some (a, _) => byAlloc a 0
    | none => ub .badCall loc s!"address {addr} is not a function"

/-- Return from the running function, which must have kept `x19`…`x29` and `sp`. -/
def ret (loc : Option Loc) : LM Unit := do
  let f ← frame loc
  let now ← savedWords
  for (r, (a, b)) in calleeSaved.zip (f.saved.zip now) do
    unless a == b do stuckL loc s!"@{f.func.name} doesn't preserve {r}"
  modify fun m => { m with frames := m.frames.drop 1 }
  if (← get).frames.isEmpty then finish loc f.func

def jump (loc : Option Loc) (label : String) : LM Unit := do
  let f ← frame loc
  match f.blocks.find? (·.label == some label) with
  | some b => modify fun m => { m with frames := match m.frames with
    | f :: fs => { f with ops := b.ops } :: fs
    | [] => [] }
  | none => stuckL loc s!"no block ^{label}"

/-! ## Instructions -/

def setFlags : Option (BitVec 4) → LM Unit
  | some f => modify fun m => { m with nzcv := f }
  | none => pure ()

/-- `add` and `sub` at 64 bits keep a pointer operand's provenance. -/
def addSub (loc : Option Loc) (sub : Bool) (a b : Word) : LM (Option Word) := do
  match a, b, sub with
  | .ptr p, .bits k, _ => pure (some (← offsetWord loc (.ptr p) (if sub then -k.toInt else k.toInt)))
  | .bits k, .ptr p, false => pure (some (← offsetWord loc (.ptr p) k.toInt))
  | _, _, _ => pure none

/-- A pointer to a function, made the first time its address is taken (as `func.addr`). -/
def funcPtr (loc : Option Loc) (name : String) : LM Ptr := do
  let c := (← get).core
  if let some p := c.addrs[name]? then return p
  let p ← liftCM (newAlloc loc 0 1 (.func name))
  modify fun m => { m with core := { m.core with addrs := m.core.addrs.insert name p } }
  pure p

/-- The pointer `aarch64.bl.free` frees: a pointer as it is; an integer, the allocation that
starts at that address (or holds it). -/
def ptrOfWord (w : Word) : LM Ptr := do
  match w with
  | .ptr p => pure p
  | .bits b =>
    let n := b.toNat
    if n == 0 then return .null
    let c := (← get).core
    let starts := c.allocs.toList.find? fun (_, al) => al.live && al.base == some n
    let holds := c.allocs.toList.find? fun (_, al) =>
      match al.base with
      | some base => al.live && base ≤ n && n < base + al.size
      | none => false
    match starts <|> holds with
    | some (a, al) => pure (.rel a 0 (n - al.base.getD 0))
    | none => pure (.abs n [])

def exec (op : Op) : LM Unit := do
  let loc := op.loc
  match op.kind with
  | .a64Alu o sf d n m =>
    let (a, b) := (← readReg loc n, ← readReg loc m)
    let kept ← match sf, o with
      | .x, .add => addSub loc false a b
      | .x, .sub => addSub loc true a b
      | _, _ => pure none
    match kept with
    | some w => writeReg d w
    | none =>
      let (r, f) := alu o sf (← toBits loc a) (← toBits loc b)
      writeReg d (.bits r)
      setFlags f
  | .a64AluImm o sf d n imm =>
    let a ← readReg loc n
    let kept ← match sf, o with
      | .x, .add => addSub loc false a (.bits (BitVec.ofInt 64 imm))
      | .x, .sub => addSub loc true a (.bits (BitVec.ofInt 64 imm))
      | _, _ => pure none
    match kept with
    | some w => writeReg d w
    | none =>
      let (r, f) := aluImm o sf (← toBits loc a) (BitVec.ofInt 64 imm)
      writeReg d (.bits r)
      setFlags f
  | .a64ShiftImm o sf d n k =>
    unless k < sf.bits do stuckL loc s!"shift amount {k} is not below {sf.bits}"
    writeReg d (.bits (shiftImm o sf (← readBits loc n) k))
  | .a64Ext signed sf d n width =>
    unless 1 ≤ width && width ≤ sf.bits do stuckL loc s!"width {width} is not in 1..{sf.bits}"
    writeReg d (.bits (ext signed sf (← readBits loc n) width))
  | .a64Mov sf d n =>
    match sf with
    | .x => writeReg d (← readReg loc n)
    | .w => writeReg d (.bits ((← readBits loc n).setWidth 32 |>.setWidth 64))
  | .a64MovWide o sf d imm hw =>
    unless imm < 65536 && hw % 16 == 0 && hw < sf.bits do stuckL loc "malformed move"
    let old ← match o with
      | .movk => readBits loc d
      | _ => pure 0
    writeReg d (.bits (movWide o sf old imm hw))
  | .a64Csel o c sf d n m =>
    if conditionHolds c (← get).nzcv then
      match sf with
      | .x => writeReg d (← readReg loc n)
      | .w => writeReg d (.bits ((← readBits loc n).setWidth 32 |>.setWidth 64))
    else
      match o, sf with
      | .csel, .x => writeReg d (← readReg loc m)
      | _, _ => writeReg d (.bits (cselElse o sf (← readBits loc m)))
  | .a64Ldr size d base off =>
    let addr ← offsetWord loc (← readReg loc base) off
    writeReg d (← loadWord loc size.bytes addr)
  | .a64Str size s base off =>
    let addr ← offsetWord loc (← readReg loc base) off
    storeWord loc size.bytes addr (← readReg loc s)
  | .a64Adrl d g =>
    match (← get).core.addrs[g]? with
    | some p => writeReg d (.ptr p)
    | none => stuckL loc s!"no global @{g}"
  | .a64AdrlFunc d f => writeReg d (.ptr (← funcPtr loc f))
  | .a64B dest => jump loc dest.label
  | .a64BCond c t f => jump loc (if conditionHolds c (← get).nzcv then t.label else f.label)
  | .a64Ret => ret loc
  | .a64Trap r => halt (.trap r) loc
  | .a64Bl callee => callNamed loc callee
  | .a64Blr _ n => callNamed loc (← funcAt loc (← readReg loc n))
  | .a64BlAlloc family align =>
    let size ← readBits loc (.x 0)
    if (← liftCM choose) != 0 then writeReg (.x 0) (.bits 0)
    else writeReg (.x 0) (.ptr (← liftCM (newAlloc loc size.toNat align (.heap family))))
    clobber 1
  | .a64BlFree family =>
    let p ← ptrOfWord (← readReg loc (.x 0))
    liftCM (freePtr loc family (some p))
    clobber 0
  | k => stuckL loc s!"{k.name} can't run in LFIR"

/-- One step: the next instruction of the running function. -/
def step : LM Unit := do
  let m ← get
  if m.hung then return
  match m.frames with
  | f :: fs =>
    match f.ops with
    | op :: rest =>
      set { m with frames := { f with ops := rest } :: fs }
      exec op
    | [] => stuckL none "a block ended without a terminator"
  | [] => stuckL none "no running function"

/-- The machine at the start of a call to `f` from outside: the stack, then the arguments where
the convention puts them (results area, stack slots, registers), then `f` entered. -/
def start (f : Func) (args : List RVal) : LM Unit := do
  let p ← liftCM (newAlloc none stackSize 16 .stack)
  let top ← offsetWord none (.ptr p) stackSize
  modify fun m => { m with sp := top }
  let down (n : Nat) : LM Unit := do
    let sp ← offsetWord none (← get).sp (-(((n + 15) / 16 * 16 : Nat) : Int))
    modify fun m => { m with sp }
  if f.rets.length > 2 then
    down (8 * f.rets.length)
    modify fun m => { m with resArea := m.sp }
    writeReg (.x 8) (← get).sp
  if args.length > 8 then
    down (8 * (args.length - 8))
    for (v, i) in (args.drop 8).zipIdx do
      storeWord none 8 (← offsetWord none (← get).sp (8 * i)) (← wordOfVal none v)
  for (v, i) in (args.take 8).zipIdx do writeReg (.x i) (← wordOfVal none v)
  enter none f
  if (← get).frames.isEmpty then finish none f

/-- Run up to `limit` steps and describe the outcome in one line, as `fir-ref run` does for the
other layers: the events, then how the run ended. -/
partial def drive (m : LMachine) (steps limit : Nat) : String :=
  if steps ≥ limit then renderRun m.core.trace s!"out of fuel after {limit} steps"
  else
    match step.run m with
    | .ok ((), m') => drive m' (steps + 1) limit
    | .error h => renderRun m.core.trace (renderHalt h)

/-- Run `f` with `args` (for the oracle that answers `0` and the world that answers zeros). -/
def run (mod : Module) (f : Func) (args : List RVal) (fuel : Nat) : String :=
  let m : LMachine := { core := Core.initial (fun _ => 0) World.zero mod }
  match (start f args).run m with
  | .ok ((), m) => drive m 0 fuel
  | .error h => renderHalt h

/-- Run `n` steps; an `error` is a halted run. -/
def runSteps : Nat → LMachine → Except Halt LMachine
  | 0, m => .ok m
  | n + 1, m =>
    match step.run m with
    | .ok ((), m') => runSteps n m'
    | .error h => .error h

end Fir.AArch64
