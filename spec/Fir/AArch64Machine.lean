import Fir.AArch64
import Fir.AArch64Abi
import Fir.Interp
import Fir.Layout
import Fir.Print

/-!
# The AArch64 LFIR machine

How `fir-ref run` runs an LFIR module for AArch64 (`layer lfir aarch64`). It is a register
machine over FIR's core: the memory, allocations, events, and oracle of `Fir.Interp` stay as they
are, and the machine adds the general-purpose registers `x0`…`x30`, `sp`, the FP/SIMD registers
`d0`…`d31` (the low 64 bits of `V0`…`V31`, all scalar code reads; a write of `s` or `d` zeroes the
rest), the flags NZCV, and a stack of call frames, each with its own virtual registers of both
classes. The instructions' bit-level meaning is
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
* **Registers have classes**: an instruction that names a register of the wrong class (an FP
  register in `add`, a general-purpose one in `fadd`) is stuck; `fmov`, `ldr`, and `str` take
  either for the register they move.
* **Calls** follow AAPCS64 as `Fir.AArch64Abi` lays it out (decisions: Calling convention, C
  ABI for aggregates): integer and pointer arguments in `x0`…`x7` and float arguments in
  `d0`…`d7`, counted separately, then 8-byte stack slots from `sp` in order; a struct or array
  as its HFA members in FP registers, its bytes in one or two `x` registers, or on the stack, or
  a pointer to a copy (`argLocs`); variadic arguments as fixed ones on Linux (decision: Varargs;
  `blr` names the call's argument types, which an external callee's event reads); one or two
  scalar results in `d0`, `d1` when all are floats of one format, otherwise in `x0`, `x1` (a
  float as its bits), more in 8-byte slots at the address the caller passes in `x8`, and a
  composite result where it would be passed first, or at `x8` (`resRegs`). A narrow integer or
  an `f32` travels in the low bits of its register; a composite's bytes in registers are read
  and written as `ldr` and `str` move them (`wordOfBytes`, `bytesOfWord`), so a pointer in a
  whole word keeps its provenance. `bl` enters an LFIR function, which must leave `x19`…`x29`, `sp`, and `d8`…`d15` as
  it found them, or calls an external function: one event, its results placed as above, and the
  caller-saved registers (`x0`…`x18`, `x30`, `d0`…`d7`, `d16`…`d31`) and flags then hold oracle
  choices. `ret` returns to the frame below,
  whatever `x30` holds: return addresses aren't modeled.
* **Runtime calls**: `aarch64.bl.alloc` and `aarch64.bl.free` allocate and free like `mem.alloc`
  and `mem.free`, without an event; `aarch64.trap.R` traps with reason `R`.
* **Exceptions** (decision: Exceptions at run time): the machine has one exception slot, the
  pending exception or none (`__fir_exn` in native code), outside FIR's memory, which no program
  can reach. `aarch64.exn.set` sets it, `aarch64.exn.take` takes it, and `aarch64.b.exn` branches
  on it. A throwing function sets it and returns; its callers check it after each call. The
  outermost call returning with an exception pending ends the run with `threw`.

A function whose body is a plain `func.ret` of its parameters also runs: it returns those
values where the calling convention puts results.
-/

namespace Fir.AArch64

/-- One running function: its blocks, the rest of the current block, its virtual registers (`vN`
and `fvN`), and what the callee-saved registers held on entry. -/
structure LFrame where
  func : Func
  blocks : List Region
  ops : List Op
  vregs : Std.HashMap Nat Word := {}
  fvregs : Std.HashMap Nat (BitVec 64) := {}
  saved : List Word

structure LMachine where
  core : Core
  /-- `x0`…`x30`. -/
  regs : Array Word := Array.replicate 31 (.bits 0)
  sp : Word := .bits 0
  /-- `d0`…`d31`: the low 64 bits of the FP/SIMD registers. -/
  fregs : Array (BitVec 64) := Array.replicate 32 0
  nzcv : BitVec 4 := 0
  frames : List LFrame := []
  /-- Where the outermost call's results go when it has more than two. -/
  resArea : Word := .bits 0
  /-- An external call didn't return: the machine runs on without doing anything. -/
  hung : Bool := false
  /-- The pending exception, if any. -/
  exn : Option Word := none

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

/-- A general-purpose register. -/
def readReg (loc : Option Loc) : Reg → LM Word
  | .xzr => pure (.bits 0)
  | .sp => do pure (← get).sp
  | .x n => do pure ((← get).regs.getD n (.bits 0))
  | .v n => do
    match (← frame loc).vregs[n]? with
    | some w => pure w
    | none => stuckL loc s!"v{n} is read before it is written"
  | r => stuckL loc s!"{r} is not a general-purpose register"

/-- Write a general-purpose register (`exec` checks the class first). -/
def writeReg (r : Reg) (w : Word) : LM Unit :=
  modify fun m => match r with
    | .xzr => m
    | .sp => { m with sp := w }
    | .x n => { m with regs := m.regs.set! n w }
    | .v n => { m with frames := match m.frames with
      | f :: fs => { f with vregs := f.vregs.insert n w } :: fs
      | [] => [] }
    | .d _ | .fv _ => m

/-- An FP register's 64 bits. -/
def readF (loc : Option Loc) : Reg → LM (BitVec 64)
  | .d n => do pure ((← get).fregs.getD n 0)
  | .fv n => do
    match (← frame loc).fvregs[n]? with
    | some b => pure b
    | none => stuckL loc s!"fv{n} is read before it is written"
  | r => stuckL loc s!"{r} is not an FP register"

def writeF (r : Reg) (b : BitVec 64) : LM Unit :=
  modify fun m => match r with
    | .d n => { m with fregs := m.fregs.set! n b }
    | .fv n => { m with frames := match m.frames with
      | f :: fs => { f with fvregs := f.fvregs.insert n b } :: fs
      | [] => [] }
    | _ => m

/-- An FP register's low bits, as a float of the format. -/
def readFs (loc : Option Loc) (fs : FSize) (r : Reg) : LM (Float.Bits fs.fty.fmt) := do
  pure ((← readF loc r).setWidth _)

/-- Write a float of the format, zeroing the register's other bits. -/
def writeFs (fs : FSize) (r : Reg) (b : Float.Bits fs.fty.fmt) : LM Unit := writeF r (b.setWidth 64)

/-- A word's bits: a pointer's address, given an address if it has none. -/
def toBits (loc : Option Loc) : Word → LM (BitVec 64)
  | .bits b => pure b
  | .ptr p => do pure (BitVec.ofNat 64 (← liftCM (ptrAddr loc p)))

def readBits (loc : Option Loc) (r : Reg) : LM (BitVec 64) := do toBits loc (← readReg loc r)

/-- A register of either class, as a word (an FP register's bits). -/
def readAny (loc : Option Loc) (r : Reg) : LM Word :=
  if r.isFp then do pure (.bits (← readF loc r)) else readReg loc r

/-- Write a register of either class (an FP register gets the word's bits). -/
def writeAny (loc : Option Loc) (r : Reg) (w : Word) : LM Unit :=
  if r.isFp then do writeF r (← toBits loc w) else writeReg r w

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
      | .poison | .va .. => do pure ((← liftCM choose) % 256).toNat
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
  | .float f => pure (.float f (.bits ((← toBits loc w).setWidth f.width)))
  | _ => stuckL loc s!"{t} is not a value type"

/-- The word that carries a value: an integer or a float's bits zero-extended, a pointer as it is,
bytes as a word (`wordOfBytes`), and `poison` as an oracle choice. -/
def wordOfVal (loc : Option Loc) : RVal → LM Word
  | .int _ (.bits b) => pure (.bits (b.setWidth 64))
  | .int _ .poison => do pure (.bits (← chooseBits))
  | .ptr (some p) => pure (.ptr p)
  | .ptr none => do pure (.bits (← chooseBits))
  | .bytes bs => wordOfBytes loc bs
  | .agg _ => stuckL loc "an aggregate is not a register value"
  | .float _ (.bits b) => pure (.bits (b.setWidth 64))
  | .float _ .poison => do pure (.bits (← chooseBits))

/-- A word in a stack slot `off` bytes above `sp`. -/
def slotWord (loc : Option Loc) (off : Nat) : LM Word := do
  loadWord loc 8 (← offsetWord loc (← get).sp off)

def space : LM SpaceCfg := do pure (← get).core.space

/-- `n` bytes of memory at `w`. -/
def loadBytes (loc : Option Loc) (w : Word) (n : Nat) : LM (List Byte) := do
  let (a, off) ← locate loc w n
  pure (readBytes ((← get).core.mem.getD a ∅) off n)

/-- Write bytes to memory at `w`. -/
def storeBytes (loc : Option Loc) (w : Word) (bs : List Byte) : LM Unit := do
  let (a, off) ← locate loc w bs.length
  modify fun m => { m with core := { m.core with
    mem := m.core.mem.insert a (writeBytes (m.core.mem.getD a ∅) off bs) } }

/-- A composite of type `t` from its bytes: each leaf as a load of its type reads it. -/
def valOfBytes (loc : Option Loc) (t : Ty) (bs : List Byte) : LM RVal := do
  let sp ← space
  let ls ← (t.leaves sp).mapM fun (o, l) => liftCM (decodeAs loc l ((bs.drop o).take (l.size sp)))
  match t.build ls with
  | some (v, []) => pure v
  | _ => stuckL loc s!"{t} has no value of its leaves"

/-- A composite value's bytes (`compositeBytes`): its leaves', `poison` in the padding. -/
def bytesOfVal (sp : SpaceCfg) (t : Ty) (v : RVal) : List Byte :=
  compositeBytes sp t (v.pieces sp t)

/-- The bytes a composite of kind `k` has in registers `rs`: eight per `x` register, a member's
per FP register. -/
def regBytes (loc : Option Loc) (k : PassKind) (rs : List Reg) : LM (List Byte) := do
  let mut out := []
  for r in rs do
    match k with
    | .hfa f _ =>
      let b ← readF loc r
      out := out ++ (digits f.bytes b.toNat).map fun d => .bits (BitVec.ofNat 8 d)
    | _ => out := out ++ (← bytesOfWord loc 8 (← readReg loc r))
  pure out

/-- Put a composite of kind `k`'s bytes in registers `rs`, a piece each (`pieces`). -/
def placeBytes (loc : Option Loc) (k : PassKind) (rs : List Reg) (bs : List Byte) : LM Unit := do
  for (pc, r) in (pieces k bs).zip rs do
    writeAny loc r (← wordOfBytes loc pc)

/-- An argument of type `t` from where `argLocs` put it. -/
def argVal (loc : Option Loc) (t : Ty) : ArgLoc → LM RVal
  | .reg r => do valOfWord loc t (← readAny loc r)
  | .stack off => do valOfWord loc t (← slotWord loc off)
  | .regs rs => do
    let sp ← space
    valOfBytes loc t ((← regBytes loc (passKind sp t) rs).take (t.size sp))
  | .mem off => do
    valOfBytes loc t (← loadBytes loc (← offsetWord loc (← get).sp off) (t.size (← space)))
  | .ref l => do
    let p ← match l with
      | .inl r => readReg loc r
      | .inr off => slotWord loc off
    valOfBytes loc t (← loadBytes loc p (t.size (← space)))
  | .none => valOfBytes loc t []

/-- The arguments of a call with parameter types `ps`, from where `argLocs` puts them. -/
def argVals (loc : Option Loc) (ps : List Ty) : LM (List RVal) := do
  (ps.zip (argLocs (← space) ps)).mapM fun (t, l) => argVal loc t l

/-- Place a call's results where `resRegs` says: in registers (a composite's pieces), or at
`x8` (a composite's bytes, or 8-byte slots). -/
def setResults (loc : Option Loc) (rets : List Ty) (vs : List RVal) : LM Unit := do
  let sp ← space
  match rets, vs with
  | [t], [v] =>
    if t.isComposite then
      let bs := bytesOfVal sp t v
      match resRegs sp rets with
      | some rs => placeBytes loc (passKind sp t) rs bs
      | none => storeBytes loc (← readReg loc (.x 8)) bs
    else scalars sp
  | _, _ => scalars sp
where
  scalars (sp : SpaceCfg) : LM Unit := do
    match resRegs sp rets with
    | some rs => for (v, r) in vs.zip rs do writeAny loc r (← wordOfVal loc v)
    | none =>
      let area ← readReg loc (.x 8)
      for (v, i) in vs.zipIdx do
        storeWord loc 8 (← offsetWord loc area (8 * i)) (← wordOfVal loc v)

/-- The FP registers a call may change: `d0`…`d7` and `d16`…`d31` (of `d8`…`d15`, only the high
64 bits, which the machine doesn't hold). -/
def fpCallerSaved : List Nat := List.range 8 ++ (List.range 16).map (· + 16)

/-- After a call outside LFIR: the caller-saved registers other than `keep`, and the flags, hold
oracle choices. -/
def clobber (keep : List Reg) : LM Unit := do
  for i in List.range 19 do
    unless keep.contains (.x i) do writeReg (.x i) (.bits (← chooseBits))
  writeReg (.x 30) (.bits (← chooseBits))
  for i in fpCallerSaved do
    unless keep.contains (.d i) do writeF (.d i) (← chooseBits)
  let f ← chooseBits
  modify fun m => { m with nzcv := f.setWidth 4 }

/-! ## Calls and returns -/

/-- What a function must preserve: `x19`…`x29`, `sp`, then `d8`…`d15` (their low 64 bits). -/
def calleeSaved : List Reg :=
  (List.range 11).map (fun i => .x (19 + i)) ++ [.sp] ++ (List.range 8).map (fun i => .d (8 + i))

def savedWords : LM (List Word) := calleeSaved.mapM (readAny none)

/-- End the outermost call: its results, by its signature (or the exception it threw), and the
leaks. -/
def finish (loc : Option Loc) (f : Func) : LM Unit := do
  if let some w := (← get).exn then
    throw { outcome := .threw (← valOfWord loc .ptr w), loc, leaks := leaks (← get).core }
  let sp ← space
  let vs ← match f.rets with
    | [t] =>
      if t.isComposite then do
        match resRegs sp f.rets with
        | some rs => pure [← argVal loc t (.regs rs)]
        | none => pure [← valOfBytes loc t (← loadBytes loc (← get).resArea (t.size sp))]
      else scalars sp
    | _ => scalars sp
  throw { outcome := .ret vs, loc, leaks := leaks (← get).core }
where
  scalars (sp : SpaceCfg) : LM (List RVal) := do
    let ws ← match resRegs sp f.rets with
      | some rs => rs.mapM (readAny loc)
      | none => (List.range f.rets.length).mapM fun i => do
        loadWord loc 8 (← offsetWord loc (← get).resArea (8 * i : Nat))
    (f.rets.zip ws).mapM fun (t, w) => valOfWord loc t w

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

/-- Call an external function with arguments of types `ps` (its parameters', or, through `blr`,
the call's, variadic arguments included): one event, then its results where the convention puts
them. -/
def callExt (loc : Option Loc) (x : Extern) (ps : List Ty) : LM Unit := do
  let vs ← argVals loc ps
  let e ← liftCM (callExtern loc x vs)
  modify fun m => { m with core := { m.core with trace := m.core.trace ++ [e] } }
  match e.results with
  | none => modify fun m => { m with hung := true }
  | some rs =>
    setResults loc x.rets rs
    clobber ((resRegs (← space) x.rets).getD [])

/-- Call a function by name. An external one reads its arguments by `site`, the call's argument
types, if given (`blr`: a variadic callee's variadic arguments are in them), else by its
parameters. -/
def callNamed (loc : Option Loc) (name : String) (site : Option (List Ty) := none) : LM Unit := do
  let c := (← get).core
  match c.funcs[name]?, c.externs[name]? with
  | some f, _ =>
    writeReg (.x 30) (.bits 0)
    enter loc f
  | none, some x => callExt loc x (site.getD x.params)
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

/-- The registers an instruction names that must be of one class: general-purpose (`false`) or
FP (`true`). `fmov`, `ldr`, and `str` take either class for the register they move. -/
def regClasses : OpKind → List (Reg × Bool)
  | .a64Alu _ _ d n m | .a64Csel _ _ _ d n m => [(d, false), (n, false), (m, false)]
  | .a64AluImm _ _ d n _ | .a64ShiftImm _ _ d n _ | .a64Ext _ _ d n _ | .a64Mov _ d n =>
    [(d, false), (n, false)]
  | .a64MovWide _ _ d _ _ | .a64Adrl d _ | .a64AdrlFunc d _ | .a64ExnTake d => [(d, false)]
  | .a64Ldr _ _ base _ | .a64Str _ _ base _ | .a64Blr _ base | .a64ExnSet base => [(base, false)]
  | .a64Falu _ _ d n m | .a64Fmadd _ d n m | .a64Fcsel _ _ d n m => [(d, true), (n, true), (m, true)]
  | .a64Funary op _ d n => if op = .fmov then [] else [(d, true), (n, true)]
  | .a64FmovImm _ d _ => [(d, true)]
  | .a64Fcmp _ n m => [(n, true), (m, true)]
  | .a64Fcvt _ _ d n => [(d, true), (n, true)]
  | .a64Cvtf _ _ _ d n => [(d, true), (n, false)]
  | .a64Fcvtz _ _ _ d n => [(d, false), (n, true)]
  | _ => []

/-- `fmov` between registers of any classes but two general-purpose ones: the low bits of the
format, zero-extended. -/
def fmov (loc : Option Loc) (fs : FSize) (d n : Reg) : LM Unit := do
  let low (b : BitVec 64) : BitVec 64 := (b.setWidth fs.bits).setWidth 64
  match d.isFp, n.isFp with
  | true, true => writeF d (low (← readF loc n))
  | true, false => writeF d (low (← readBits loc n))
  | false, true => writeReg d (.bits (low (← readF loc n)))
  | false, false => stuckL loc "fmov needs an FP register"

def exec (op : Op) : LM Unit := do
  let loc := op.loc
  for (r, fp) in regClasses op.kind do
    unless r.isFp == fp do
      stuckL loc s!"{r} is not {if fp then "an FP" else "a general-purpose"} register"
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
    writeAny loc d (← loadWord loc size.bytes addr)
  | .a64Str size s base off =>
    let addr ← offsetWord loc (← readReg loc base) off
    storeWord loc size.bytes addr (← readAny loc s)
  | .a64Falu o fs d n m => writeFs fs d (fpAlu o (← readFs loc fs n) (← readFs loc fs m))
  | .a64Funary o fs d n =>
    match o with
    | .fmov => fmov loc fs d n
    | .fabs => writeFs fs d (Float.abs (← readFs loc fs n))
    | .fneg => writeFs fs d (Float.neg (← readFs loc fs n))
    | .fsqrt => writeFs fs d (fpSqrt (← readFs loc fs n))
  | .a64Fmadd fs d n m =>
    writeFs fs d (fpMulAdd (← readFs loc fs d) (← readFs loc fs n) (← readFs loc fs m))
  | .a64FmovImm fs d imm =>
    unless imm < 256 do stuckL loc s!"{imm} is not an 8-bit immediate"
    writeFs fs d (vfpExpandImm _ imm)
  | .a64Fcmp fs n m =>
    let f := fpCompare (← readFs loc fs n) (← readFs loc fs m)
    modify fun st => { st with nzcv := f }
  | .a64Fcsel c fs d n m =>
    let r := if conditionHolds c (← get).nzcv then n else m
    writeFs fs d (← readFs loc fs r)
  | .a64Fcvt dst src d n =>
    if dst = src then stuckL loc "fcvt converts between s and d"
    else writeFs dst d (fpConvert _ (← readFs loc src n))
  | .a64Cvtf signed fs sf d n =>
    writeFs fs d (intToFp _ signed ((← readBits loc n).setWidth sf.bits))
  | .a64Fcvtz signed sf fs d n =>
    writeReg d (.bits ((fpToInt signed sf.bits (← readFs loc fs n)).setWidth 64))
  | .a64Adrl d g =>
    match (← get).core.addrs[g]? with
    | some p => writeReg d (.ptr p)
    | none => stuckL loc s!"no global @{g}"
  | .a64AdrlFunc d f => writeReg d (.ptr (← funcPtr loc f))
  | .a64B dest => jump loc dest.label
  | .a64BCond c t f => jump loc (if conditionHolds c (← get).nzcv then t.label else f.label)
  | .a64Ret => ret loc
  | .a64ExnSet n => do
    let w ← readReg loc n
    modify fun m => { m with exn := some w }
  | .a64ExnTake d =>
    match (← get).exn with
    | some w =>
      modify fun m => { m with exn := none }
      writeReg d w
    | none => stuckL loc "no exception is pending"
  | .a64BExn t f => jump loc (if (← get).exn.isSome then t.label else f.label)
  | .a64Trap r => halt (.trap r) loc
  | .a64Bl callee => callNamed loc callee
  | .a64Blr sig n =>
    let site := match sig with
      | .func ps _ _ => some ps
      | _ => none
    callNamed loc (← funcAt loc (← readReg loc n)) site
  | .a64BlAlloc family align =>
    let size ← readBits loc (.x 0)
    if (← liftCM choose) != 0 then writeReg (.x 0) (.bits 0)
    else writeReg (.x 0) (.ptr (← liftCM (newAlloc loc size.toNat align (.heap family))))
    clobber [.x 0]
  | .a64BlFree family =>
    let p ← ptrOfWord (← readReg loc (.x 0))
    liftCM (freePtr loc family (some p))
    clobber []
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
  let sp ← space
  if (resRegs sp f.rets).isNone then
    down (match f.rets with
      | [t] => if t.isComposite then t.size sp else 8
      | rs => 8 * rs.length)
    modify fun m => { m with resArea := m.sp }
    writeReg (.x 8) (← get).sp
  -- A variadic function's variadic arguments go where fixed ones of their types would.
  let tys := (f.params.map (·.ty)) ++ ((args.drop f.params.length).map RVal.argTy)
  -- Copies of the composites passed by reference.
  let mut refs : List Word := []
  for (v, t) in args.zip tys do
    if passKind sp t == .ref then
      down (t.size sp)
      storeBytes none (← get).sp (bytesOfVal sp t v)
      refs := refs ++ [(← get).sp]
    else refs := refs ++ [.bits 0]
  let locs := argLocs sp tys
  let n := argStack sp tys
  if n > 0 then down n
  for ((v, t), (l, p)) in (args.zip tys).zip (locs.zip refs) do
    let slot (off : Nat) : LM Word := do offsetWord none (← get).sp off
    match l with
    | .reg r => writeAny none r (← wordOfVal none v)
    | .stack off => storeWord none 8 (← slot off) (← wordOfVal none v)
    | .regs rs => placeBytes none (passKind sp t) rs (bytesOfVal sp t v)
    | .mem off => storeBytes none (← slot off) (bytesOfVal sp t v)
    | .ref (.inl r) => writeReg r p
    | .ref (.inr off) => storeWord none 8 (← slot off) p
    | .none => pure ()
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
  let m : LMachine := { core := Core.initial Oracle.zero World.zero mod }
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
