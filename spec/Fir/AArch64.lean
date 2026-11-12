import Fir.AArch64Syntax

/-!
# AArch64 instruction semantics

What each `aarch64.*` instruction computes from the bits it reads, written by hand this round in
the shape of Arm's ASL pseudocode (`AddWithCarry`, `ConditionHolds`, the `sf` size), so that a
later import of the ASL can replace these definitions one by one (decision: First target).

Everything here is on bit vectors: registers as `BitVec 64` and flags as NZCV in a `BitVec 4`
(N is bit 3). What FIR adds on top, registers that hold pointers with their provenance, is the
machine's business (`Fir.AArch64Machine`): it turns a pointer into its address before calling
these functions, except for the few instructions that keep provenance (adding or subtracting an
integer, moves, selects, and 64-bit loads and stores).

A 32-bit (`.w`) operation reads the low 32 bits of its sources and zero-extends its result, as
writing a `W` register does.
-/

namespace Fir.AArch64

open BitVec

/-- NZCV from its four bits. -/
def nzcv (n z c v : Bool) : BitVec 4 :=
  (BitVec.ofBool n ++ BitVec.ofBool z ++ BitVec.ofBool c ++ BitVec.ofBool v)

def flagN (f : BitVec 4) : Bool := f.getLsbD 3
def flagZ (f : BitVec 4) : Bool := f.getLsbD 2
def flagC (f : BitVec 4) : Bool := f.getLsbD 1
def flagV (f : BitVec 4) : Bool := f.getLsbD 0

/-- ASL `AddWithCarry`: `x + y + carry` and the flags it sets. -/
def addWithCarry (x y : BitVec n) (carry : Bool) : BitVec n × BitVec 4 :=
  let c : Nat := if carry then 1 else 0
  let usum := x.toNat + y.toNat + c
  let ssum := x.toInt + y.toInt + c
  let r := BitVec.ofNat n usum
  (r, nzcv (r.msb) (r == 0) (r.toNat != usum) (r.toInt != ssum))

/-- The flags a logical operation (`ands`) sets. -/
def logicFlags (r : BitVec n) : BitVec 4 := nzcv r.msb (r == 0) false false

/-- ASL `ConditionHolds`. -/
def conditionHolds (c : Cond) (f : BitVec 4) : Bool :=
  match c with
  | .eq => flagZ f
  | .ne => !flagZ f
  | .hs => flagC f
  | .lo => !flagC f
  | .mi => flagN f
  | .pl => !flagN f
  | .vs => flagV f
  | .vc => !flagV f
  | .hi => flagC f && !flagZ f
  | .ls => !(flagC f && !flagZ f)
  | .ge => flagN f == flagV f
  | .lt => flagN f != flagV f
  | .gt => !flagZ f && flagN f == flagV f
  | .le => !(!flagZ f && flagN f == flagV f)

/-- Three-register data processing on `n`-bit operands: the result, and the flags if the
operation sets them. Shifts by a register take the amount modulo `n`; division by zero gives 0,
and signed `MIN / -1` gives `MIN` (ASL's `RoundTowardsZero` of the exact quotient, truncated). -/
def aluN (op : AluOp) (x y : BitVec n) : BitVec n × Option (BitVec 4) :=
  match op with
  | .add => (x + y, none)
  | .adds => let (r, f) := addWithCarry x y false; (r, some f)
  | .sub => (x - y, none)
  | .subs => let (r, f) := addWithCarry x (~~~y) true; (r, some f)
  | .and => (x &&& y, none)
  | .ands => (x &&& y, some (logicFlags (x &&& y)))
  | .orr => (x ||| y, none)
  | .eor => (x ^^^ y, none)
  | .bic => (x &&& ~~~y, none)
  | .lsl => (x <<< (y.toNat % n), none)
  | .lsr => (x >>> (y.toNat % n), none)
  | .asr => (x.sshiftRight (y.toNat % n), none)
  | .mul => (x * y, none)
  | .sdiv => (x.sdiv y, none)
  | .udiv => (x / y, none)
  | .smulh => (((x.signExtend (2 * n) * y.signExtend (2 * n)) >>> n).setWidth n, none)
  | .umulh => (((x.setWidth (2 * n) * y.setWidth (2 * n)) >>> n).setWidth n, none)

/-- An operation at size `sf` on 64-bit register contents. -/
def atSize (sf : Sf) (f : {n : Nat} → BitVec n → BitVec n → BitVec n × Option (BitVec 4))
    (x y : BitVec 64) : BitVec 64 × Option (BitVec 4) :=
  match sf with
  | .x => f x y
  | .w => let (r, fl) := f (x.setWidth 32) (y.setWidth 32); (r.setWidth 64, fl)

def alu (op : AluOp) (sf : Sf) (x y : BitVec 64) : BitVec 64 × Option (BitVec 4) :=
  atSize sf (aluN op) x y

/-- Data processing with an immediate (already turned into bits). -/
def aluImm (op : AluImmOp) (sf : Sf) (x imm : BitVec 64) : BitVec 64 × Option (BitVec 4) :=
  let op' : AluOp := match op with
    | .add => .add | .adds => .adds | .sub => .sub | .subs => .subs
    | .and => .and | .ands => .ands | .orr => .orr | .eor => .eor
  alu op' sf x imm

/-- A shift by an immediate below the size (`UBFM` and `SBFM` aliases). -/
def shiftImm (op : ShiftImmOp) (sf : Sf) (x : BitVec 64) (k : Nat) : BitVec 64 :=
  let f {n : Nat} (v : BitVec n) : BitVec n := match op with
    | .lsl => v <<< k
    | .lsr => v >>> k
    | .asr => v.sshiftRight k
  match sf with
  | .x => f x
  | .w => (f (x.setWidth 32)).setWidth 64

/-- `sbfx`/`ubfx d, n, #0, #width`: the low `width` bits, sign- or zero-extended to the size. -/
def ext (signed : Bool) (sf : Sf) (x : BitVec 64) (width : Nat) : BitVec 64 :=
  let low := x.setWidth width
  match sf with
  | .x => if signed then low.signExtend 64 else low.setWidth 64
  | .w => (if signed then low.signExtend 32 else low.setWidth 32).setWidth 64

/-- `movz`, `movn`, `movk`: a 16-bit immediate at bit `hw`; `movk` keeps the other bits of
`old`. -/
def movWide (op : MovOp) (sf : Sf) (old : BitVec 64) (imm hw : Nat) : BitVec 64 :=
  let n := sf.bits
  let v : BitVec 64 := BitVec.ofNat 64 (imm % 65536) <<< hw
  let r : BitVec 64 := match op with
    | .movz => v
    | .movn => ~~~v
    | .movk => (old &&& ~~~(BitVec.ofNat 64 65535 <<< hw)) ||| v
  (r.setWidth n).setWidth 64

/-- The value `csinc`, `csinv`, and `csneg` pick when the condition fails (`csel` picks `m`). -/
def cselElse (op : CselOp) (sf : Sf) (m : BitVec 64) : BitVec 64 :=
  let r := match op with
    | .csel => m
    | .csinc => m + 1
    | .csinv => ~~~m
    | .csneg => 0 - m
  (r.setWidth sf.bits).setWidth 64

/-! Spot checks against the architecture. -/

#guard (alu .subs .x 5 7).2 == some (nzcv true false false false)
#guard (alu .subs .x 7 7).2 == some (nzcv false true true false)
#guard (alu .adds .w 0x7fffffff 1).2 == some (nzcv true false false true)
#guard (alu .sdiv .x (BitVec.intMin 64) (BitVec.allOnes 64)).1 == BitVec.intMin 64
#guard (alu .udiv .x 7 0).1 == 0
#guard (alu .smulh .x (BitVec.allOnes 64) 2).1 == BitVec.allOnes 64
#guard (alu .umulh .x (BitVec.allOnes 64) 2).1 == 1
#guard (alu .lsl .w 1 33).1 == 2
#guard (alu .add .w 0xffffffff 1).1 == 0
#guard ext true .x 0x80 8 == BitVec.ofInt 64 (-128)
#guard ext false .w 0xffffffffffffffff 8 == 0xff
#guard movWide .movn .w 0 0 0 == 0xffffffff
#guard movWide .movk .x 0xffffffffffffffff 0x1234 16 == 0xffffffff1234ffff
#guard conditionHolds .lt (nzcv true false false false)
#guard !conditionHolds .hi (nzcv false true true false)

end Fir.AArch64
