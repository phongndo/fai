import Fir.AArch64Syntax
import Fir.Float

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

**Floating point** (decision: AArch64 semantics): scalar instructions on FP/SIMD registers, with
FPCR as Linux and macOS leave it (round to nearest, default-NaN mode `DN`, flush-to-zero `FZ`, and
alternate behavior `AH` off). The arithmetic is `Fir.Float`'s; what Arm adds is which NaN a
result is. `FPProcessNaNs` gives the first signaling NaN operand, else the first quiet one, made
quiet; an invalid operation with no NaN operand gives the default NaN, which is FIR's canonical
NaN (`nanResult`'s answer 0). Each result is one FIR's op allows (`Fir.AArch64Proofs`), so the
source refines to these with the oracle whose NaN choice is Arm's (decision: NaN choice).
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

/-! ## Floating point -/

section FP
open _root_.Fir.Float

variable {F : FloatFmt}

/-- A signaling NaN: a NaN with the quiet bit clear. -/
def isSNaN (x : Bits F) : Bool := isNaN x && manOf x < quietBit F

/-- ASL `FPProcessNaNs` (and `FPProcessNaN`, `FPProcessNaNs3`) with `DN` off: the first signaling
NaN operand, else the first quiet one, made quiet; `none` when no operand is a NaN. -/
def processNaNs (ops : List (Bits F)) : Option (Bits F) :=
  match ops.find? isSNaN with
  | some x => some (quietAs F x)
  | none => (ops.find? isNaN).map (quietAs F)

/-- What a scalar FP operation on two registers computes when no operand is a NaN, as FIR's op
does with the NaN answer `o`. -/
def _root_.Fir.FAluOp.float (op : FAluOp) (o : Int) : Bits F → Bits F → Bits F :=
  match op with
  | .fadd => Float.add o
  | .fsub => Float.sub o
  | .fmul => Float.mul o
  | .fdiv => Float.div o

/-- `fadd`, `fsub`, `fmul`, `fdiv` (ASL `FPAdd`, `FPSub`, `FPMul`, `FPDiv`). -/
def fpAlu (op : FAluOp) (x y : Bits F) : Bits F :=
  match processNaNs [x, y] with
  | some r => r
  | none => op.float 0 x y

/-- `fsqrt` (ASL `FPSqrt`). -/
def fpSqrt (x : Bits F) : Bits F :=
  match processNaNs [x] with
  | some r => r
  | none => Float.sqrt 0 x

/-- `fmadd` (ASL `FPMulAdd(addend, op1, op2)`): `n * m + a`, rounded once. A quiet NaN addend with
an infinite times zero product is an invalid operation, giving the default NaN. -/
def fpMulAdd (a n m : Bits F) : Bits F :=
  if isNaN a && !isSNaN a && (((decode n).isInf && (decode m).isZero) ||
      ((decode n).isZero && (decode m).isInf)) then canonNaN F
  else
    match processNaNs [a, n, m] with
    | some r => r
    | none => Float.fma 0 n m a

/-- `fcvt` between formats (ASL `FPConvert`): a NaN is made quiet in the new format
(`FPConvertNaN`); anything else is rounded (exact when widening). -/
def fpConvert (G : FloatFmt) (x : Bits F) : Bits G :=
  if isNaN x then quietAs G x else Float.cvt G 0 x

/-- `fcmp`'s flags (ASL `FPCompare`): `0011` unordered, `0110` equal, `1000` less, `0010`
greater; `-0` equals `+0`. -/
def fpCompare (x y : Bits F) : BitVec 4 :=
  match decode x, decode y with
  | .nan, _ | _, .nan => nzcv false false true true
  | a, b =>
    if a.ord F = b.ord F then nzcv false true true false
    else if a.ord F < b.ord F then nzcv true false false false
    else nzcv false false true false

/-- `fcvtzs` and `fcvtzu` into `n` bits (ASL `FPToFixed`, rounding toward zero): the integer part,
saturated at the bounds of the signed or unsigned range; NaN gives 0. -/
def fpToInt (signed : Bool) (n : Nat) (x : Bits F) : BitVec n :=
  let lo : Int := if signed then -(2 ^ (n - 1)) else 0
  let hi : Int := if signed then 2 ^ (n - 1) - 1 else 2 ^ n - 1
  match decode x with
  | .nan => 0
  | .inf neg => BitVec.ofInt n (if neg then lo else hi)
  | .fin .. => BitVec.ofInt n (max lo (min hi ((truncInt x).getD 0)))

/-- `scvtf` and `ucvtf` (ASL `FixedToFP`): an integer, rounded. -/
def intToFp (F : FloatFmt) (signed : Bool) (x : BitVec n) : Bits F :=
  Float.ofInt F (if signed then x.toInt else x.toNat)

/-- `fmov` of an immediate (ASL `VFPExpandImm`): the sign, an exponent of `NOT(b6)`, `E - 3`
copies of `b6`, and bits 5 and 4, and bits 3 to 0 at the top of the fraction:
`±(16 + imm8<3:0>) / 16 · 2^e`, `e` from -3 to 4. -/
def vfpExpandImm (F : FloatFmt) (imm8 : Nat) : Bits F :=
  let b6 := imm8 / 64 % 2
  let ones := if b6 = 1 then (2 ^ (F.e - 3) - 1) * 4 else 0
  pack F (imm8 / 128 % 2 == 1) ((1 - b6) * 2 ^ (F.e - 1) + ones + imm8 / 16 % 4)
    (imm8 % 16 * 2 ^ (F.m - 4))

end FP

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
#guard vfpExpandImm FloatTy.f64.fmt 0x70 == 0x3ff0000000000000
#guard vfpExpandImm FloatTy.f64.fmt 0x00 == 0x4000000000000000
#guard vfpExpandImm FloatTy.f32.fmt 0xf8 == 0xbfc00000
#guard vfpExpandImm FloatTy.f32.fmt 0x30 == 0x41800000
#guard vfpExpandImm FloatTy.f32.fmt 0x40 == 0x3e000000
-- fadd of a quiet and a signaling NaN: the signaling one, quieted.
#guard fpAlu (F := FloatTy.f32.fmt) .fadd 0x7fc00001 0x7f800002 == 0x7fc00002
#guard fpAlu (F := FloatTy.f32.fmt) .fadd 0xffc00001 0x3f800000 == 0xffc00001
-- inf - inf: the default NaN.
#guard fpAlu (F := FloatTy.f64.fmt) .fsub 0x7ff0000000000000 0x7ff0000000000000 ==
  0x7ff8000000000000
-- A quiet NaN addend with inf * 0: the default NaN, not the addend.
#guard fpMulAdd (F := FloatTy.f32.fmt) 0x7fc00005 0x7f800000 0 == 0x7fc00000
#guard fpMulAdd (F := FloatTy.f32.fmt) 0x7fc00005 0x3f800000 0x7f800001 == 0x7fc00001
#guard fpConvert (F := FloatTy.f64.fmt) FloatTy.f32.fmt 0x7ff0000020000000 == 0x7fc00001
#guard fpCompare (F := FloatTy.f32.fmt) 0x80000000 0 == nzcv false true true false
#guard fpCompare (F := FloatTy.f32.fmt) 0x7fc00000 0 == nzcv false false true true
#guard fpToInt (F := FloatTy.f64.fmt) true 32 0x41f0000000000000 == 0x7fffffff
#guard fpToInt (F := FloatTy.f64.fmt) false 64 0xbff0000000000000 == 0
#guard fpToInt (F := FloatTy.f32.fmt) true 64 0x7fc00000 == 0

end Fir.AArch64
