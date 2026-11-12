import Fir.Basic
import Fir.OpDSL

/-!
# AArch64 LFIR: registers and modifiers

The vocabulary the `aarch64.*` ops (declared with the other ops in `Fir.Syntax`) are written in:
registers, which are immediates (`x3`, `sp`, `v12`), and the modifiers spelled in op names (the
operation size, condition codes, ALU operations).

LFIR is in *machine form* (decision: LFIR for AArch64): instructions read and write registers
named by immediates instead of SSA values, and a function's code is `aarch64.code`, whose labeled
blocks end in explicit branches. Before register allocation the code uses virtual registers
(`v0`, `v1`, …), each local to a call; after it, only the physical ones.
-/

namespace Fir

/-- A register: a general-purpose register `x0`…`x30`, the stack pointer `sp`, the zero register
`xzr`, or a virtual register `vN`. An op's size modifier (`.w` or `.x`) says how much of it the op
reads and writes; the name is the same for both. -/
inductive Reg where
  | x (n : Nat)
  | sp
  | xzr
  | v (n : Nat)
  deriving DecidableEq, Repr, Inhabited

def Reg.render : Reg → String
  | .x n => s!"x{n}"
  | .sp => "sp"
  | .xzr => "xzr"
  | .v n => s!"v{n}"

instance : ToString Reg := ⟨Reg.render⟩

/-- A register's name: `x0`…`x30`, `sp`, `xzr`, or `v` and a number. -/
def Reg.ofString? (s : String) : Option Reg :=
  if s == "sp" then some .sp
  else if s == "xzr" then some .xzr
  else
    match s.toList with
    | c :: ds =>
      let n? := if ds.isEmpty || (ds.length > 1 && ds.head? == some '0') then none
        else (String.ofList ds).toNat?
      match c, n? with
      | 'x', some n => if n ≤ 30 then some (.x n) else none
      | 'v', some n => some (.v n)
      | _, _ => none
    | [] => none

#guard Reg.ofString? "x30" == some (.x 30)
#guard Reg.ofString? "x31" == none
#guard Reg.ofString? "v007" == none
#guard Reg.ofString? "v12" == some (.v 12)

/-- The operation size (ASL's `sf`): `.w` reads the low 32 bits of its sources and writes a
zero-extended 32-bit result; `.x` uses all 64. -/
inductive Sf where
  | w | x
  deriving DecidableEq, Repr

def Sf.bits : Sf → Nat
  | .w => 32
  | .x => 64

instance : Spelled Sf := ⟨[sp "w" .w, sp "x" .x]⟩

/-- A condition on the flags NZCV (ASL's `ConditionHolds`). -/
inductive Cond where
  | eq | ne | hs | lo | mi | pl | vs | vc | hi | ls | ge | lt | gt | le
  deriving DecidableEq, Repr

instance : Spelled Cond := ⟨[sp "eq" .eq, sp "ne" .ne, sp "hs" .hs, sp "lo" .lo, sp "mi" .mi,
  sp "pl" .pl, sp "vs" .vs, sp "vc" .vc, sp "hi" .hi, sp "ls" .ls, sp "ge" .ge, sp "lt" .lt,
  sp "gt" .gt, sp "le" .le]⟩

/-- Three-register data processing. `adds`, `subs`, and `ands` also set the flags; `lsl`, `lsr`,
and `asr` shift by a register (`lslv` and friends: the amount modulo the size); `smulh` and
`umulh` are 64-bit only. -/
inductive AluOp where
  | add | adds | sub | subs | and | ands | orr | eor | bic | lsl | lsr | asr | mul | sdiv | udiv
  | smulh | umulh
  deriving DecidableEq, Repr

instance : Spelled AluOp := ⟨[sp "add" .add, sp "adds" .adds, sp "sub" .sub, sp "subs" .subs,
  sp "and" .and, sp "ands" .ands, sp "orr" .orr, sp "eor" .eor, sp "bic" .bic, sp "lsl" .lsl,
  sp "lsr" .lsr, sp "asr" .asr, sp "mul" .mul, sp "sdiv" .sdiv, sp "udiv" .udiv,
  sp "smulh" .smulh, sp "umulh" .umulh]⟩

/-- Data processing with an immediate: arithmetic (`imm12`, optionally shifted by 12) and
logical (a bitmask immediate). Which immediates encode is the emitter's concern. -/
inductive AluImmOp where
  | add | adds | sub | subs | and | ands | orr | eor
  deriving DecidableEq, Repr

instance : Spelled AluImmOp := ⟨[sp "add" .add, sp "adds" .adds, sp "sub" .sub, sp "subs" .subs,
  sp "and" .and, sp "ands" .ands, sp "orr" .orr, sp "eor" .eor]⟩

/-- Shifts by an immediate (aliases of `UBFM` and `SBFM`). -/
inductive ShiftImmOp where
  | lsl | lsr | asr
  deriving DecidableEq, Repr

instance : Spelled ShiftImmOp := ⟨[sp "lsl" .lsl, sp "lsr" .lsr, sp "asr" .asr]⟩

/-- Wide-immediate moves. -/
inductive MovOp where
  | movz | movn | movk
  deriving DecidableEq, Repr

instance : Spelled MovOp := ⟨[sp "movz" .movz, sp "movn" .movn, sp "movk" .movk]⟩

/-- Conditional selects. -/
inductive CselOp where
  | csel | csinc | csinv | csneg
  deriving DecidableEq, Repr

instance : Spelled CselOp := ⟨[sp "csel" .csel, sp "csinc" .csinc, sp "csinv" .csinv,
  sp "csneg" .csneg]⟩

/-- The size of a load or store: 1, 2, 4, or 8 bytes. -/
inductive MemSize where
  | b | h | w | x
  deriving DecidableEq, Repr

def MemSize.bytes : MemSize → Nat
  | .b => 1
  | .h => 2
  | .w => 4
  | .x => 8

instance : Spelled MemSize := ⟨[sp "b" .b, sp "h" .h, sp "w" .w, sp "x" .x]⟩

/-- `sbfx` (signed) and `ubfx`: extract the low bits and sign- or zero-extend them. -/
def extModes : List (Spelling Bool) := [sp "sbfx" true, sp "ubfx" false]

end Fir
