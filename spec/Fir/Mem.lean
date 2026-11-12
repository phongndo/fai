import Std.Data.ExtTreeMap
import Fir.Basic
import Fir.Syntax
import Fir.Layout

/-!
# Memory

Memory is a set of separate allocations, not one big array. Each allocation has a size, an
alignment, bytes, and a lifetime. It gets a numeric address only when one is first observed.

Maps here are extensional (`Std.ExtTreeMap`): two maps with the same entries are equal, however
they were built. So two runs that leave memory reading the same have equal states, which keeps
proofs about rewrites short.

Values are stored little-endian. Per-target byte order comes with data layouts.
-/

namespace Fir

inductive AllocKind where
  | stack
  | heap (family : String)
  /-- A global's memory, allocated before the program starts and never freed. -/
  | global (name : String) (const : Bool)
  /-- A function: size 0, so no access can read or write it. -/
  | func (name : String)
  deriving DecidableEq, Repr

/-- An allocation's bytes, by offset. Unwritten bytes are `poison`. -/
abbrev Bytes := Std.ExtTreeMap Nat Byte

/-- An allocation, apart from its bytes (which the machine keeps separately, so that writing
memory never changes this record). -/
structure Alloc where
  size : Nat
  align : Nat
  kind : AllocKind
  live : Bool := true
  /-- The address, once one has been observed. -/
  base : Option Nat := none
  /-- Tags whose pointers have been exposed. -/
  exposed : List Nat := []
  site : Option Loc := none
  freedAt : Option Loc := none

/-- Write bytes starting at `off`. -/
def writeBytes (m : Bytes) (off : Nat) : List Byte → Bytes
  | [] => m
  | b :: bs => writeBytes (m.insert off b) (off + 1) bs

def readBytes (m : Bytes) (off n : Nat) : List Byte :=
  (List.range n).map fun i => m.getD (off + i) .poison

/-- Whether byte `off` of the allocation is aligned to `n`: the offset is a multiple of `n` and
the allocation is aligned to at least `n`, or the allocation already has an address and the byte's
address is a multiple of `n`. The second case allows aligning by hand. Checking it never assigns an
address. -/
def Alloc.alignedAt (al : Alloc) (off : Int) (n : Nat) : Bool :=
  (off % n == 0 && al.align ≥ n) ||
    match al.base with
    | some b => (b + off) % n == 0
    | none => false

/-! ## Encoding values as bytes -/

/-- The low `k` base-256 digits of `n`, least significant first. -/
def digits : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => n % 256 :: digits k (n / 256)

/-- The number whose base-256 digits are `ds`, least significant first. -/
def undigits : List Nat → Nat
  | [] => 0
  | d :: ds => d + 256 * undigits ds

/-- An integer's bytes. `poison` makes every byte `poison`. -/
def encodeInt (w : Nat) : Val w → List Byte
  | .poison => List.replicate (w / 8) .poison
  | .bits b => (digits (w / 8) b.toNat).map fun d => .bits (BitVec.ofNat 8 d)

/-- A pointer's bytes: fragments that keep its provenance. -/
def encodePtr (cfg : SpaceCfg) : Option Ptr → List Byte
  | none => List.replicate (cfg.ptrBits / 8) .poison
  | some p => (List.range (cfg.ptrBits / 8)).map (.frag p)

/-- Read bytes back as an integer, if none of them is a pointer fragment. (The interpreter first
turns fragments into address bytes, exposing their pointers.) Any `poison` byte makes the result
`poison`. -/
def decodeInt? (w : Nat) (bs : List Byte) : Option (Val w) :=
  if bs.any (fun | .frag .. => true | _ => false) then none
  else if bs.any (· == .poison) then some .poison
  else some (.bits (BitVec.ofNat w (undigits (bs.map fun | .bits b => b.toNat | _ => 0))))

/-- The pointer whose fragments these bytes are, in order. -/
def ptrOfFrags? (n : Nat) : List Byte → Option Ptr
  | .frag p 0 :: rest =>
    if (Byte.frag p 0 :: rest) == (List.range n).map (.frag p) then some p else none
  | _ => none

/-- The bytes a value takes in memory. -/
def RVal.encode (cfg : SpaceCfg) : RVal → List Byte
  | .int w v => encodeInt w v
  | .ptr p => encodePtr cfg p
  | .bytes bs => bs
  -- Aggregates are stored leaf by leaf (`Fir.Interp`), never encoded whole.
  | .agg _ => []

end Fir
