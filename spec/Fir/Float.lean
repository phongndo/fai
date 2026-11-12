import Fir.Basic

/-!
# Floats

IEEE 754 binary floating point, bit for bit and generically over the format (`FloatFmt`)
(decisions: Floats, Float ops, Float semantics, NaN determinism). Round to nearest, ties to even;
no exception flags, no rounding modes, no fast-math permissions.

Every finite value of a format is a whole number of *units*, the smallest subnormal
`2^-qneg` (`2^-149` for `f32`, `2^-1074` for `f64`), so a float decodes (`decode`) to NaN, a
signed infinity, or a sign and a natural number of units. Each arithmetic op computes its exact
result as a sign and a nonnegative rational number of units, `n / d`, and rounds it once, with the
one rounding function `round`: the sum `a ± b` is `a ± b` units; the product of `a` and `b` units
is `a * b / 2^qneg` units; and so on. `sqrt` computes the integer square root of the exact result
scaled by 4, with a sticky bit for an inexact root: every rounding boundary is a whole number at
that scale, so a value strictly between `r` and `r + 1` rounds as the true root does. `fma`
rounds `a * b + c` once.

A NaN result is the oracle's choice (`nanResult`) between the canonical NaN (positive, only the
quiet bit set: `0x7fc00000` for `f32`, `0x7ff8000000000000` for `f64`) and each NaN input with its
quiet bit set (Wasm's rule); an answer of 0 picks the canonical NaN. The ops that only copy bits
(`neg`, `abs`, `copysign`) keep every payload, signaling ones included.
-/

namespace Fir

/-- Every finite value is a whole number of units, `2^-qneg`: the smallest subnormal. -/
def FloatFmt.qneg (F : FloatFmt) : Nat := 2 ^ (F.e - 1) + F.m - 2

/-- The all-ones exponent field, of infinities and NaNs. -/
def FloatFmt.special (F : FloatFmt) : Nat := 2 ^ F.e - 1

/-- `2^top` units is where rounding overflows to infinity: the largest finite value plus half
an ulp, rounded up to the next power of two, as IEEE 754 rounds with an unbounded exponent. -/
def FloatFmt.top (F : FloatFmt) : Nat := F.m + 2 ^ F.e - 2

namespace Float

/-- The bits of a value of format `F`. -/
abbrev Bits (F : FloatFmt) := BitVec F.width

variable {F G : FloatFmt}

/-! ## Fields -/

/-- The sign bit. -/
def signOf (x : Bits F) : Bool := x.toNat / 2 ^ (F.e + F.m) % 2 == 1

/-- The biased exponent field. -/
def expOf (x : Bits F) : Nat := x.toNat / 2 ^ F.m % 2 ^ F.e

/-- The trailing significand field. -/
def manOf (x : Bits F) : Nat := x.toNat % 2 ^ F.m

/-- The bits with these fields. -/
def pack (F : FloatFmt) (neg : Bool) (E T : Nat) : Bits F :=
  BitVec.ofNat F.width ((if neg then 2 ^ (F.e + F.m) else 0) + E * 2 ^ F.m + T)

/-- The sign bit alone. -/
def signMask (F : FloatFmt) : Bits F := BitVec.ofNat F.width (2 ^ (F.e + F.m))

def isNaN (x : Bits F) : Bool := expOf x == F.special && manOf x != 0

def inf (F : FloatFmt) (neg : Bool) : Bits F := pack F neg F.special 0

def zero (F : FloatFmt) (neg : Bool) : Bits F := pack F neg 0 0

/-- The quiet bit, the trailing significand's top bit. -/
def quietBit (F : FloatFmt) : Nat := 2 ^ (F.m - 1)

/-- The canonical NaN: positive, with only the quiet bit set. -/
def canonNaN (F : FloatFmt) : Bits F := pack F false F.special (quietBit F)

/-- A NaN of format `F` as a quiet NaN of format `G`: the same sign, the trailing significand's
top bits (shifted left into a wider format, or its low bits dropped for a narrower one), and the
quiet bit set. For `G = F` this only sets the quiet bit. -/
def quietAs (G : FloatFmt) (x : Bits F) : Bits G :=
  pack G (signOf x) G.special (manOf x * 2 ^ G.m / 2 ^ F.m ||| quietBit G)

/-- A NaN result (decision: NaN determinism): the canonical NaN, or one of the NaN inputs made
quiet, as the oracle's answer `o` picks; an answer of 0 picks the canonical NaN. -/
def nanResult (G : FloatFmt) (o : Int) (ins : List (Bits F)) : Bits G :=
  let cs := canonNaN G :: (ins.filter isNaN).map (quietAs G)
  cs.getD (o.toNat % cs.length) (canonNaN G)

/-! ## Values -/

/-- What a float stands for: NaN, a signed infinity, or a sign and a number of units. -/
inductive Num where
  | nan
  | inf (neg : Bool)
  | fin (neg : Bool) (n : Nat)
  deriving DecidableEq, Repr

/-- The number of units with exponent field `E` and trailing significand `T`. -/
def mag (F : FloatFmt) (E T : Nat) : Nat := if E = 0 then T else (2 ^ F.m + T) * 2 ^ (E - 1)

def decode (x : Bits F) : Num :=
  if expOf x = F.special then (if manOf x = 0 then .inf (signOf x) else .nan)
  else .fin (signOf x) (mag F (expOf x) (manOf x))

/-- A signed number of units. -/
def sval (neg : Bool) (n : Nat) : Int := if neg then -(n : Int) else n

def Num.neg : Num → Bool
  | .nan => false
  | .inf n | .fin n _ => n

def Num.isInf : Num → Bool
  | .inf _ => true
  | _ => false

def Num.isZero : Num → Bool
  | .fin _ 0 => true
  | _ => false

/-- The units of a finite value (0 otherwise). -/
def Num.units : Num → Nat
  | .fin _ n => n
  | _ => 0

/-! ## Rounding -/

/-- `n / d` rounded to the nearest integer, ties to even. -/
def rne (n d : Nat) : Nat :=
  if 2 * (n % d) > d ∨ (2 * (n % d) = d ∧ n / d % 2 = 1) then n / d + 1 else n / d

/-- The float nearest to `n / d` units (`d > 0`), with sign `neg`, ties to even; infinity from
`2^top` units up. The result keeps `s` low bits of the integer part's `m + 1` (or fewer) top
bits: its significand `i` is `n / d / 2^s` rounded. -/
def round (F : FloatFmt) (neg : Bool) (n d : Nat) : Bits F :=
  let s := Nat.log2 (n / d) - F.m
  let i := rne n (d * 2 ^ s)
  if i < 2 ^ F.m then pack F neg 0 i
  else
    let (i, s) := if i = 2 ^ (F.m + 1) then (2 ^ F.m, s + 1) else (i, s)
    if s + 1 ≥ F.special then inf F neg else pack F neg (s + 1) (i - 2 ^ F.m)

/-! ## Arithmetic -/

/-- `x + y` units, exact, then rounded; an exact zero is `-0` only when both addends are
negative (so both are zeros), as round-to-nearest gives. -/
def addFin (F : FloatFmt) (nx : Bool) (x : Nat) (ny : Bool) (y : Nat) : Bits F :=
  let s := sval nx x + sval ny y
  if s = 0 then zero F (nx && ny) else round F (decide (s < 0)) s.natAbs 1

def add (o : Int) (x y : Bits F) : Bits F :=
  match decode x, decode y with
  | .nan, _ | _, .nan => nanResult F o [x, y]
  | .inf a, .inf b => if a = b then inf F a else nanResult F o [x, y]
  | .inf a, .fin .. | .fin .., .inf a => inf F a
  | .fin a n, .fin b k => addFin F a n b k

def sub (o : Int) (x y : Bits F) : Bits F :=
  match decode x, decode y with
  | .nan, _ | _, .nan => nanResult F o [x, y]
  | .inf a, .inf b => if a = b then nanResult F o [x, y] else inf F a
  | .inf a, .fin .. => inf F a
  | .fin .., .inf b => inf F (!b)
  | .fin a n, .fin b k => addFin F a n (!b) k

def mul (o : Int) (x y : Bits F) : Bits F :=
  match decode x, decode y with
  | .nan, _ | _, .nan => nanResult F o [x, y]
  | .inf a, .inf b => inf F (a != b)
  | .inf a, .fin b n | .fin b n, .inf a => if n = 0 then nanResult F o [x, y] else inf F (a != b)
  | .fin a n, .fin b k => round F (a != b) (n * k) (2 ^ F.qneg)

def div (o : Int) (x y : Bits F) : Bits F :=
  match decode x, decode y with
  | .nan, _ | _, .nan => nanResult F o [x, y]
  | .inf _, .inf _ => nanResult F o [x, y]
  | .inf a, .fin b _ => inf F (a != b)
  | .fin a _, .inf b => zero F (a != b)
  | .fin a n, .fin b k =>
    if k = 0 then (if n = 0 then nanResult F o [x, y] else inf F (a != b))
    else round F (a != b) (n * 2 ^ F.qneg) k

/-- The square root of `n` units is `√(n · 2^qneg)` units. With `X` that scaled by 4 and
`r = ⌊√X⌋`, the root is `(2r + sticky) / 4` units, where the sticky bit says the root is
inexact: rounding boundaries are multiples of half a unit, whole numbers at the scale of `√X`,
so a value strictly between `r` and `r + 1` rounds like any other there. -/
def sqrt (o : Int) (x : Bits F) : Bits F :=
  match decode x with
  | .nan => nanResult F o [x]
  | .inf false => x
  | .inf true => nanResult F o [x]
  | .fin neg n =>
    if n = 0 then x
    else if neg then nanResult F o [x]
    else
      let X := n * 2 ^ F.qneg * 4
      let r := X.sqrt
      round F false (2 * r + (if r * r = X then 0 else 1)) 4

/-- `x * y + z`, rounded once. -/
def fma (o : Int) (x y z : Bits F) : Bits F :=
  let nan := nanResult F o [x, y, z]
  match decode x, decode y, decode z with
  | .nan, _, _ | _, .nan, _ | _, _, .nan => nan
  | a, b, c =>
    let sp := a.neg != b.neg
    if (a.isZero && b.isInf) || (a.isInf && b.isZero) then nan
    else if a.isInf || b.isInf then
      match c with
      | .inf nc => if nc = sp then inf F sp else nan
      | _ => inf F sp
    else
      match c with
      | .inf nc => inf F nc
      | _ =>
        let s := sval sp (a.units * b.units) + sval c.neg (c.units * 2 ^ F.qneg)
        if s = 0 then zero F (sp && c.neg)
        else round F (decide (s < 0)) s.natAbs (2 ^ F.qneg)

/-! ## Copying sign bits

These change only the sign bit, so every payload is kept. -/

def neg (x : Bits F) : Bits F := x ^^^ signMask F

def abs (x : Bits F) : Bits F := x &&& ~~~signMask F

/-- `x`'s magnitude with `y`'s sign. -/
def copysign (x y : Bits F) : Bits F := (x &&& ~~~signMask F) ||| (y &&& signMask F)

/-! ## Comparison -/

/-- A non-NaN value's place in the order: infinities beyond every finite value, and both zeros
at 0. -/
def Num.ord (F : FloatFmt) : Num → Int
  | .inf n => sval n (2 ^ F.top)
  | .fin n k => sval n k
  | .nan => 0

/-- Compare: `unordered` if either is NaN, otherwise `test` on their places in the order. -/
def cmp (unordered : Bool) (test : Int → Int → Bool) (x y : Bits F) : Bool :=
  match decode x, decode y with
  | .nan, _ | _, .nan => unordered
  | a, b => test (a.ord F) (b.ord F)

/-! ## Conversions -/

/-- A value of format `F` in format `G`, rounded (exact when `G` is wider). -/
def cvt (G : FloatFmt) (o : Int) (x : Bits F) : Bits G :=
  match decode x with
  | .nan => nanResult G o [x]
  | .inf n => inf G n
  | .fin n k =>
    if F.qneg ≤ G.qneg then round G n (k * 2 ^ (G.qneg - F.qneg)) 1
    else round G n k (2 ^ (F.qneg - G.qneg))

/-- An integer, rounded. -/
def ofInt (F : FloatFmt) (v : Int) : Bits F :=
  round F (decide (v < 0)) (v.natAbs * 2 ^ F.qneg) 1

/-- The integer part (toward zero) of a finite value; `none` for NaN and the infinities. -/
def truncInt (x : Bits F) : Option Int :=
  match decode x with
  | .fin n k => some (sval n (k / 2 ^ F.qneg))
  | _ => none

end Float

end Fir
