import Fir.Float

/-!
# Float constants as text

How `float.const`, run-line arguments, and run outcomes write a float's bits (decision: Float ops):

* A finite value prints as the shortest decimal that reads back to the same bits: among the
  decimals with the fewest significant digits that round to it, the closest, and on a tie the
  one whose last digit is even. With `D` its digits and `x` its scientific exponent (the value is
  `d.ddd × 10^x`), it is written plainly when `-4 ≤ x < 16`, always with a digit after the point
  (`1.5`, `100.0`, `0.001`, `-0.0`), and otherwise as `d[.ddd]e±x` with no `+` and no leading
  zeros in the exponent (`1e300`, `1.5e-7`, `5e-324`).
* Infinities are `inf` and `-inf`.
* A NaN is `nan` when its trailing significand is just the quiet bit (the canonical NaN), and
  otherwise `nan(0x…)`, the trailing significand field in lowercase hexadecimal with no leading
  zeros (quiet bit included: `f32` `0x7fc00001` is `nan(0x400001)`, the signaling `0x7f800001`
  is `nan(0x1)`). A set sign bit puts `-` in front: `-nan`, `-nan(0x1)`.

Reading a decimal rounds it to the nearest value, ties to even, as any exact result is rounded;
the shortest decimal reads back exactly by construction. Decimals far outside the format's
range are infinity or zero without computing their huge powers of ten (`ofDec`), which gives
what rounding them exactly would.
-/

namespace Fir.Float

variable {F : FloatFmt}

/-! ## Reading -/

/-- A float literal. -/
inductive Lit where
  /-- `±d × 10^e` -/
  | dec (neg : Bool) (d : Nat) (e : Int)
  | inf (neg : Bool)
  /-- `nan`, with the canonical trailing significand (`none`), or `nan(0x…)` with this one. -/
  | nan (neg : Bool) (payload : Option Nat)
  deriving DecidableEq, Repr

/-- `d × 10^e` as `num / den` units. -/
def decUnits (F : FloatFmt) (d : Nat) (e : Int) : Nat × Nat :=
  if 0 ≤ e then (d * 10 ^ e.toNat * 2 ^ F.qneg, 1) else (d * 2 ^ F.qneg, 10 ^ e.natAbs)

/-- `±d × 10^e`, rounded. -/
def roundDec (F : FloatFmt) (neg : Bool) (d : Nat) (e : Int) : Bits F :=
  let (a, b) := decUnits F d e
  round F neg a b

def numDigits (n : Nat) : Nat := (toString n).length

/-- `±d × 10^e`, rounded; values of at least `10^(top - qneg)` (at least `2^(top - qneg)`, where
rounding overflows) are infinite, and values below `10^-(qneg + 1)` (below half a unit) are zero,
without computing their powers of ten. -/
def ofDec (F : FloatFmt) (neg : Bool) (d : Nat) (e : Int) : Bits F :=
  if d = 0 then zero F neg
  else
    -- The value is below `10^L` and at least `10^(L - 1)`.
    let L : Int := numDigits d + e
    if (F.top : Int) - F.qneg ≤ L - 1 then inf F neg
    else if L ≤ -((F.qneg : Int) + 1) then zero F neg
    else roundDec F neg d e

/-- A literal's bits, if its NaN payload fits: nonzero, below `2^m`. -/
def Lit.toBits (F : FloatFmt) : Lit → Option (Bits F)
  | .dec neg d e => some (ofDec F neg d e)
  | .inf neg => some (Float.inf F neg)
  | .nan neg none => some (pack F neg F.special (quietBit F))
  | .nan neg (some p) => if 0 < p ∧ p < 2 ^ F.m then some (pack F neg F.special p) else none

def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

def hexVal? (c : Char) : Option Nat :=
  if c.isDigit then some (digitVal c)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def decimalOf (cs : List Char) : Nat := cs.foldl (fun n c => n * 10 + digitVal c) 0

def hexOf? (cs : List Char) : Option Nat :=
  cs.foldlM (fun n c => (hexVal? c).map (n * 16 + ·)) 0

/-- Read `[-](inf | nan | nan(0xH…) | D…[.D…][(e|E)[+|-]D…])`. -/
def parseLit (s : String) : Option Lit := do
  let (neg, cs) := match s.toList with
    | '-' :: cs => (true, cs)
    | cs => (false, cs)
  match cs with
  | ['i', 'n', 'f'] => some (.inf neg)
  | ['n', 'a', 'n'] => some (.nan neg none)
  | 'n' :: 'a' :: 'n' :: '(' :: '0' :: 'x' :: rest =>
    match rest.reverse with
    | ')' :: hs =>
      if hs.isEmpty then none else
      let p ← hexOf? hs.reverse
      some (.nan neg (some p))
    | _ => none
  | _ =>
    let ip := cs.takeWhile Char.isDigit
    if ip.isEmpty then none else
    let rest := cs.drop ip.length
    let (fp, rest) ← match rest with
      | '.' :: r =>
        let f := r.takeWhile Char.isDigit
        if f.isEmpty then none else some (f, r.drop f.length)
      | r => some ([], r)
    let e : Int ← match rest with
      | [] => some 0
      | c :: r =>
        if c != 'e' && c != 'E' then none else
        let (eneg, ds) := match r with
          | '-' :: ds => (true, ds)
          | '+' :: ds => (false, ds)
          | ds => (false, ds)
        if ds.isEmpty || !ds.all Char.isDigit then none else
        let v : Int := decimalOf ds
        some (if eneg then -v else v)
    some (.dec neg (decimalOf (ip ++ fp)) (e - fp.length))

/-! ## Writing -/

/-- `⌊log10 (a / b)⌋`, for `a, b > 0`. -/
def log10Floor (a b : Nat) : Int :=
  if b ≤ a then ((numDigits (a / b) - 1 : Nat) : Int)
  else
    let k := numDigits (b / a) - 1
    if b ≤ a * 10 ^ k then -(k : Int) else -((k + 1 : Nat) : Int)

/-- Strip trailing zeros: `(120, e)` is `(12, e + 1)`. -/
def stripZeros : Nat → Nat → Int → Nat × Int
  | 0, d, e => (d, e)
  | fuel + 1, d, e => if d ≠ 0 ∧ d % 10 = 0 then stripZeros fuel (d / 10) (e + 1) else (d, e)

/-- The shortest decimal `(d, e)`, the value `d × 10^e`, that rounds back to `x`, a finite
nonzero float of `n` units: for each length from 1, the two decimals of that many digits around
the value, the closer first (the even one on a tie). The exact value, at the last length tried,
always rounds back. -/
def shortest (F : FloatFmt) (x : Bits F) (neg : Bool) (n : Nat) : Nat × Int :=
  let L := log10Floor n (2 ^ F.qneg)
  go L (2 * F.qneg + 2 ^ F.e + 64) 1
where
  go (L : Int) : Nat → Nat → Nat × Int
    | 0, _ => (0, 0)
    | fuel + 1, len =>
      let e : Int := L - len + 1
      -- The value is `a / b` times `10^e`, and `lo` the integer part.
      let (a, b) := if 0 ≤ e then (n, 2 ^ F.qneg * 10 ^ e.toNat) else (n * 10 ^ e.natAbs, 2 ^ F.qneg)
      let lo := a / b
      let cands :=
        if 2 * a < (2 * lo + 1) * b then [lo, lo + 1]
        else if 2 * a > (2 * lo + 1) * b then [lo + 1, lo]
        else if lo % 2 = 0 then [lo, lo + 1] else [lo + 1, lo]
      match cands.find? (fun d => roundDec F neg d e == x) with
      | some d => stripZeros (numDigits d) d e
      | none => go L fuel (len + 1)

def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

/-- `d × 10^e` in the plain or the scientific form. -/
def renderDec (d : Nat) (e : Int) : String :=
  let ds := (toString d).toList
  let len := ds.length
  let x : Int := len - 1 + e
  if -4 ≤ x ∧ x < 16 then
    if 0 ≤ e then String.ofList ds ++ zeros e.toNat ++ ".0"
    else
      let k := e.natAbs
      if k < len then String.ofList (ds.take (len - k)) ++ "." ++ String.ofList (ds.drop (len - k))
      else "0." ++ zeros (k - len) ++ String.ofList ds
  else
    let rest := ds.drop 1
    String.ofList (ds.take 1) ++ (if rest.isEmpty then "" else "." ++ String.ofList rest) ++
      "e" ++ toString x

def hexText (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- The text of a float's bits. -/
def render (x : Bits F) : String :=
  let sign := if signOf x then "-" else ""
  match decode x with
  | .nan => sign ++ (if manOf x = quietBit F then "nan" else s!"nan(0x{hexText (manOf x)})")
  | .inf _ => sign ++ "inf"
  | .fin _ 0 => sign ++ "0.0"
  | .fin neg n =>
    let (d, e) := shortest F x neg n
    sign ++ renderDec d e

end Fir.Float
