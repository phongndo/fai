//! Floats, mirroring `spec/Fir/Float.lean` and `spec/Fir/FloatText.lean` for the oracle that
//! always answers 0 (decisions: Floats, Float ops, Float semantics, NaN determinism).
//!
//! A float value is its bits in a `u64`. Arithmetic uses the host's IEEE 754 operations, which
//! round to nearest, ties to even, exactly as Lean's one rounding function does; the host's NaN
//! results differ between machines (x86-64 makes a negative NaN, AArch64 propagates an input), so
//! every NaN an arithmetic op produces is replaced by the canonical NaN, the choice of the oracle
//! that always answers 0 (`Float.nanResult`). The ops that only copy bits (`neg`, `abs`,
//! `copysign`) keep payloads. Conversions from integers wider than 128 bits, and the reading and
//! writing of decimals, have no exact host operation: they follow Lean's `round` and `shortest`
//! on big integers.

use num_bigint::{BigInt, BigUint, Sign};

use crate::ir::{CvtEdge, FBinOp, FPred, FUnOp, FloatTy};
use crate::sem::{Bits, Out, TrapReason, UbKind, mask};

fn one() -> BigUint {
    BigUint::from(1u32)
}

fn is_zero(n: &BigUint) -> bool {
    n.bits() == 0
}

fn small(n: &BigUint) -> u64 {
    u64::try_from(n).unwrap_or(0)
}

/// The format's parameters (Lean's `FloatFmt`): exponent width `e`, trailing significand width
/// `m`, and `qneg`, where a unit (the smallest subnormal) is `2^-qneg`.
#[derive(Clone, Copy)]
struct Fmt {
    e: u32,
    m: u32,
    qneg: u32,
}

fn fmt(f: FloatTy) -> Fmt {
    match f {
        FloatTy::F32 => Fmt {
            e: 8,
            m: 23,
            qneg: 149,
        },
        FloatTy::F64 => Fmt {
            e: 11,
            m: 52,
            qneg: 1074,
        },
    }
}

impl Fmt {
    /// The all-ones exponent field.
    fn special(self) -> u64 {
        (1 << self.e) - 1
    }

    fn top(self) -> u64 {
        u64::from(self.m) + (1 << self.e) - 2
    }

    fn pack(self, neg: bool, e: u64, t: u64) -> u64 {
        (u64::from(neg) << (self.e + self.m)) | (e << self.m) | t
    }

    fn quiet_bit(self) -> u64 {
        1 << (self.m - 1)
    }

    fn canon_nan(self) -> u64 {
        self.pack(false, self.special(), self.quiet_bit())
    }

    fn sign(self, x: u64) -> bool {
        (x >> (self.e + self.m)) & 1 == 1
    }

    fn exp(self, x: u64) -> u64 {
        (x >> self.m) & self.special()
    }

    fn man(self, x: u64) -> u64 {
        x & mask(self.m)
    }

    fn is_nan(self, x: u64) -> bool {
        self.exp(x) == self.special() && self.man(x) != 0
    }

    /// Lean's `decode` for a finite value: its number of units.
    fn units(self, x: u64) -> BigUint {
        let (e, t) = (self.exp(x), self.man(x));
        if e == 0 {
            BigUint::from(t)
        } else {
            BigUint::from((1u64 << self.m) + t) << (e - 1)
        }
    }
}

/// The canonical NaN of a type: positive, only the quiet bit set.
pub fn canonical_nan(f: FloatTy) -> u64 {
    fmt(f).canon_nan()
}

pub fn is_nan(f: FloatTy, x: u64) -> bool {
    fmt(f).is_nan(x)
}

fn of_host32(x: f32) -> u64 {
    if x.is_nan() {
        fmt(FloatTy::F32).canon_nan()
    } else {
        u64::from(x.to_bits())
    }
}

fn of_host64(x: f64) -> u64 {
    if x.is_nan() {
        fmt(FloatTy::F64).canon_nan()
    } else {
        x.to_bits()
    }
}

fn h32(x: u64) -> f32 {
    f32::from_bits(x as u32)
}

fn h64(x: u64) -> f64 {
    f64::from_bits(x)
}

/// `float.add` and friends on defined bits.
pub fn bin(f: FloatTy, op: FBinOp, a: u64, b: u64) -> u64 {
    let s = fmt(f);
    if op == FBinOp::Copysign {
        let sm = 1u64 << (s.e + s.m);
        return (a & !sm) | (b & sm);
    }
    match f {
        FloatTy::F32 => {
            let (a, b) = (h32(a), h32(b));
            of_host32(match op {
                FBinOp::Add => a + b,
                FBinOp::Sub => a - b,
                FBinOp::Mul => a * b,
                FBinOp::Div => a / b,
                FBinOp::Copysign => unreachable!(),
            })
        }
        FloatTy::F64 => {
            let (a, b) = (h64(a), h64(b));
            of_host64(match op {
                FBinOp::Add => a + b,
                FBinOp::Sub => a - b,
                FBinOp::Mul => a * b,
                FBinOp::Div => a / b,
                FBinOp::Copysign => unreachable!(),
            })
        }
    }
}

pub fn un(f: FloatTy, op: FUnOp, a: u64) -> u64 {
    let s = fmt(f);
    let sm = 1u64 << (s.e + s.m);
    match op {
        FUnOp::Neg => a ^ sm,
        FUnOp::Abs => a & !sm,
        FUnOp::Sqrt => match f {
            FloatTy::F32 => of_host32(h32(a).sqrt()),
            FloatTy::F64 => of_host64(h64(a).sqrt()),
        },
    }
}

pub fn fma(f: FloatTy, a: u64, b: u64, c: u64) -> u64 {
    match f {
        FloatTy::F32 => of_host32(h32(a).mul_add(h32(b), h32(c))),
        FloatTy::F64 => of_host64(h64(a).mul_add(h64(b), h64(c))),
    }
}

pub fn cmp(f: FloatTy, p: FPred, a: u64, b: u64) -> bool {
    let (x, y) = match f {
        FloatTy::F32 => (f64::from(h32(a)), f64::from(h32(b))),
        FloatTy::F64 => (h64(a), h64(b)),
    };
    if x.is_nan() || y.is_nan() {
        return matches!(
            p,
            FPred::Ueq
                | FPred::Une
                | FPred::Ult
                | FPred::Ule
                | FPred::Ugt
                | FPred::Uge
                | FPred::Uno
        );
    }
    match p {
        FPred::Oeq | FPred::Ueq => x == y,
        FPred::One | FPred::Une => x != y,
        FPred::Olt | FPred::Ult => x < y,
        FPred::Ole | FPred::Ule => x <= y,
        FPred::Ogt | FPred::Ugt => x > y,
        FPred::Oge | FPred::Uge => x >= y,
        FPred::Ord => true,
        FPred::Uno => false,
    }
}

/// `float.ext` and `float.trunc`: a value of type `f` as a `g`, rounded.
pub fn cvt(f: FloatTy, g: FloatTy, a: u64) -> u64 {
    match (f, g) {
        (FloatTy::F32, FloatTy::F64) => of_host64(f64::from(h32(a))),
        (FloatTy::F64, FloatTy::F32) => of_host32(h64(a) as f32),
        (FloatTy::F32, FloatTy::F32) => of_host32(h32(a)),
        (FloatTy::F64, FloatTy::F64) => of_host64(h64(a)),
    }
}

/// `int.to_float`: the `w`-bit integer `x`, signed or unsigned, rounded to a `g`.
pub(crate) fn from_int(g: FloatTy, signed: bool, w: u32, x: &Bits) -> u64 {
    if w <= 128 {
        let raw: u128 = match x {
            Bits::Small(v) => u128::from(*v),
            Bits::Big(v) => u128::try_from(v).unwrap_or(0),
        };
        if signed {
            let v = if w == 128 {
                raw as i128
            } else {
                let s = 128 - w;
                ((raw << s) as i128) >> s
            };
            return match g {
                FloatTy::F32 => u64::from((v as f32).to_bits()),
                FloatTy::F64 => (v as f64).to_bits(),
            };
        }
        return match g {
            FloatTy::F32 => u64::from((raw as f32).to_bits()),
            FloatTy::F64 => (raw as f64).to_bits(),
        };
    }
    let v = if signed {
        x.to_int(w)
    } else {
        BigInt::from(x.to_nat())
    };
    let s = fmt(g);
    round(
        s,
        v.sign() == Sign::Minus,
        &(v.magnitude() << s.qneg),
        &one(),
    )
}

/// `float.to_int`: the integer part of `a` (a `f`) as a `w`-bit integer.
pub(crate) fn to_int(f: FloatTy, signed: bool, edge: CvtEdge, w: u32, a: u64) -> Out {
    let s = fmt(f);
    let (lo, hi) = if signed {
        (
            -(BigInt::from(1u32) << (w - 1)),
            (BigInt::from(1u32) << (w - 1)) - 1,
        )
    } else {
        (BigInt::from(0u32), (BigInt::from(1u32) << w) - 1)
    };
    let neg = s.sign(a);
    let edge_out = |sat: BigInt| match edge {
        CvtEdge::Ub => Out::Ub(UbKind::Convert),
        CvtEdge::Trap => Out::Trap(TrapReason::Convert),
        CvtEdge::Sat => Out::Val(Some(crate::sem::konst(w, &sat))),
    };
    if s.exp(a) == s.special() {
        if s.man(a) != 0 {
            return edge_out(BigInt::from(0u32));
        }
        return edge_out(if neg { lo } else { hi });
    }
    let t = s.units(a) >> s.qneg;
    let v = BigInt::from_biguint(if neg { Sign::Minus } else { Sign::Plus }, t);
    if lo <= v && v <= hi {
        Out::Val(Some(crate::sem::konst(w, &v)))
    } else {
        edge_out(v.clamp(lo, hi))
    }
}

// Exact rounding (Lean's `round`)

/// `n / d` rounded to the nearest integer, ties to even.
fn rne(n: &BigUint, d: &BigUint) -> BigUint {
    let q = n / d;
    let r2 = (n % d) << 1u32;
    if r2 > *d || (r2 == *d && q.bit(0)) {
        q + 1u32
    } else {
        q
    }
}

fn log2(n: &BigUint) -> u64 {
    if is_zero(n) { 0 } else { n.bits() - 1 }
}

/// The float nearest to `n / d` units with sign `neg` (Lean's `round`).
fn round(s: Fmt, neg: bool, n: &BigUint, d: &BigUint) -> u64 {
    let sh = log2(&(n / d)).saturating_sub(u64::from(s.m));
    let i = rne(n, &(d << sh));
    let two_m = one() << s.m;
    if i < two_m {
        return s.pack(neg, 0, small(&i));
    }
    let (i, sh) = if i == (one() << (s.m + 1)) {
        (two_m.clone(), sh + 1)
    } else {
        (i, sh)
    };
    if sh + 1 >= s.special() {
        s.pack(neg, s.special(), 0)
    } else {
        s.pack(neg, sh + 1, small(&(i - two_m)))
    }
}

// Text (Lean's `Fir.FloatText`)

/// A float literal.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Lit {
    /// `±d × 10^e`; the exponent saturates far beyond where it matters.
    Dec {
        neg: bool,
        d: BigUint,
        e: i64,
    },
    Inf(bool),
    /// `nan`, or `nan(0x…)` with this trailing significand.
    Nan(bool, Option<BigUint>),
}

fn pow10(k: u64) -> BigUint {
    BigUint::from(10u32).pow(k as u32)
}

fn num_digits(n: &BigUint) -> i64 {
    n.to_string().len() as i64
}

/// `d × 10^e` as `num / den` units.
fn dec_units(s: Fmt, d: &BigUint, e: i64) -> (BigUint, BigUint) {
    if e >= 0 {
        ((d * pow10(e as u64)) << s.qneg, one())
    } else {
        (d << s.qneg, pow10(e.unsigned_abs()))
    }
}

fn round_dec(s: Fmt, neg: bool, d: &BigUint, e: i64) -> u64 {
    let (a, b) = dec_units(s, d, e);
    round(s, neg, &a, &b)
}

/// Lean's `ofDec`.
fn of_dec(s: Fmt, neg: bool, d: &BigUint, e: i64) -> u64 {
    if is_zero(d) {
        return s.pack(neg, 0, 0);
    }
    let l = num_digits(d) + e;
    if s.top() as i64 - i64::from(s.qneg) < l {
        s.pack(neg, s.special(), 0)
    } else if l <= -(i64::from(s.qneg) + 1) {
        s.pack(neg, 0, 0)
    } else {
        round_dec(s, neg, d, e)
    }
}

impl Lit {
    /// The bits of a `f`, if a NaN payload fits (Lean's `Lit.toBits`).
    pub fn to_bits(&self, f: FloatTy) -> Option<u64> {
        let s = fmt(f);
        match self {
            Lit::Dec { neg, d, e } => Some(of_dec(s, *neg, d, *e)),
            Lit::Inf(neg) => Some(s.pack(*neg, s.special(), 0)),
            Lit::Nan(neg, None) => Some(s.pack(*neg, s.special(), s.quiet_bit())),
            Lit::Nan(neg, Some(p)) => {
                let p = u64::try_from(p).ok()?;
                (p > 0 && p < 1 << s.m).then(|| s.pack(*neg, s.special(), p))
            }
        }
    }
}

/// Read `[-](inf | nan | nan(0xH…) | D…[.D…][(e|E)[+|-]D…])` (Lean's `parseLit`).
pub fn parse_lit(text: &str) -> Option<Lit> {
    let (neg, t) = match text.strip_prefix('-') {
        Some(t) => (true, t),
        None => (false, text),
    };
    match t {
        "inf" => return Some(Lit::Inf(neg)),
        "nan" => return Some(Lit::Nan(neg, None)),
        _ => {}
    }
    if let Some(rest) = t.strip_prefix("nan(0x") {
        let hs = rest.strip_suffix(')')?;
        if hs.is_empty() || !hs.chars().all(|c| c.is_ascii_hexdigit()) {
            return None;
        }
        return Some(Lit::Nan(neg, BigUint::parse_bytes(hs.as_bytes(), 16)));
    }
    let b = t.as_bytes();
    let mut i = 0;
    while i < b.len() && b[i].is_ascii_digit() {
        i += 1;
    }
    if i == 0 {
        return None;
    }
    let ip = &t[..i];
    let mut fp = "";
    if i < b.len() && b[i] == b'.' {
        let j = i + 1;
        let mut k = j;
        while k < b.len() && b[k].is_ascii_digit() {
            k += 1;
        }
        if k == j {
            return None;
        }
        fp = &t[j..k];
        i = k;
    }
    let mut e: i64 = 0;
    if i < b.len() {
        if b[i] != b'e' && b[i] != b'E' {
            return None;
        }
        let mut j = i + 1;
        let eneg = match b.get(j) {
            Some(b'-') => {
                j += 1;
                true
            }
            Some(b'+') => {
                j += 1;
                false
            }
            _ => false,
        };
        let ds = &t[j..];
        if ds.is_empty() || !ds.bytes().all(|c| c.is_ascii_digit()) {
            return None;
        }
        // Saturate: beyond `10^15` every value is already infinite or zero.
        let v = ds
            .parse::<i64>()
            .unwrap_or(i64::MAX)
            .min(1_000_000_000_000_000);
        e = if eneg { -v } else { v };
    }
    let digits = format!("{ip}{fp}");
    let d = BigUint::parse_bytes(digits.as_bytes(), 10)?;
    Some(Lit::Dec {
        neg,
        d,
        e: e - fp.len() as i64,
    })
}

/// `⌊log10 (a / b)⌋` for `a, b > 0` (Lean's `log10Floor`).
fn log10_floor(a: &BigUint, b: &BigUint) -> i64 {
    if b <= a {
        num_digits(&(a / b)) - 1
    } else {
        let k = num_digits(&(b / a)) - 1;
        if *b <= a * pow10(k as u64) {
            -k
        } else {
            -(k + 1)
        }
    }
}

/// The shortest decimal that reads back to `x`, a finite nonzero float of `n` units (Lean's
/// `shortest`).
fn shortest(s: Fmt, x: u64, neg: bool, n: &BigUint) -> (BigUint, i64) {
    let q = one() << s.qneg;
    let l = log10_floor(n, &q);
    let mut len = 1i64;
    loop {
        let e = l - len + 1;
        let (a, b) = if e >= 0 {
            (n.clone(), &q * pow10(e as u64))
        } else {
            (n * pow10(e.unsigned_abs()), q.clone())
        };
        let lo = &a / &b;
        let a2 = &a << 1u32;
        let mid = (&lo * 2u32 + 1u32) * &b;
        let hi = &lo + 1u32;
        let cands = if a2 < mid {
            [lo, hi]
        } else if a2 > mid || lo.bit(0) {
            [hi, lo]
        } else {
            [lo, hi]
        };
        for d in cands {
            if round_dec(s, neg, &d, e) == x {
                let (mut d, mut e) = (d, e);
                let ten = BigUint::from(10u32);
                while !is_zero(&d) && is_zero(&(&d % &ten)) {
                    d /= &ten;
                    e += 1;
                }
                return (d, e);
            }
        }
        len += 1;
    }
}

/// `d × 10^e` in the plain or the scientific form (Lean's `renderDec`).
fn render_dec(d: &BigUint, e: i64) -> String {
    let ds = d.to_string();
    let len = ds.len() as i64;
    let x = len - 1 + e;
    if (-4..16).contains(&x) {
        if e >= 0 {
            format!("{ds}{}.0", "0".repeat(e as usize))
        } else {
            let k = e.unsigned_abs() as usize;
            let len = ds.len();
            if k < len {
                format!("{}.{}", &ds[..len - k], &ds[len - k..])
            } else {
                format!("0.{}{ds}", "0".repeat(k - len))
            }
        }
    } else {
        let rest = &ds[1..];
        let frac = if rest.is_empty() {
            String::new()
        } else {
            format!(".{rest}")
        };
        format!("{}{frac}e{x}", &ds[..1])
    }
}

/// A float's bits as text (Lean's `Float.render`).
pub fn render(f: FloatTy, x: u64) -> String {
    let s = fmt(f);
    let neg = s.sign(x);
    let sign = if neg { "-" } else { "" };
    if s.exp(x) == s.special() {
        let t = s.man(x);
        return if t == 0 {
            format!("{sign}inf")
        } else if t == s.quiet_bit() {
            format!("{sign}nan")
        } else {
            format!("{sign}nan({t:#x})")
        };
    }
    let n = s.units(x);
    if is_zero(&n) {
        return format!("{sign}0.0");
    }
    let (d, e) = shortest(s, x, neg, &n);
    format!("{sign}{}", render_dec(&d, e))
}

/// Whether the bits fit the type.
pub fn fits(f: FloatTy, bits: u64) -> bool {
    f.width() == 64 || bits >> f.width() == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(f: FloatTy, s: &str) -> u64 {
        parse_lit(s).unwrap().to_bits(f).unwrap()
    }

    #[test]
    fn text_round_trips() {
        for s in [
            "1.5",
            "-0.0",
            "1e300",
            "5e-324",
            "0.1",
            "100.0",
            "1e16",
            "1000000000000000.0",
            "0.0001",
            "1e-5",
            "1.7976931348623157e308",
            "2.2250738585072014e-308",
            "nan",
            "-nan(0x1)",
            "inf",
            "-inf",
        ] {
            assert_eq!(render(FloatTy::F64, lit(FloatTy::F64, s)), s);
        }
        assert_eq!(render(FloatTy::F32, lit(FloatTy::F32, "0.1")), "0.1");
        assert_eq!(render(FloatTy::F32, lit(FloatTy::F32, "1e-45")), "1e-45");
        assert_eq!(lit(FloatTy::F32, "0.1"), 0x3dcccccd);
        assert_eq!(lit(FloatTy::F64, "0.1"), 0.1f64.to_bits());
    }

    #[test]
    fn printing_agrees_with_the_host() {
        // The host's shortest digits are a check on Lean's algorithm (ties aside).
        let mut x: u64 = 0x1234_5678_9abc_def1;
        for _ in 0..20000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let v = f64::from_bits(x);
            if v.is_finite() {
                let ours = parse_lit(&render(FloatTy::F64, x)).unwrap();
                assert_eq!(ours.to_bits(FloatTy::F64), Some(x));
                let host: f64 = format!("{v:e}").parse().unwrap();
                assert_eq!(host.to_bits(), x);
            }
            let w = f32::from_bits(x as u32);
            if w.is_finite() {
                let text = render(FloatTy::F32, x & 0xffff_ffff);
                let digits = |t: &str| {
                    t.trim_start_matches('-')
                        .split('e')
                        .next()
                        .unwrap()
                        .chars()
                        .filter(char::is_ascii_digit)
                        .collect::<String>()
                        .trim_matches('0')
                        .len()
                };
                let host = format!("{w:e}");
                assert_eq!(digits(&text), digits(&host), "{text} vs {host}");
                assert_eq!(text.parse::<f32>().unwrap().to_bits(), x as u32);
            }
        }
    }
}
