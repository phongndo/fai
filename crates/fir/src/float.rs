//! Floats, mirroring `spec/Fir/Float.lean` and `spec/Fir/FloatText.lean` for the oracle that
//! always answers 0 (decisions: Floats, Float ops, Float semantics, NaN determinism).
//!
//! A float value is its bits in a `u64`. Nothing here uses the host's float arithmetic, whose
//! results depend on the calling thread's floating-point environment (a C caller's `fesetround`,
//! or flush-to-zero and denormals-are-zero in x86-64's MXCSR or AArch64's FPCR): arithmetic and
//! conversions use `rustc_apfloat` (LLVM's APFloat in software, as Miri uses it), rounding to
//! nearest, ties to even, exactly as Lean's one rounding function does; `sqrt` follows Lean's
//! integer square root and `round` on big integers, comparisons compare bits as integers. Every
//! NaN an arithmetic op produces is replaced by the canonical NaN, the choice of the oracle that
//! always answers 0 (`Float.nanResult`, `Oracle.zero`), or by Arm's choice under
//! [`NanRule::Arm`]. The ops that only copy bits (`neg`, `abs`, `copysign`) keep payloads.
//! Conversions from integers wider than 128 bits, and the reading and writing of decimals, follow
//! Lean's `round` and `shortest` on big integers.

use num_bigint::{BigInt, BigUint, Sign};
use rustc_apfloat::ieee::{Double, Single};
use rustc_apfloat::{Float, FloatConvert, Round};

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

// Software arithmetic: a `Single` or `Double` holds a `f32` or `f64`'s bits.

const RNE: Round = Round::NearestTiesToEven;

fn sw<T: Float>(x: u64) -> T {
    T::from_bits(u128::from(x))
}

/// A result's bits, with every NaN made the canonical one.
fn of_sw<T: Float>(f: FloatTy, x: T) -> u64 {
    if x.is_nan() {
        fmt(f).canon_nan()
    } else {
        x.to_bits() as u64
    }
}

fn bin_sw<T: Float>(f: FloatTy, op: FBinOp, a: u64, b: u64) -> u64 {
    let (a, b) = (sw::<T>(a), sw::<T>(b));
    let r = match op {
        FBinOp::Add => a.add_r(b, RNE),
        FBinOp::Sub => a.sub_r(b, RNE),
        FBinOp::Mul => a.mul_r(b, RNE),
        FBinOp::Div => a.div_r(b, RNE),
        FBinOp::Copysign => unreachable!(),
    };
    of_sw(f, r.value)
}

/// How NaN results are picked: the oracle's NaN choice (Lean's `Oracle.nan`, decision: NaN
/// choice), for the two oracles the tools use.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum NanRule {
    /// The canonical NaN, always: the oracle that answers 0 (`fir run`, `fir-ref run`).
    #[default]
    Canonical,
    /// AArch64's rule with default-NaN mode off (`AArch64.processNaNs`): the first signaling NaN
    /// operand, else the first quiet one, made quiet, in the order the instruction that
    /// implements the op takes them; the canonical NaN for an invalid operation. Under this
    /// oracle a program's NaNs are those of its compiled code.
    Arm,
}

/// A NaN of format `f` as a quiet NaN of format `g` (Lean's `quietAs`).
pub fn quiet_as(f: FloatTy, g: FloatTy, x: u64) -> u64 {
    let (s, t) = (fmt(f), fmt(g));
    let man = if t.m >= s.m {
        s.man(x) << (t.m - s.m)
    } else {
        s.man(x) >> (s.m - t.m)
    };
    t.pack(s.sign(x), t.special(), man | t.quiet_bit())
}

fn is_snan(s: Fmt, x: u64) -> bool {
    s.is_nan(x) && s.man(x) & s.quiet_bit() == 0
}

/// Arm's `FPProcessNaNs` (Lean's `AArch64.processNaNs`): the first signaling NaN operand, else
/// the first quiet one, made quiet; `None` if no operand is a NaN.
pub fn process_nans(f: FloatTy, ops: &[u64]) -> Option<u64> {
    let s = fmt(f);
    ops.iter()
        .find(|&&x| is_snan(s, x))
        .or_else(|| ops.iter().find(|&&x| s.is_nan(x)))
        .map(|&x| quiet_as(f, f, x))
}

/// [`bin`] with NaN results picked by `rule`. Under Arm's rule the operands are in the order of
/// `fadd`, `fsub`, `fmul`, `fdiv`.
pub fn bin_with(rule: NanRule, f: FloatTy, op: FBinOp, a: u64, b: u64) -> u64 {
    if rule == NanRule::Arm
        && op != FBinOp::Copysign
        && let Some(r) = process_nans(f, &[a, b])
    {
        return r;
    }
    bin(f, op, a, b)
}

/// [`un`] with NaN results picked by `rule`.
pub fn un_with(rule: NanRule, f: FloatTy, op: FUnOp, a: u64) -> u64 {
    if rule == NanRule::Arm
        && op == FUnOp::Sqrt
        && let Some(r) = process_nans(f, &[a])
    {
        return r;
    }
    un(f, op, a)
}

/// [`fma`] (`a * b + c`) with NaN results picked by `rule`. Under Arm's rule it is `fmadd`
/// with addend `c` (Lean's `AArch64.fpMulAdd c a b`): a quiet NaN addend with an infinite times
/// zero product gives the canonical NaN, and NaN operands are taken in the order `c`, `a`, `b`.
pub fn fma_with(rule: NanRule, f: FloatTy, a: u64, b: u64, c: u64) -> u64 {
    if rule == NanRule::Arm {
        let s = fmt(f);
        let inf = |x: u64| s.exp(x) == s.special() && s.man(x) == 0;
        let zero = |x: u64| s.exp(x) == 0 && s.man(x) == 0;
        if s.is_nan(c) && !is_snan(s, c) && ((inf(a) && zero(b)) || (zero(a) && inf(b))) {
            return s.canon_nan();
        }
        if let Some(r) = process_nans(f, &[c, a, b]) {
            return r;
        }
    }
    fma(f, a, b, c)
}

/// [`cvt`] with NaN results picked by `rule`: under Arm's rule (`fcvt`), a NaN made quiet in the
/// new format.
pub fn cvt_with(rule: NanRule, f: FloatTy, g: FloatTy, a: u64) -> u64 {
    if rule == NanRule::Arm && fmt(f).is_nan(a) {
        return quiet_as(f, g, a);
    }
    cvt(f, g, a)
}

/// `float.add` and friends on defined bits.
pub fn bin(f: FloatTy, op: FBinOp, a: u64, b: u64) -> u64 {
    let s = fmt(f);
    if op == FBinOp::Copysign {
        let sm = 1u64 << (s.e + s.m);
        return (a & !sm) | (b & sm);
    }
    match f {
        FloatTy::F32 => bin_sw::<Single>(f, op, a, b),
        FloatTy::F64 => bin_sw::<Double>(f, op, a, b),
    }
}

pub fn un(f: FloatTy, op: FUnOp, a: u64) -> u64 {
    let s = fmt(f);
    let sm = 1u64 << (s.e + s.m);
    match op {
        FUnOp::Neg => a ^ sm,
        FUnOp::Abs => a & !sm,
        FUnOp::Sqrt => sqrt(s, a),
    }
}

/// `float.sqrt`, exact with integers: a positive finite `M · 2^E` (`M` normalized to `m + 1` or
/// `m + 2` bits, `E` even) has the root `√(M · 2^2k) · 2^((E - 2k) / 2)`; `r = ⌊√(M · 2^2k)⌋` has at
/// least two bits beyond the significand's `m + 1`, and with a sticky bit for an inexact root it
/// rounds as the true root does. The root of a positive float is always normal. (Lean's `sqrt`,
/// on units and big integers, is the test's oracle.)
fn sqrt(s: Fmt, a: u64) -> u64 {
    let (e, t) = (s.exp(a), s.man(a));
    if e == s.special() {
        return if t != 0 || s.sign(a) {
            s.canon_nan()
        } else {
            a
        };
    }
    if e == 0 && t == 0 {
        return a;
    }
    if s.sign(a) {
        return s.canon_nan();
    }
    let bias = (1i64 << (s.e - 1)) - 1;
    let m = i64::from(s.m);
    let (mut sig, mut exp) = if e == 0 {
        (u128::from(t), 1 - bias - m)
    } else {
        (u128::from(t | 1 << s.m), e as i64 - bias - m)
    };
    let lz = m - i64::from(127 - sig.leading_zeros());
    sig <<= lz;
    exp -= lz;
    if exp % 2 != 0 {
        sig <<= 1;
        exp -= 1;
    }
    let k2 = (m + 7) & !1; // even, at least m + 6
    let x = sig << k2;
    let r = x.isqrt();
    let sticky = r * r != x;
    let shift = i64::from(128 - r.leading_zeros()) - (m + 1);
    let mut q = r >> shift;
    let rem = r & ((1 << shift) - 1);
    let half = 1u128 << (shift - 1);
    if rem > half || (rem == half && (sticky || q & 1 == 1)) {
        q += 1;
    }
    let mut pow = (exp - k2) / 2 + shift;
    if q == 1 << (m + 1) {
        q >>= 1;
        pow += 1;
    }
    s.pack(false, (pow + m + bias) as u64, (q as u64) & mask(s.m))
}

fn fma_sw<T: Float>(f: FloatTy, a: u64, b: u64, c: u64) -> u64 {
    of_sw(f, sw::<T>(a).mul_add_r(sw(b), sw(c), RNE).value)
}

pub fn fma(f: FloatTy, a: u64, b: u64, c: u64) -> u64 {
    match f {
        FloatTy::F32 => fma_sw::<Single>(f, a, b, c),
        FloatTy::F64 => fma_sw::<Double>(f, a, b, c),
    }
}

pub fn cmp(f: FloatTy, p: FPred, a: u64, b: u64) -> bool {
    let s = fmt(f);
    if s.is_nan(a) || s.is_nan(b) {
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
    // Lean's `Num.ord`: a non-NaN value's magnitude bits grow with its magnitude (infinities
    // last), and both zeros are 0.
    let sm = 1u64 << (s.e + s.m);
    let ord = |x: u64| {
        let v = (x & !sm) as i64;
        if x & sm != 0 { -v } else { v }
    };
    let (x, y) = (ord(a), ord(b));
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

fn cvt_sw<T: Float + FloatConvert<U>, U: Float>(g: FloatTy, a: u64) -> u64 {
    of_sw(g, sw::<T>(a).convert_r(RNE, &mut false).value)
}

/// `float.ext` and `float.trunc`: a value of type `f` as a `g`, rounded.
pub fn cvt(f: FloatTy, g: FloatTy, a: u64) -> u64 {
    match (f, g) {
        (FloatTy::F32, FloatTy::F64) => cvt_sw::<Single, Double>(g, a),
        (FloatTy::F64, FloatTy::F32) => cvt_sw::<Double, Single>(g, a),
        (FloatTy::F32, FloatTy::F32) => cvt_sw::<Single, Single>(g, a),
        (FloatTy::F64, FloatTy::F64) => cvt_sw::<Double, Double>(g, a),
    }
}

fn from_int_sw<T: Float>(g: FloatTy, signed: bool, w: u32, raw: u128) -> u64 {
    let r = if signed {
        let v = if w == 128 {
            raw as i128
        } else {
            let s = 128 - w;
            ((raw << s) as i128) >> s
        };
        T::from_i128_r(v, RNE)
    } else {
        T::from_u128_r(raw, RNE)
    };
    of_sw(g, r.value)
}

/// `int.to_float`: the `w`-bit integer `x`, signed or unsigned, rounded to a `g`.
pub(crate) fn from_int(g: FloatTy, signed: bool, w: u32, x: &Bits) -> u64 {
    if w <= 128 {
        let raw: u128 = match x {
            Bits::Small(v) => u128::from(*v),
            Bits::Big(v) => u128::try_from(v).unwrap_or(0),
        };
        return match g {
            FloatTy::F32 => from_int_sw::<Single>(g, signed, w, raw),
            FloatTy::F64 => from_int_sw::<Double>(g, signed, w, raw),
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

    // Lean's definitions on big integers, as a check on the software arithmetic.

    enum Num {
        Nan,
        Inf(bool),
        Fin(bool, BigUint),
    }

    fn decode(s: Fmt, x: u64) -> Num {
        if s.exp(x) == s.special() {
            if s.man(x) != 0 {
                Num::Nan
            } else {
                Num::Inf(s.sign(x))
            }
        } else {
            Num::Fin(s.sign(x), s.units(x))
        }
    }

    fn sval(neg: bool, n: &BigUint) -> BigInt {
        BigInt::from_biguint(if neg { Sign::Minus } else { Sign::Plus }, n.clone())
    }

    fn signed_round(s: Fmt, v: &BigInt, zero_neg: bool, d: &BigUint) -> u64 {
        if v.sign() == Sign::NoSign {
            s.pack(zero_neg, 0, 0)
        } else {
            round(s, v.sign() == Sign::Minus, v.magnitude(), d)
        }
    }

    fn exact_bin(s: Fmt, op: FBinOp, x: u64, y: u64) -> u64 {
        let nan = s.canon_nan();
        let inf = |n: bool| s.pack(n, s.special(), 0);
        let q = one() << s.qneg;
        match (decode(s, x), decode(s, y), op) {
            (Num::Nan, _, _) | (_, Num::Nan, _) => nan,
            (Num::Inf(a), Num::Inf(b), FBinOp::Add) => {
                if a == b {
                    inf(a)
                } else {
                    nan
                }
            }
            (Num::Inf(a), Num::Inf(b), FBinOp::Sub) => {
                if a != b {
                    inf(a)
                } else {
                    nan
                }
            }
            (Num::Inf(a), Num::Fin(..), FBinOp::Add | FBinOp::Sub) => inf(a),
            (Num::Fin(..), Num::Inf(b), FBinOp::Add) => inf(b),
            (Num::Fin(..), Num::Inf(b), FBinOp::Sub) => inf(!b),
            (Num::Fin(a, n), Num::Fin(b, k), FBinOp::Add | FBinOp::Sub) => {
                let b = b != (op == FBinOp::Sub);
                signed_round(s, &(sval(a, &n) + sval(b, &k)), a && b, &one())
            }
            (Num::Inf(a), Num::Inf(b), FBinOp::Mul) => inf(a != b),
            (Num::Inf(a), Num::Fin(b, n), FBinOp::Mul)
            | (Num::Fin(b, n), Num::Inf(a), FBinOp::Mul) => {
                if is_zero(&n) {
                    nan
                } else {
                    inf(a != b)
                }
            }
            (Num::Fin(a, n), Num::Fin(b, k), FBinOp::Mul) => round(s, a != b, &(n * k), &q),
            (Num::Inf(_), Num::Inf(_), FBinOp::Div) => nan,
            (Num::Inf(a), Num::Fin(b, _), FBinOp::Div) => inf(a != b),
            (Num::Fin(a, _), Num::Inf(b), FBinOp::Div) => s.pack(a != b, 0, 0),
            (Num::Fin(a, n), Num::Fin(b, k), FBinOp::Div) => {
                if is_zero(&k) {
                    if is_zero(&n) { nan } else { inf(a != b) }
                } else {
                    round(s, a != b, &(n << s.qneg), &k)
                }
            }
            (_, _, FBinOp::Copysign) => unreachable!(),
        }
    }

    fn exact_fma(s: Fmt, x: u64, y: u64, z: u64) -> u64 {
        let nan = s.canon_nan();
        let inf = |n: bool| s.pack(n, s.special(), 0);
        let (a, b, c) = (decode(s, x), decode(s, y), decode(s, z));
        let parts = |v: &Num| match v {
            Num::Nan => unreachable!(),
            Num::Inf(n) => (*n, None),
            Num::Fin(n, k) => (*n, Some(k.clone())),
        };
        if matches!(a, Num::Nan) || matches!(b, Num::Nan) || matches!(c, Num::Nan) {
            return nan;
        }
        let ((na, ka), (nb, kb), (nc, kc)) = (parts(&a), parts(&b), parts(&c));
        let sp = na != nb;
        let zero = |k: &Option<BigUint>| k.as_ref().is_some_and(is_zero);
        if (zero(&ka) && kb.is_none()) || (ka.is_none() && zero(&kb)) {
            return nan;
        }
        if ka.is_none() || kb.is_none() {
            return match kc {
                None if nc != sp => nan,
                _ => inf(sp),
            };
        }
        let Some(kc) = kc else { return inf(nc) };
        let v = sval(sp, &(ka.unwrap() * kb.unwrap())) + sval(nc, &(kc << s.qneg));
        signed_round(s, &v, sp && nc, &(one() << s.qneg))
    }

    fn exact_sqrt(s: Fmt, x: u64) -> u64 {
        match decode(s, x) {
            Num::Nan | Num::Inf(true) => s.canon_nan(),
            Num::Inf(false) => x,
            Num::Fin(_, n) if is_zero(&n) => x,
            Num::Fin(true, _) => s.canon_nan(),
            Num::Fin(false, n) => {
                let x = n << (s.qneg + 2);
                let r = x.sqrt();
                let sticky = u32::from(&r * &r != x);
                round(s, false, &((r << 1u32) + sticky), &BigUint::from(4u32))
            }
        }
    }

    fn exact_cvt(f: Fmt, g: Fmt, x: u64) -> u64 {
        match decode(f, x) {
            Num::Nan => g.canon_nan(),
            Num::Inf(n) => g.pack(n, g.special(), 0),
            Num::Fin(n, k) if f.qneg <= g.qneg => round(g, n, &(k << (g.qneg - f.qneg)), &one()),
            Num::Fin(n, k) => round(g, n, &k, &(one() << (f.qneg - g.qneg))),
        }
    }

    /// Bits that hit the edge cases: zeros, subnormals, the normal limits, near-ties, infinities,
    /// and NaNs, with random significands.
    struct Gen(u64);

    impl Gen {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn float(&mut self, s: Fmt) -> u64 {
            let r = self.next();
            let sp = s.special();
            let e = match r % 8 {
                0 => 0,
                1 => 1 + (r >> 8) % 3,
                2 => sp - 1 - (r >> 8) % 3,
                3 => sp,
                4 => (sp >> 1) + (r >> 8) % 8 - 4,
                _ => (r >> 8) % (sp + 1),
            };
            let t = match (r >> 20) % 6 {
                0 => 0,
                1 => 1 + (r >> 24) % 4,
                2 => mask(s.m) - (r >> 24) % 4,
                _ => self.next() & mask(s.m),
            };
            s.pack((r >> 40) & 1 == 1, e, t)
        }
    }

    fn host(f: FloatTy, x: f64) -> u64 {
        if x.is_nan() {
            canonical_nan(f)
        } else {
            match f {
                FloatTy::F32 => u64::from((x as f32).to_bits()),
                FloatTy::F64 => x.to_bits(),
            }
        }
    }

    #[test]
    fn arithmetic_agrees_with_lean_and_the_host() {
        let mut g = Gen(0x9e37_79b9_7f4a_7c15);
        for f in [FloatTy::F32, FloatTy::F64] {
            let s = fmt(f);
            let hf = |x: u64| match f {
                FloatTy::F32 => f64::from(f32::from_bits(x as u32)),
                FloatTy::F64 => f64::from_bits(x),
            };
            for _ in 0..20000 {
                let (a, b, c) = (g.float(s), g.float(s), g.float(s));
                for op in [FBinOp::Add, FBinOp::Sub, FBinOp::Mul, FBinOp::Div] {
                    let ours = bin(f, op, a, b);
                    assert_eq!(ours, exact_bin(s, op, a, b), "{op:?} {a:#x} {b:#x}");
                    // The host, in its default environment, as a second opinion.
                    let host = match f {
                        FloatTy::F32 => {
                            let (x, y) = (f32::from_bits(a as u32), f32::from_bits(b as u32));
                            f64::from(match op {
                                FBinOp::Add => x + y,
                                FBinOp::Sub => x - y,
                                FBinOp::Mul => x * y,
                                _ => x / y,
                            })
                        }
                        FloatTy::F64 => {
                            let (x, y) = (hf(a), hf(b));
                            match op {
                                FBinOp::Add => x + y,
                                FBinOp::Sub => x - y,
                                FBinOp::Mul => x * y,
                                _ => x / y,
                            }
                        }
                    };
                    assert_eq!(ours, self::host(f, host), "{op:?} {a:#x} {b:#x}");
                }
                assert_eq!(
                    fma(f, a, b, c),
                    exact_fma(s, a, b, c),
                    "fma {a:#x} {b:#x} {c:#x}"
                );
                let host_fma = match f {
                    FloatTy::F32 => f64::from(
                        f32::from_bits(a as u32)
                            .mul_add(f32::from_bits(b as u32), f32::from_bits(c as u32)),
                    ),
                    FloatTy::F64 => hf(a).mul_add(hf(b), hf(c)),
                };
                assert_eq!(
                    fma(f, a, b, c),
                    host(f, host_fma),
                    "fma {a:#x} {b:#x} {c:#x}"
                );
                let host_sqrt = match f {
                    FloatTy::F32 => f64::from(f32::from_bits(a as u32).sqrt()),
                    FloatTy::F64 => hf(a).sqrt(),
                };
                assert_eq!(un(f, FUnOp::Sqrt, a), exact_sqrt(s, a), "sqrt {a:#x}");
                assert_eq!(un(f, FUnOp::Sqrt, a), host(f, host_sqrt), "sqrt {a:#x}");
                for p in [FPred::Oeq, FPred::Olt, FPred::Ole, FPred::Une, FPred::Uge] {
                    let (x, y) = (hf(a), hf(b));
                    let host_cmp = match p {
                        FPred::Oeq => x == y,
                        FPred::Olt => x < y,
                        FPred::Ole => x <= y,
                        FPred::Une => x != y,
                        _ => x.partial_cmp(&y) != Some(std::cmp::Ordering::Less),
                    };
                    assert_eq!(cmp(f, p, a, b), host_cmp, "{p:?} {a:#x} {b:#x}");
                }
                let other = match f {
                    FloatTy::F32 => FloatTy::F64,
                    FloatTy::F64 => FloatTy::F32,
                };
                assert_eq!(cvt(f, other, a), exact_cvt(s, fmt(other), a), "cvt {a:#x}");
                assert_eq!(cvt(f, f, a), exact_cvt(s, s, a), "cvt {a:#x}");
                let w = 1 + (g.next() % 128) as u32;
                let raw = (u128::from(g.next()) << 64 | u128::from(g.next())) >> (128 - w);
                let x = if w <= 64 {
                    Bits::Small(raw as u64)
                } else {
                    Bits::Big(BigUint::from(raw))
                };
                for signed in [false, true] {
                    let v = if signed {
                        x.to_int(w)
                    } else {
                        BigInt::from(x.to_nat())
                    };
                    let exact = signed_round(s, &(v << s.qneg), false, &one());
                    assert_eq!(
                        from_int(f, signed, w, &x),
                        exact,
                        "from_int {signed} {w} {raw:#x}"
                    );
                }
            }
        }
    }

    #[test]
    fn sqrt_agrees_with_the_host() {
        // Every 509th f32 (subnormals, normals, and the specials around them), and f64s spread
        // over every exponent.
        for x in (0..=u32::MAX)
            .step_by(509)
            .chain([1, 0x007f_ffff, 0x7f7f_ffff])
        {
            let host = f32::from_bits(x).sqrt();
            let want = if host.is_nan() {
                canonical_nan(FloatTy::F32)
            } else {
                u64::from(host.to_bits())
            };
            assert_eq!(un(FloatTy::F32, FUnOp::Sqrt, u64::from(x)), want, "{x:#x}");
        }
        let mut g = Gen(0x2545_f491_4f6c_dd1d);
        for _ in 0..200_000 {
            let x = g.next();
            assert_eq!(
                un(FloatTy::F64, FUnOp::Sqrt, x),
                host(FloatTy::F64, f64::from_bits(x).sqrt()),
                "{x:#x}"
            );
        }
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
