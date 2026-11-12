//! What each integer op computes, mirroring `spec/Fir/Sem.lean`.
//!
//! A defined `iN` value is its bits, read as an unsigned number below `2^N` ([`Bits`]): a `u64`
//! when `N ≤ 64`, a big integer otherwise. Every op has a fast path on `u64` and an exact path on
//! big integers, both following the Lean definitions (Lean's `BitVec`) case by case. `None` is
//! `poison`.

use num_bigint::{BigInt, BigUint, Sign};

use crate::ir::{ArithOp, BitOp, DivOp, Edge, Ovf, Pred, ShiftEdge, ShiftOp, TruncMode};

/// A defined integer's bits: `Small` exactly when the width is at most 64.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum Bits {
    Small(u64),
    Big(BigUint),
}

/// Why a trap happened (Lean's `TrapReason`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum TrapReason {
    Div0,
    Overflow,
    Shift,
    Oom,
    Bounds,
    Tag,
}

impl TrapReason {
    pub fn name(self) -> &'static str {
        match self {
            TrapReason::Div0 => "div0",
            TrapReason::Overflow => "overflow",
            TrapReason::Shift => "shift",
            TrapReason::Oom => "oom",
            TrapReason::Bounds => "bounds",
            TrapReason::Tag => "tag",
        }
    }
}

/// Which rule a program broke (Lean's `UBKind`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UbKind {
    Div0,
    Overflow,
    Shift,
    Poison,
    Fact,
    NoProgress,
    NoProvenance,
    OutOfBounds,
    UseAfterFree,
    Misaligned,
    DoubleFree,
    BadFree,
    NoAlias,
    ReadOnly,
    PtrCompare,
    AddressSpace,
    ConstWrite,
    FuncAccess,
    BadCall,
    Bounds,
    Tag,
}

impl UbKind {
    pub fn name(self) -> &'static str {
        match self {
            UbKind::Div0 => "div0",
            UbKind::Overflow => "overflow",
            UbKind::Shift => "shift",
            UbKind::Poison => "poison",
            UbKind::Fact => "fact",
            UbKind::NoProgress => "no-progress",
            UbKind::NoProvenance => "no-provenance",
            UbKind::OutOfBounds => "out-of-bounds",
            UbKind::UseAfterFree => "use-after-free",
            UbKind::Misaligned => "misaligned",
            UbKind::DoubleFree => "double-free",
            UbKind::BadFree => "bad-free",
            UbKind::NoAlias => "noalias",
            UbKind::ReadOnly => "readonly",
            UbKind::PtrCompare => "ptr-compare",
            UbKind::AddressSpace => "address-space",
            UbKind::ConstWrite => "const-write",
            UbKind::FuncAccess => "func-access",
            UbKind::BadCall => "bad-call",
            UbKind::Bounds => "bounds",
            UbKind::Tag => "tag",
        }
    }
}

/// The outcome of one integer op (Lean's `OpOut`); `Val(None)` is `poison`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum Out {
    Val(Option<Bits>),
    Trap(TrapReason),
    Ub(UbKind),
}

/// The low `w` bits set, for `w ≤ 64`.
pub(crate) fn mask(w: u32) -> u64 {
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
}

/// `2^w` as a big integer.
fn pow2(w: u32) -> BigInt {
    BigInt::from(1u8) << w
}

/// Sign-extend the low `w` bits (`0 < w ≤ 64`).
pub(crate) fn sext64(w: u32, x: u64) -> i64 {
    let s = 64 - w;
    ((x << s) as i64) >> s
}

/// `n` wrapped to a signed `w`-bit integer (`0 < w ≤ 64`).
pub(crate) fn wrap_signed(w: u32, n: i128) -> i128 {
    let m = 1i128 << w;
    let r = n.rem_euclid(m);
    if r >= m / 2 { r - m } else { r }
}

impl Bits {
    /// The value `n mod 2^w`.
    pub(crate) fn of_int(w: u32, n: &BigInt) -> Bits {
        if w <= 64 {
            // The low 64 bits of the two's complement, then the low `w`.
            let (sign, digits) = n.to_u64_digits();
            let low = digits.first().copied().unwrap_or(0);
            let low = if sign == Sign::Minus {
                low.wrapping_neg()
            } else {
                low
            };
            Bits::Small(low & mask(w))
        } else {
            let m = pow2(w);
            let mut r = n % &m;
            if r.sign() == Sign::Minus {
                r += &m;
            }
            Bits::Big(r.magnitude().clone())
        }
    }

    pub(crate) fn of_i128(w: u32, n: i128) -> Bits {
        if w <= 64 {
            Bits::Small((n as u64) & mask(w))
        } else {
            Bits::of_int(w, &BigInt::from(n))
        }
    }

    /// The value `n mod 2^w`, for `n ≥ 0`.
    pub(crate) fn of_nat(w: u32, n: &BigUint) -> Bits {
        if w <= 64 {
            Bits::Small(n.iter_u64_digits().next().unwrap_or(0) & mask(w))
        } else if n.bits() <= u64::from(w) {
            Bits::Big(n.clone())
        } else {
            Bits::Big(n % pow2(w).magnitude())
        }
    }

    pub(crate) fn zero(w: u32) -> Bits {
        Bits::of_i128(w, 0)
    }

    /// The unsigned value (`BitVec.toNat`).
    pub(crate) fn to_nat(&self) -> BigUint {
        match self {
            Bits::Small(x) => BigUint::from(*x),
            Bits::Big(x) => x.clone(),
        }
    }

    /// The signed value (`BitVec.toInt`).
    pub(crate) fn to_int(&self, w: u32) -> BigInt {
        match self {
            Bits::Small(x) => BigInt::from(sext64(w, *x)),
            Bits::Big(x) => {
                if x.bit(u64::from(w) - 1) {
                    BigInt::from(x.clone()) - pow2(w)
                } else {
                    BigInt::from(x.clone())
                }
            }
        }
    }

    pub(crate) fn is_zero(&self) -> bool {
        match self {
            Bits::Small(x) => *x == 0,
            Bits::Big(x) => x.bits() == 0,
        }
    }

    /// The unsigned value if it fits in 64 bits.
    pub(crate) fn to_u64(&self) -> Option<u64> {
        match self {
            Bits::Small(x) => Some(*x),
            Bits::Big(x) => u64::try_from(x).ok(),
        }
    }

    fn big(&self) -> &BigUint {
        match self {
            Bits::Big(x) => x,
            Bits::Small(_) => unreachable!("a wide value stored in 64 bits"),
        }
    }

    fn small(&self) -> u64 {
        match self {
            Bits::Small(x) => *x,
            Bits::Big(_) => unreachable!("a narrow value stored as a big integer"),
        }
    }
}

/// `int.const n`: `n` wrapped to `w` bits.
pub(crate) fn konst(w: u32, n: &BigInt) -> Bits {
    Bits::of_int(w, n)
}

fn exact(op: ArithOp, a: &BigInt, b: &BigInt) -> BigInt {
    match op {
        ArithOp::Add => a + b,
        ArithOp::Sub => a - b,
        ArithOp::Mul => a * b,
    }
}

/// What `int.add`/`sub`/`mul` of two defined values needs: the wrapped result, whether each kind
/// of overflow happens, and the saturated results.
struct ArithFacts {
    wrapped: Bits,
    ovf_s: bool,
    ovf_u: bool,
    sat_s: Bits,
    sat_u: Bits,
}

fn arith_facts(op: ArithOp, w: u32, a: &Bits, b: &Bits) -> ArithFacts {
    if w <= 64 {
        let (x, y) = (a.small(), b.small());
        let m = mask(w);
        let wrapped = match op {
            ArithOp::Add => x.wrapping_add(y),
            ArithOp::Sub => x.wrapping_sub(y),
            ArithOp::Mul => x.wrapping_mul(y),
        } & m;
        // Signed: exact in i128 (|x|, |y| ≤ 2^63).
        let (sx, sy) = (i128::from(sext64(w, x)), i128::from(sext64(w, y)));
        let rs = match op {
            ArithOp::Add => sx + sy,
            ArithOp::Sub => sx - sy,
            ArithOp::Mul => sx * sy,
        };
        let smax = (1i128 << (w - 1)) - 1;
        let smin = -(1i128 << (w - 1));
        // Unsigned: the exact result clamped to [0, 2^w - 1].
        let (ovf_u, sat_u) = match op {
            ArithOp::Add => {
                let r = u128::from(x) + u128::from(y);
                (r > u128::from(m), r.min(u128::from(m)) as u64)
            }
            ArithOp::Sub => (x < y, x.saturating_sub(y)),
            ArithOp::Mul => {
                let r = u128::from(x) * u128::from(y);
                (r > u128::from(m), r.min(u128::from(m)) as u64)
            }
        };
        ArithFacts {
            wrapped: Bits::Small(wrapped),
            ovf_s: rs < smin || rs > smax,
            ovf_u,
            sat_s: Bits::of_i128(w, rs.clamp(smin, smax)),
            sat_u: Bits::Small(sat_u),
        }
    } else {
        let (xu, yu) = (BigInt::from(a.big().clone()), BigInt::from(b.big().clone()));
        let (xs, ys) = (a.to_int(w), b.to_int(w));
        let ru = exact(op, &xu, &yu);
        let rs = exact(op, &xs, &ys);
        let umax = pow2(w) - 1;
        let smax = pow2(w - 1) - 1;
        let smin = -pow2(w - 1);
        let zero = BigInt::from(0u8);
        ArithFacts {
            wrapped: Bits::of_int(w, &ru),
            ovf_s: rs < smin || rs > smax,
            ovf_u: ru < zero || ru > umax,
            sat_s: Bits::of_int(w, &rs.clone().clamp(smin, smax)),
            sat_u: Bits::of_int(w, &ru.clamp(zero, umax)),
        }
    }
}

fn ovf_needs_defined(o: Ovf) -> bool {
    matches!(o, Ovf::Trap(_) | Ovf::Ub(_))
}

/// `int.add.overflow.s` and friends on defined operands: the wrapped result and whether the
/// operation overflowed, signed or unsigned.
pub(crate) fn overflow_pair(op: ArithOp, signed: bool, w: u32, a: &Bits, b: &Bits) -> (Bits, bool) {
    let f = arith_facts(op, w, a, b);
    (f.wrapped, if signed { f.ovf_s } else { f.ovf_u })
}

/// `int.add`, `int.sub`, `int.mul` (Lean's `Sem.arith`).
pub(crate) fn arith(op: ArithOp, ovf: Ovf, w: u32, a: Option<&Bits>, b: Option<&Bits>) -> Out {
    let (Some(a), Some(b)) = (a, b) else {
        return if ovf_needs_defined(ovf) {
            Out::Ub(UbKind::Poison)
        } else {
            Out::Val(None)
        };
    };
    let f = arith_facts(op, w, a, b);
    let pick = |o: bool, v: Bits| Out::Val((!o).then_some(v));
    match ovf {
        Ovf::Wrap => Out::Val(Some(f.wrapped)),
        Ovf::Nsw => pick(f.ovf_s, f.wrapped),
        Ovf::Nuw => pick(f.ovf_u, f.wrapped),
        Ovf::NswNuw => pick(f.ovf_s || f.ovf_u, f.wrapped),
        Ovf::Trap(s) => {
            if if s { f.ovf_s } else { f.ovf_u } {
                Out::Trap(TrapReason::Overflow)
            } else {
                Out::Val(Some(f.wrapped))
            }
        }
        Ovf::Ub(s) => {
            if if s { f.ovf_s } else { f.ovf_u } {
                Out::Ub(UbKind::Overflow)
            } else {
                Out::Val(Some(f.wrapped))
            }
        }
        Ovf::Sat(s) => {
            let (o, sat) = if s {
                (f.ovf_s, f.sat_s)
            } else {
                (f.ovf_u, f.sat_u)
            };
            Out::Val(Some(if o { sat } else { f.wrapped }))
        }
    }
}

/// `int.and`, `int.or`, `int.xor`.
pub(crate) fn bit(op: BitOp, a: Option<&Bits>, b: Option<&Bits>) -> Option<Bits> {
    Some(match (a?, b?) {
        (Bits::Small(x), Bits::Small(y)) => Bits::Small(match op {
            BitOp::And => x & y,
            BitOp::Or => x | y,
            BitOp::Xor => x ^ y,
        }),
        (x, y) => {
            let (x, y) = (x.big(), y.big());
            Bits::Big(match op {
                BitOp::And => x & y,
                BitOp::Or => x | y,
                BitOp::Xor => x ^ y,
            })
        }
    })
}

/// Lean's `BitVec.sdiv`/`udiv`/`srem`/`umod`: `x / 0 = 0`, `x rem 0 = x`, signed ops truncate
/// toward zero, and `MIN / -1` wraps to `MIN`.
fn div_bits(op: DivOp, w: u32, a: &Bits, b: &Bits) -> Bits {
    if w <= 64 {
        let (x, y) = (a.small(), b.small());
        let r = match op {
            DivOp::DivU => x.checked_div(y).unwrap_or(0),
            DivOp::RemU => x.checked_rem(y).unwrap_or(x),
            DivOp::DivS | DivOp::RemS => {
                let (sx, sy) = (i128::from(sext64(w, x)), i128::from(sext64(w, y)));
                if sy == 0 {
                    if op == DivOp::DivS { 0 } else { x }
                } else if op == DivOp::DivS {
                    (sx / sy) as u64
                } else {
                    (sx % sy) as u64
                }
            }
        };
        Bits::Small(r & mask(w))
    } else {
        let (x, y) = (a.big(), b.big());
        match op {
            DivOp::DivU if y.bits() == 0 => Bits::zero(w),
            DivOp::DivU => Bits::Big(x / y),
            DivOp::RemU if y.bits() == 0 => a.clone(),
            DivOp::RemU => Bits::Big(x % y),
            DivOp::DivS | DivOp::RemS => {
                let (sx, sy) = (a.to_int(w), b.to_int(w));
                if sy.sign() == Sign::NoSign {
                    if op == DivOp::DivS {
                        Bits::zero(w)
                    } else {
                        a.clone()
                    }
                } else if op == DivOp::DivS {
                    Bits::of_int(w, &(sx / sy))
                } else {
                    Bits::of_int(w, &(sx % sy))
                }
            }
        }
    }
}

fn edge_needs_defined(e: Edge) -> bool {
    matches!(e, Edge::Ub | Edge::Trap)
}

fn is_int_min(w: u32, x: &Bits) -> bool {
    match x {
        Bits::Small(x) => *x == 1u64 << (w - 1),
        Bits::Big(x) => x.bits() == u64::from(w) && x.trailing_zeros() == Some(u64::from(w) - 1),
    }
}

fn is_all_ones(w: u32, x: &Bits) -> bool {
    match x {
        Bits::Small(x) => *x == mask(w),
        Bits::Big(x) => x.count_ones() == u64::from(w),
    }
}

/// Division and remainder (Lean's `Sem.div`): `zero` applies to a zero divisor, `ovf` to signed
/// `MIN / -1`.
pub(crate) fn div(
    op: DivOp,
    zero: Edge,
    ovf: Edge,
    w: u32,
    a: Option<&Bits>,
    b: Option<&Bits>,
) -> Out {
    let Some(b) = b else {
        return if edge_needs_defined(zero) {
            Out::Ub(UbKind::Poison)
        } else {
            Out::Val(None)
        };
    };
    if b.is_zero() {
        return match (zero, a) {
            (Edge::Ub, _) => Out::Ub(UbKind::Div0),
            (Edge::Trap, _) => Out::Trap(TrapReason::Div0),
            (_, None) => Out::Val(None),
            (_, Some(x)) => Out::Val(Some(div_bits(op, w, x, b))),
        };
    }
    let Some(x) = a else {
        return if op.signed() && edge_needs_defined(ovf) {
            Out::Ub(UbKind::Poison)
        } else {
            Out::Val(None)
        };
    };
    if op.signed() && is_int_min(w, x) && is_all_ones(w, b) {
        match ovf {
            Edge::Ub => Out::Ub(UbKind::Overflow),
            Edge::Trap => Out::Trap(TrapReason::Overflow),
            _ => Out::Val(Some(div_bits(op, w, x, b))),
        }
    } else {
        Out::Val(Some(div_bits(op, w, x, b)))
    }
}

/// Shift `x` by `n` bits, which may be at least the width (Lean's `shiftBits`).
fn shift_bits(op: ShiftOp, w: u32, x: &Bits, n: u64) -> Bits {
    if w <= 64 {
        let x = x.small();
        let neg = x >> (w - 1) & 1 == 1;
        let r = if n >= u64::from(w) {
            match op {
                ShiftOp::Shl | ShiftOp::ShrU => 0,
                ShiftOp::ShrS => {
                    if neg {
                        u64::MAX
                    } else {
                        0
                    }
                }
            }
        } else {
            match op {
                ShiftOp::Shl => x << n,
                ShiftOp::ShrU => x >> n,
                ShiftOp::ShrS => (sext64(w, x) >> n) as u64,
            }
        };
        Bits::Small(r & mask(w))
    } else {
        let xb = x.big();
        let n = n.min(u64::from(w));
        match op {
            ShiftOp::Shl => Bits::of_nat(w, &(xb << n)),
            ShiftOp::ShrU => Bits::Big(xb >> n),
            ShiftOp::ShrS => Bits::of_int(w, &(x.to_int(w) >> n)),
        }
    }
}

fn shift_edge_needs_defined(e: ShiftEdge) -> bool {
    matches!(e, ShiftEdge::Ub | ShiftEdge::Trap)
}

/// Shifts (Lean's `Sem.shift`). The amount is read as unsigned.
pub(crate) fn shift(
    op: ShiftOp,
    edge: ShiftEdge,
    w: u32,
    a: Option<&Bits>,
    n: Option<&Bits>,
) -> Out {
    let Some(n) = n else {
        return if shift_edge_needs_defined(edge) {
            Out::Ub(UbKind::Poison)
        } else {
            Out::Val(None)
        };
    };
    // The amount, saturated: anything at least `w` behaves alike, except under `.mask`.
    let amount = n.to_u64();
    match amount {
        Some(k) if k < u64::from(w) => Out::Val(a.map(|x| shift_bits(op, w, x, k))),
        _ => match (edge, a) {
            (ShiftEdge::Ub, _) => Out::Ub(UbKind::Shift),
            (ShiftEdge::Trap, _) => Out::Trap(TrapReason::Shift),
            (_, None) => Out::Val(None),
            (ShiftEdge::Mask, Some(x)) => {
                let k = match n {
                    Bits::Small(k) => k % u64::from(w),
                    Bits::Big(k) => {
                        let r = k % BigUint::from(w);
                        u64::try_from(&r).unwrap_or(0)
                    }
                };
                Out::Val(Some(shift_bits(op, w, x, k)))
            }
            (_, Some(x)) => Out::Val(Some(shift_bits(op, w, x, u64::MAX))),
        },
    }
}

/// Integer comparison (Lean's `Sem.cmpBits`).
pub(crate) fn cmp_bits(p: Pred, w: u32, a: &Bits, b: &Bits) -> bool {
    use std::cmp::Ordering;
    let (u, s) = match (a, b) {
        (Bits::Small(x), Bits::Small(y)) => (x.cmp(y), sext64(w, *x).cmp(&sext64(w, *y))),
        (x, y) => (x.big().cmp(y.big()), x.to_int(w).cmp(&y.to_int(w))),
    };
    match p {
        Pred::Eq => u == Ordering::Equal,
        Pred::Ne => u != Ordering::Equal,
        Pred::Slt => s == Ordering::Less,
        Pred::Sle => s != Ordering::Greater,
        Pred::Sgt => s == Ordering::Greater,
        Pred::Sge => s != Ordering::Less,
        Pred::Ult => u == Ordering::Less,
        Pred::Ule => u != Ordering::Greater,
        Pred::Ugt => u == Ordering::Greater,
        Pred::Uge => u != Ordering::Less,
    }
}

/// `int.zext` to `v` bits (Lean's `setWidth`).
pub(crate) fn zext(v: u32, x: &Bits) -> Bits {
    Bits::of_nat(v, &x.to_nat())
}

/// `int.sext` from `w` to `v` bits.
pub(crate) fn sext(w: u32, v: u32, x: &Bits) -> Bits {
    match x {
        Bits::Small(x) if v <= 64 => Bits::Small(sext64(w, *x) as u64 & mask(v)),
        _ => Bits::of_int(v, &x.to_int(w)),
    }
}

/// `int.trunc` from `w` to `v` bits.
pub(crate) fn trunc(mode: TruncMode, w: u32, v: u32, x: &Bits) -> Option<Bits> {
    let r = Bits::of_nat(v, &x.to_nat());
    let ok = match mode {
        TruncMode::Wrap => true,
        TruncMode::Nsw => sext(v, w, &r) == *x,
        TruncMode::Nuw => zext(w, &r) == *x,
    };
    ok.then_some(r)
}

/// Bytes, least significant first, of a defined `w`-bit value (`w` a multiple of 8).
pub(crate) fn to_le_bytes(w: u32, x: &Bits, out: &mut Vec<u8>) {
    let n = (w / 8) as usize;
    match x {
        Bits::Small(x) => out.extend((0..n).map(|i| if i < 8 { (x >> (8 * i)) as u8 } else { 0 })),
        Bits::Big(x) => {
            let bytes = x.to_bytes_le();
            out.extend((0..n).map(|i| bytes.get(i).copied().unwrap_or(0)));
        }
    }
}

/// The `w`-bit value with these bytes, least significant first.
pub(crate) fn from_le_bytes(w: u32, bytes: &[u8]) -> Bits {
    if w <= 64 {
        let x = bytes
            .iter()
            .take(8)
            .enumerate()
            .fold(0u64, |acc, (i, &b)| acc | u64::from(b) << (8 * i));
        Bits::Small(x & mask(w))
    } else {
        Bits::of_nat(w, &BigUint::from_bytes_le(bytes))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every op agrees between the `u64` path and the big-integer path, by computing at width
    /// `w` both ways: a `w ≤ 64` value embedded in a wider computation is checked against the
    /// definitions directly instead, on small exhaustive widths.
    fn all(w: u32) -> Vec<Bits> {
        (0..1u64 << w).map(Bits::Small).collect()
    }

    fn val(o: &Out) -> Option<i128> {
        match o {
            Out::Val(Some(Bits::Small(x))) => Some(i128::from(*x)),
            _ => None,
        }
    }

    #[test]
    fn arith_matches_definitions_exhaustively() {
        for w in 1..=4 {
            let m = (1i128 << w) - 1;
            let (smin, smax) = (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1);
            for a in all(w) {
                for b in all(w) {
                    let (x, y) = (a.small() as i128, b.small() as i128);
                    let (sx, sy) = (sext64(w, x as u64) as i128, sext64(w, y as u64) as i128);
                    for op in [ArithOp::Add, ArithOp::Sub, ArithOp::Mul] {
                        let f = |p: i128, q: i128| match op {
                            ArithOp::Add => p + q,
                            ArithOp::Sub => p - q,
                            ArithOp::Mul => p * q,
                        };
                        let (ru, rs) = (f(x, y), f(sx, sy));
                        let wrap = ru.rem_euclid(m + 1);
                        let r = arith(op, Ovf::Wrap, w, Some(&a), Some(&b));
                        assert_eq!(val(&r), Some(wrap));
                        let r = arith(op, Ovf::Sat(true), w, Some(&a), Some(&b));
                        assert_eq!(val(&r), Some(rs.clamp(smin, smax).rem_euclid(m + 1)));
                        let r = arith(op, Ovf::Sat(false), w, Some(&a), Some(&b));
                        assert_eq!(val(&r), Some(ru.clamp(0, m)));
                        let r = arith(op, Ovf::Nsw, w, Some(&a), Some(&b));
                        assert_eq!(val(&r), (smin..=smax).contains(&rs).then_some(wrap));
                    }
                }
            }
        }
    }

    #[test]
    fn wide_paths_agree_with_narrow_ones() {
        // An op on 64-bit values, computed again at 72 bits on sign- or zero-extended inputs,
        // gives the 72-bit extension of the 64-bit result whenever no overflow is involved.
        let samples = [
            0u64,
            1,
            2,
            7,
            0x7fff_ffff_ffff_ffff,
            0x8000_0000_0000_0000,
            u64::MAX,
        ];
        for &x in &samples {
            for &y in &samples {
                let (a, b) = (Bits::Small(x), Bits::Small(y));
                let (wa, wb) = (zext(72, &a), zext(72, &b));
                for op in [DivOp::DivU, DivOp::RemU] {
                    let n = div(op, Edge::Total, Edge::Wrap, 64, Some(&a), Some(&b));
                    let wide = div(op, Edge::Total, Edge::Wrap, 72, Some(&wa), Some(&wb));
                    let Out::Val(Some(n)) = n else { panic!() };
                    assert_eq!(wide, Out::Val(Some(zext(72, &n))));
                }
                let (sa, sb) = (sext(64, 72, &a), sext(64, 72, &b));
                for p in [Pred::Slt, Pred::Ult, Pred::Sge, Pred::Eq] {
                    let u = cmp_bits(p, 64, &a, &b);
                    let wide = if matches!(p, Pred::Ult) {
                        cmp_bits(p, 72, &wa, &wb)
                    } else {
                        cmp_bits(p, 72, &sa, &sb)
                    };
                    assert_eq!(u, wide);
                }
            }
        }
    }
}
