//! AAPCS64 as FIR uses it (decisions: Calling convention, C ABI for aggregates), mirroring
//! `spec/Fir/AArch64Abi.lean`: where a call's arguments and results travel. Instruction
//! selection, register allocation, and the LFIR machine all ask here.
//!
//! A scalar travels in one register of its class or an 8-byte stack slot. A composite (a struct
//! or an array, [`Types::is_composite`]) travels as AAPCS64 says (§6.8.2): nothing if empty; as
//! a homogeneous float aggregate (one to four floats of one format, no padding) in consecutive FP
//! registers; up to 16 bytes as its bytes in one or two `x` registers (an even first one if it is
//! 16-byte aligned); larger as a pointer to a copy the caller makes. A composite that doesn't fit
//! the registers left goes on the stack as its bytes and closes its class's registers for the
//! arguments after it.

use crate::ir::{FloatTy, Reg, SpaceCfg, Ty};
use crate::types::{Shape, Types, align_up};

/// How AAPCS64 passes a value of some type (Lean's `PassKind`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PassKind {
    /// An integer, bytes, or a pointer.
    Gp,
    /// A float.
    Fp,
    /// An HFA of this many floats of one format.
    Hfa(FloatTy, u32),
    /// A composite of this many 8-byte words (1 to 16 bytes), 16-byte aligned if `true`.
    Words(u32, bool),
    /// A composite larger than 16 bytes, passed as a pointer to a copy.
    Ref,
    /// An empty composite: nothing.
    Nothing,
}

/// Where an argument travels (Lean's `ArgLoc`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ArgLoc {
    /// A scalar in a register.
    Reg(Reg),
    /// A scalar in the 8-byte stack slot this many bytes above `sp`.
    Stack(u32),
    /// A composite's pieces in this many consecutive registers from the first.
    Regs(Reg, u32),
    /// A composite's bytes this many bytes above `sp`.
    Mem(u32),
    /// A pointer to a copy of the composite, in a register.
    RefReg(Reg),
    /// A pointer to a copy of the composite, in the stack slot at this offset.
    RefStack(u32),
    /// Nothing (an empty composite).
    Nothing,
}

impl ArgLoc {
    /// The registers it takes.
    pub fn regs(self) -> impl Iterator<Item = Reg> {
        let (first, n) = match self {
            ArgLoc::Reg(r) | ArgLoc::RefReg(r) => (Some(r), 1),
            ArgLoc::Regs(r, n) => (Some(r), n),
            _ => (None, 0),
        };
        (0..n).filter_map(move |i| first.map(|r| nth(r, i)))
    }
}

/// The register `i` after `r`, of its class.
pub fn nth(r: Reg, i: u32) -> Reg {
    if r.is_fp() {
        Reg::d(r.fpr_index() + i)
    } else {
        Reg::x(r.0 + i)
    }
}

/// Whether a type has a zero-length array anywhere in it, which keeps it from being an HFA
/// (Lean's `Ty.hasEmptyArray`; GCC's rule).
fn has_empty_array(types: &Types, t: Ty) -> bool {
    match types.shape_of(t) {
        Some(Shape::Struct(_, fs)) => fs.iter().any(|&f| has_empty_array(types, f)),
        Some(Shape::Array(n, e)) => n == 0 || has_empty_array(types, e),
        _ => false,
    }
}

/// The format and member count of an HFA (Lean's `hfaOf?`).
pub fn hfa_of(types: &Types, sp: &SpaceCfg, t: Ty) -> Option<(FloatTy, u32)> {
    if has_empty_array(types, t) {
        return None;
    }
    let mut leaves = Vec::new();
    types.leaves(sp, t, 0, &mut leaves);
    let Some(&(_, Ty::Float(f))) = leaves.first() else {
        return None;
    };
    let n = leaves.len() as u128;
    let b = u128::from(f.width() / 8);
    let ok = n <= 4
        && types.size(sp, t) == n * b
        && leaves
            .iter()
            .enumerate()
            .all(|(i, &(o, l))| l == Ty::Float(f) && o == i as u128 * b);
    ok.then_some((f, n as u32))
}

/// How AAPCS64 passes a value of type `t` (Lean's `passKind`).
pub fn pass_kind(types: &Types, sp: &SpaceCfg, t: Ty) -> PassKind {
    if types.is_composite(t) {
        let size = types.size(sp, t);
        if size == 0 {
            PassKind::Nothing
        } else if let Some((f, n)) = hfa_of(types, sp, t) {
            PassKind::Hfa(f, n)
        } else if size <= 16 {
            PassKind::Words(size.div_ceil(8) as u32, types.align(sp, t) >= 16)
        } else {
            PassKind::Ref
        }
    } else if t.is_float() {
        PassKind::Fp
    } else {
        PassKind::Gp
    }
}

/// Where the arguments of a call with parameter types `ps` go, and how many bytes of stack they
/// take (Lean's `argLocs` and `argStack`).
pub fn arg_locs(types: &Types, sp: &SpaceCfg, ps: &[Ty]) -> (Vec<ArgLoc>, u32) {
    let (locs, state) = arg_state(types, sp, ps);
    (locs, state.2)
}

/// [`arg_locs`], with NGRN, NSRN, and NSAA after the arguments: how many `x` and FP registers
/// they close, and how many bytes of stack they take (what a variadic function's `va_list`
/// starts from).
pub fn arg_state(types: &Types, sp: &SpaceCfg, ps: &[Ty]) -> (Vec<ArgLoc>, (u32, u32, u32)) {
    let (mut g, mut f, mut s) = (0u32, 0u32, 0u32);
    let locs = ps
        .iter()
        .map(|&t| match pass_kind(types, sp, t) {
            PassKind::Gp => {
                if g < 8 {
                    g += 1;
                    ArgLoc::Reg(Reg::x(g - 1))
                } else {
                    s += 8;
                    ArgLoc::Stack(s - 8)
                }
            }
            PassKind::Fp => {
                if f < 8 {
                    f += 1;
                    ArgLoc::Reg(Reg::d(f - 1))
                } else {
                    s += 8;
                    ArgLoc::Stack(s - 8)
                }
            }
            PassKind::Hfa(fl, n) => {
                if f + n <= 8 {
                    f += n;
                    ArgLoc::Regs(Reg::d(f - n), n)
                } else {
                    f = 8;
                    let at = s;
                    s += (n * fl.width() / 8).next_multiple_of(8);
                    ArgLoc::Mem(at)
                }
            }
            PassKind::Words(n, even) => {
                if even {
                    g = g.next_multiple_of(2);
                }
                if g + n <= 8 {
                    g += n;
                    ArgLoc::Regs(Reg::x(g - n), n)
                } else {
                    g = 8;
                    let at = align_up(u128::from(s), if even { 16 } else { 8 }) as u32;
                    s = at + 8 * n;
                    ArgLoc::Mem(at)
                }
            }
            PassKind::Ref => {
                if g < 8 {
                    g += 1;
                    ArgLoc::RefReg(Reg::x(g - 1))
                } else {
                    s += 8;
                    ArgLoc::RefStack(s - 8)
                }
            }
            PassKind::Nothing => ArgLoc::Nothing,
        })
        .collect();
    (locs, (g, f, s))
}

/// The registers a call's results come back in (Lean's `resRegs`): a composite's where it would
/// be passed first; one or two scalars in `d0`, `d1` (`s0`, `s1`) when all are floats of one
/// format, otherwise in `x0`, `x1`, a float as its bits. `None` when they come back in memory at
/// the address the caller passes in `x8`: a composite over 16 bytes (its bytes), or three or
/// more scalars (8-byte slots). It is how C returns a struct, and the scalar rule how C returns a
/// struct of the results as 8-byte fields.
pub fn res_regs(types: &Types, sp: &SpaceCfg, rets: &[Ty]) -> Option<Vec<Reg>> {
    if let [t] = *rets
        && types.is_composite(t)
    {
        return match arg_locs(types, sp, &[t]).0[0] {
            ArgLoc::Regs(r, n) => Some((0..n).map(|i| nth(r, i)).collect()),
            ArgLoc::Nothing => Some(Vec::new()),
            _ => None,
        };
    }
    if rets.len() > 2 {
        return None;
    }
    let fp = rets.first().is_some_and(|t| t.is_float()) && rets.iter().all(|t| *t == rets[0]);
    Some(
        (0..rets.len() as u32)
            .map(|i| if fp { Reg::d(i) } else { Reg::x(i) })
            .collect(),
    )
}

/// The registers a call reads for its arguments and writes for its results.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CallShape {
    /// The argument registers.
    pub args: Vec<Reg>,
    /// The result registers (none when the results go through memory).
    pub rets: Vec<Reg>,
    /// Whether the results go in the area `x8` points to.
    pub area: bool,
}

impl CallShape {
    /// A call with these parameter and result types, of table `types`.
    pub fn of(types: &Types, sp: &SpaceCfg, ps: &[Ty], rets: &[Ty]) -> CallShape {
        let args = arg_locs(types, sp, ps)
            .0
            .into_iter()
            .flat_map(ArgLoc::regs)
            .collect();
        match res_regs(types, sp, rets) {
            Some(rets) => CallShape {
                args,
                rets,
                area: false,
            },
            None => CallShape {
                args,
                rets: Vec::new(),
                area: true,
            },
        }
    }
}

/// A composite's bytes split into the pieces its registers hold (Lean's `pieces`): 8-byte words
/// (the last one shorter), or an HFA's members. Each piece is `(offset, size)`.
pub fn pieces(k: PassKind, size: u32) -> Vec<(u32, u32)> {
    let (w, n) = match k {
        PassKind::Words(n, _) => (8, n),
        PassKind::Hfa(f, n) => (f.width() / 8, n),
        _ => return Vec::new(),
    };
    (0..n)
        .map(|i| {
            let o = (w * i).min(size);
            (o, w.min(size - o))
        })
        .collect()
}

/// The FP registers a call may change: `d0`…`d7` and `d16`…`d31` (of `d8`…`d15` only the high
/// 64 bits, which FIR never holds anything in).
pub const FP_CALLER_SAVED: [u32; 24] = [
    0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Policy;

    #[test]
    fn locations() {
        let types = Types::new();
        let sp = SpaceCfg::default();
        let (i, d, s) = (
            Ty::Int(32),
            Ty::Float(FloatTy::F64),
            Ty::Float(FloatTy::F32),
        );
        assert_eq!(
            arg_locs(&types, &sp, &[i, d, Ty::Ptr]).0,
            [Reg::x(0), Reg::d(0), Reg::x(1)].map(ArgLoc::Reg)
        );
        let mut ps = vec![s; 9];
        ps.extend([i; 10]);
        assert_eq!(arg_locs(&types, &sp, &ps).1, 24);
        assert_eq!(arg_locs(&types, &sp, &ps).0[8], ArgLoc::Stack(0));
        assert_eq!(arg_locs(&types, &sp, &ps).0[18], ArgLoc::Stack(16));
        assert_eq!(
            res_regs(&types, &sp, &[s, s]),
            Some(vec![Reg::d(0), Reg::d(1)])
        );
        assert_eq!(
            res_regs(&types, &sp, &[s, d]),
            Some(vec![Reg::x(0), Reg::x(1)])
        );
        assert_eq!(res_regs(&types, &sp, &[i, d, d]), None);
    }

    /// The same examples as `spec/Fir/AArch64Abi.lean`'s.
    #[test]
    fn composites() {
        let mut types = Types::new();
        let sp = SpaceCfg::default();
        let (f32_, f64_) = (Ty::Float(FloatTy::F32), Ty::Float(FloatTy::F64));
        let s2 = types.structure(Policy::C, &[Ty::Int(32), Ty::Int(32)]);
        let a2 = types.array(2, f32_);
        let hfa3 = types.structure(Policy::C, &[f32_, a2]);
        let big = types.structure(Policy::C, &[Ty::Int(64), Ty::Int(64), Ty::Int(8)]);
        let z = types.array(0, Ty::Int(128));
        let al16 = types.structure(Policy::C, &[z, Ty::Int(64)]);
        let mixed = types.structure(Policy::C, &[f32_, f64_]);
        let packed = types.structure(Policy::Packed, &[f32_, f32_]);
        let empty = types.structure(Policy::C, &[]);
        let pair = types.structure(Policy::C, &[Ty::Int(64), Ty::Int(64)]);
        let k = |t| pass_kind(&types, &sp, t);
        assert_eq!(k(s2), PassKind::Words(1, false));
        assert_eq!(k(hfa3), PassKind::Hfa(FloatTy::F32, 3));
        assert_eq!(k(mixed), PassKind::Words(2, false));
        assert_eq!(k(packed), PassKind::Hfa(FloatTy::F32, 2));
        assert_eq!(k(big), PassKind::Ref);
        assert_eq!(k(al16), PassKind::Words(2, true));
        assert_eq!(k(empty), PassKind::Nothing);
        let locs = |ps: &[Ty]| arg_locs(&types, &sp, ps).0;
        let mut ps = vec![Ty::Ptr; 7];
        ps.extend([pair, Ty::Int(8)]);
        let mut want: Vec<ArgLoc> = (0..7).map(|i| ArgLoc::Reg(Reg::x(i))).collect();
        want.extend([ArgLoc::Mem(0), ArgLoc::Stack(16)]);
        assert_eq!(locs(&ps), want);
        assert_eq!(
            locs(&[Ty::Int(8), al16, Ty::Int(8)]),
            [
                ArgLoc::Reg(Reg::x(0)),
                ArgLoc::Regs(Reg::x(2), 2),
                ArgLoc::Reg(Reg::x(4))
            ]
        );
        let mut ps = vec![f64_; 6];
        ps.extend([hfa3, f32_]);
        let mut want: Vec<ArgLoc> = (0..6).map(|i| ArgLoc::Reg(Reg::d(i))).collect();
        want.extend([ArgLoc::Mem(0), ArgLoc::Stack(16)]);
        assert_eq!(locs(&ps), want);
        assert_eq!(
            locs(&[big, big]),
            [ArgLoc::RefReg(Reg::x(0)), ArgLoc::RefReg(Reg::x(1))]
        );
        let rr = |rs: &[Ty]| res_regs(&types, &sp, rs);
        assert_eq!(rr(&[hfa3]), Some(vec![Reg::d(0), Reg::d(1), Reg::d(2)]));
        assert_eq!(rr(&[s2]), Some(vec![Reg::x(0)]));
        assert_eq!(rr(&[big]), None);
        assert_eq!(pieces(PassKind::Words(2, false), 12), [(0, 8), (8, 4)]);
        assert_eq!(
            pieces(PassKind::Hfa(FloatTy::F32, 3), 12),
            [(0, 4), (4, 4), (8, 4)]
        );
    }
}
