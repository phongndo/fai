//! AAPCS64 as FIR uses it (decision: Calling convention), mirroring `argLocs` and `resRegs` in
//! `spec/Fir/AArch64Machine.lean`: where a call's arguments and results travel. Instruction
//! selection, register allocation, and the LFIR machine all ask here.

use crate::ir::{Reg, Ty};

/// Where an argument travels: a register, or the stack slot this many bytes above `sp`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ArgLoc {
    Reg(Reg),
    Stack(u32),
}

/// Where the arguments of a call with parameter types `ps` go: integers and pointers in
/// `x0`…`x7` and floats in `d0`…`d7` (`s0`…`s7`), counted separately and in order, and the rest
/// in 8-byte stack slots from `sp`, in order (Lean's `argLocs`).
pub fn arg_locs(ps: &[Ty]) -> Vec<ArgLoc> {
    let (mut g, mut f, mut s) = (0, 0, 0);
    ps.iter()
        .map(|t| {
            let (count, reg): (&mut u32, fn(u32) -> Reg) = if t.is_float() {
                (&mut f, Reg::d)
            } else {
                (&mut g, Reg::x)
            };
            if *count < 8 {
                *count += 1;
                ArgLoc::Reg(reg(*count - 1))
            } else {
                s += 1;
                ArgLoc::Stack(8 * (s - 1))
            }
        })
        .collect()
}

/// How many stack slots the arguments take (Lean's `stackSlots`).
pub fn stack_slots(ps: &[Ty]) -> u32 {
    arg_locs(ps)
        .iter()
        .filter(|l| matches!(l, ArgLoc::Stack(_)))
        .count() as u32
}

/// The registers one or two results go in (Lean's `resRegs`): `d0`, `d1` (`s0`, `s1`) when all
/// are floats of one format, otherwise `x0`, `x1`, a float as its bits; `None` for three or
/// more, which go in 8-byte slots at the address the caller passes in `x8`. It is how C returns
/// a struct of the results as 8-byte fields: a homogeneous float aggregate in FP registers, any
/// other 16 bytes in `x0` and `x1`.
pub fn res_regs(rets: &[Ty]) -> Option<Vec<Reg>> {
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

/// The FP registers a call may change: `d0`…`d7` and `d16`…`d31` (of `d8`…`d15` only the high
/// 64 bits, which FIR never holds anything in).
pub const FP_CALLER_SAVED: [u32; 24] = [
    0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::FloatTy;

    #[test]
    fn locations() {
        let (i, d, s) = (
            Ty::Int(32),
            Ty::Float(FloatTy::F64),
            Ty::Float(FloatTy::F32),
        );
        assert_eq!(
            arg_locs(&[i, d, Ty::Ptr]),
            [Reg::x(0), Reg::d(0), Reg::x(1)].map(ArgLoc::Reg)
        );
        let mut ps = vec![s; 9];
        ps.extend([i; 10]);
        assert_eq!(stack_slots(&ps), 3);
        assert_eq!(arg_locs(&ps)[8], ArgLoc::Stack(0));
        assert_eq!(arg_locs(&ps)[18], ArgLoc::Stack(16));
        assert_eq!(res_regs(&[s, s]), Some(vec![Reg::d(0), Reg::d(1)]));
        assert_eq!(res_regs(&[s, d]), Some(vec![Reg::x(0), Reg::x(1)]));
        assert_eq!(res_regs(&[i, d, d]), None);
    }
}
