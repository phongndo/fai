//! The vocabulary of the `aarch64` dialect, mirroring `spec/Fir/AArch64Syntax.lean`: registers
//! (immediates of the `aarch64.*` ops) and the modifiers spelled in their names.

use std::fmt;

/// A register (Lean's `Reg`), packed in 32 bits. The top bit is the class: clear for
/// general-purpose registers, where `0..=30` are `x0`…`x30`, then `sp` and `xzr`; set for FP/SIMD
/// ones, where `0..=31` below it are `d0`…`d31`. Within either class the virtual registers start
/// at [`Reg::FIRST_VIRTUAL`] (`vN`, or `fvN` with the class bit). Instruction selection numbers
/// the virtual registers of both classes from one counter, so `vN` and `fvN` are never both in
/// the code it makes and [`Reg::virt_index`] alone identifies a virtual register.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Reg(pub u32);

impl Reg {
    pub const SP: Reg = Reg(31);
    pub const XZR: Reg = Reg(32);
    pub const FP: Reg = Reg(29);
    pub const LR: Reg = Reg(30);
    pub const FIRST_VIRTUAL: u32 = 64;
    /// The class bit: set for FP/SIMD registers.
    pub const FP_CLASS: u32 = 1 << 31;

    pub fn x(n: u32) -> Reg {
        debug_assert!(n <= 30);
        Reg(n)
    }

    /// The FP/SIMD register `dN` (`sN` at 32 bits).
    pub fn d(n: u32) -> Reg {
        debug_assert!(n <= 31);
        Reg(Self::FP_CLASS | n)
    }

    pub fn virt(n: u32) -> Reg {
        Reg(Self::FIRST_VIRTUAL + n)
    }

    /// The virtual FP register `fvN`.
    pub fn fvirt(n: u32) -> Reg {
        Reg(Self::FP_CLASS | (Self::FIRST_VIRTUAL + n))
    }

    /// The register without its class bit.
    fn low(self) -> u32 {
        self.0 & !Self::FP_CLASS
    }

    /// Whether it is an FP/SIMD register, physical or virtual.
    pub fn is_fp(self) -> bool {
        self.0 & Self::FP_CLASS != 0
    }

    /// `x0`…`x30`.
    pub fn is_gpr(self) -> bool {
        self.0 <= 30
    }

    /// `d0`…`d31`.
    pub fn is_fpr(self) -> bool {
        self.is_fp() && self.low() < 32
    }

    /// A physical FP register's number.
    pub fn fpr_index(self) -> u32 {
        self.low()
    }

    pub fn is_virtual(self) -> bool {
        self.low() >= Self::FIRST_VIRTUAL
    }

    /// The virtual register's number.
    pub fn virt_index(self) -> u32 {
        self.low() - Self::FIRST_VIRTUAL
    }

    /// Whether the encoding names a register (`FIR_INVALID`, all ones, doesn't).
    pub fn is_valid(self) -> bool {
        let l = self.low();
        let physical = if self.is_fp() { l < 32 } else { l <= 32 };
        physical || (l >= Self::FIRST_VIRTUAL && self.0 != u32::MAX)
    }

    /// A register's name: `x0`…`x30`, `sp`, `xzr`, `v` and a number, `d0`…`d31`, or `fv` and a
    /// number, without leading zeros.
    pub fn parse(s: &str) -> Option<Reg> {
        match s {
            "sp" => return Some(Reg::SP),
            "xzr" => return Some(Reg::XZR),
            _ => {}
        }
        let (c, digits) = match s.strip_prefix("fv") {
            Some(d) => ("fv", d),
            None => s.split_at_checked(1)?,
        };
        if digits.is_empty()
            || !digits.bytes().all(|b| b.is_ascii_digit())
            || (digits.len() > 1 && digits.starts_with('0'))
        {
            return None;
        }
        let n: u64 = digits.parse().ok()?;
        let max_virtual = u64::from(Self::FP_CLASS - 1 - Self::FIRST_VIRTUAL);
        match c {
            "x" if n <= 30 => Some(Reg(n as u32)),
            "d" if n <= 31 => Some(Reg::d(n as u32)),
            "v" if n < max_virtual => Some(Reg::virt(n as u32)),
            "fv" if n < max_virtual => Some(Reg::fvirt(n as u32)),
            _ => None,
        }
    }
}

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Reg::SP => f.write_str("sp"),
            Reg::XZR => f.write_str("xzr"),
            r if r.is_virtual() && r.is_fp() => write!(f, "fv{}", r.virt_index()),
            r if r.is_virtual() => write!(f, "v{}", r.virt_index()),
            r if r.is_fp() => write!(f, "d{}", r.low()),
            Reg(n) => write!(f, "x{n}"),
        }
    }
}

/// The operation size (ASL's `sf`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Sf {
    W,
    X,
}

impl Sf {
    pub fn bits(self) -> u32 {
        match self {
            Sf::W => 32,
            Sf::X => 64,
        }
    }
}

/// A condition on NZCV.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Cond {
    Eq,
    Ne,
    Hs,
    Lo,
    Mi,
    Pl,
    Vs,
    Vc,
    Hi,
    Ls,
    Ge,
    Lt,
    Gt,
    Le,
}

impl Cond {
    pub fn name(self) -> &'static str {
        match self {
            Cond::Eq => "eq",
            Cond::Ne => "ne",
            Cond::Hs => "hs",
            Cond::Lo => "lo",
            Cond::Mi => "mi",
            Cond::Pl => "pl",
            Cond::Vs => "vs",
            Cond::Vc => "vc",
            Cond::Hi => "hi",
            Cond::Ls => "ls",
            Cond::Ge => "ge",
            Cond::Lt => "lt",
            Cond::Gt => "gt",
            Cond::Le => "le",
        }
    }

    /// The condition that holds exactly when this one doesn't.
    pub fn invert(self) -> Cond {
        match self {
            Cond::Eq => Cond::Ne,
            Cond::Ne => Cond::Eq,
            Cond::Hs => Cond::Lo,
            Cond::Lo => Cond::Hs,
            Cond::Mi => Cond::Pl,
            Cond::Pl => Cond::Mi,
            Cond::Vs => Cond::Vc,
            Cond::Vc => Cond::Vs,
            Cond::Hi => Cond::Ls,
            Cond::Ls => Cond::Hi,
            Cond::Ge => Cond::Lt,
            Cond::Lt => Cond::Ge,
            Cond::Gt => Cond::Le,
            Cond::Le => Cond::Gt,
        }
    }

    /// Whether the condition holds for flags NZCV (ASL's `ConditionHolds`).
    pub fn holds(self, nzcv: u8) -> bool {
        let (n, z, c, v) = (nzcv & 8 != 0, nzcv & 4 != 0, nzcv & 2 != 0, nzcv & 1 != 0);
        match self {
            Cond::Eq => z,
            Cond::Ne => !z,
            Cond::Hs => c,
            Cond::Lo => !c,
            Cond::Mi => n,
            Cond::Pl => !n,
            Cond::Vs => v,
            Cond::Vc => !v,
            Cond::Hi => c && !z,
            Cond::Ls => !(c && !z),
            Cond::Ge => n == v,
            Cond::Lt => n != v,
            Cond::Gt => !z && n == v,
            Cond::Le => !(!z && n == v),
        }
    }
}

/// Three-register data processing (Lean's `AluOp`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum AluOp {
    Add,
    Adds,
    Sub,
    Subs,
    And,
    Ands,
    Orr,
    Eor,
    Bic,
    Lsl,
    Lsr,
    Asr,
    Mul,
    Sdiv,
    Udiv,
    Smulh,
    Umulh,
}

/// Data processing with an immediate (Lean's `AluImmOp`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum AluImmOp {
    Add,
    Adds,
    Sub,
    Subs,
    And,
    Ands,
    Orr,
    Eor,
}

/// Shifts by an immediate.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ShiftImmOp {
    Lsl,
    Lsr,
    Asr,
}

/// Wide-immediate moves.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum MovOp {
    Movz,
    Movn,
    Movk,
}

/// Conditional selects.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum CselOp {
    Csel,
    Csinc,
    Csinv,
    Csneg,
}

/// The size of a load or store.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum MemSize {
    B,
    H,
    W,
    X,
}

impl MemSize {
    pub fn bytes(self) -> u32 {
        match self {
            MemSize::B => 1,
            MemSize::H => 2,
            MemSize::W => 4,
            MemSize::X => 8,
        }
    }

    /// The size of an access of `n` bytes, if it is one.
    pub fn of_bytes(n: u64) -> Option<MemSize> {
        match n {
            1 => Some(MemSize::B),
            2 => Some(MemSize::H),
            4 => Some(MemSize::W),
            8 => Some(MemSize::X),
            _ => None,
        }
    }
}

/// The format of a scalar FP operation (Lean's `FSize`): `s` (`f32`) or `d` (`f64`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FSize {
    S,
    D,
}

impl FSize {
    pub fn bits(self) -> u32 {
        match self {
            FSize::S => 32,
            FSize::D => 64,
        }
    }

    pub fn of(f: crate::ir::FloatTy) -> FSize {
        match f {
            crate::ir::FloatTy::F32 => FSize::S,
            crate::ir::FloatTy::F64 => FSize::D,
        }
    }

    pub fn fty(self) -> crate::ir::FloatTy {
        match self {
            FSize::S => crate::ir::FloatTy::F32,
            FSize::D => crate::ir::FloatTy::F64,
        }
    }
}

/// Scalar FP arithmetic on two registers (Lean's `FAluOp`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FAluOp {
    Fadd,
    Fsub,
    Fmul,
    Fdiv,
}

/// Scalar FP operations on one register (Lean's `FUnaryOp`); `fmov` also moves bits between a
/// general-purpose register and an FP one.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FUnaryOp {
    Fmov,
    Fabs,
    Fneg,
    Fsqrt,
}

/// ASL's `VFPExpandImm` (Lean's `vfpExpandImm`, in `spec/Fir/AArch64.lean`): the float an 8-bit `fmov` immediate encodes.
pub fn vfp_expand_imm(fs: FSize, imm8: u32) -> u64 {
    let (e, m) = match fs {
        FSize::S => (8, 23),
        FSize::D => (11, 52),
    };
    let imm8 = u64::from(imm8);
    let b6 = (imm8 >> 6) & 1;
    let ones = if b6 == 1 {
        ((1u64 << (e - 3)) - 1) << 2
    } else {
        0
    };
    let exp = ((1 - b6) << (e - 1)) | ones | ((imm8 >> 4) & 3);
    ((imm8 >> 7) << (e + m)) | (exp << m) | ((imm8 & 15) << (m - 4))
}
