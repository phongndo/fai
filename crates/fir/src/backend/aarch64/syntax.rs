//! The vocabulary of the `aarch64` dialect, mirroring `spec/Fir/AArch64Syntax.lean`: registers
//! (immediates of the `aarch64.*` ops) and the modifiers spelled in their names.

use std::fmt;

/// A register (Lean's `Reg`): `x0`…`x30`, `sp`, `xzr`, or a virtual register `vN`, packed in 32
/// bits: `0..=30` are `x0`…`x30`, then `sp`, `xzr`, and the virtual registers from
/// [`Reg::FIRST_VIRTUAL`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Reg(pub u32);

impl Reg {
    pub const SP: Reg = Reg(31);
    pub const XZR: Reg = Reg(32);
    pub const FP: Reg = Reg(29);
    pub const LR: Reg = Reg(30);
    pub const FIRST_VIRTUAL: u32 = 64;

    pub fn x(n: u32) -> Reg {
        debug_assert!(n <= 30);
        Reg(n)
    }

    pub fn virt(n: u32) -> Reg {
        Reg(Self::FIRST_VIRTUAL + n)
    }

    /// `x0`…`x30`.
    pub fn is_gpr(self) -> bool {
        self.0 <= 30
    }

    pub fn is_virtual(self) -> bool {
        self.0 >= Self::FIRST_VIRTUAL
    }

    /// The virtual register's number.
    pub fn virt_index(self) -> u32 {
        self.0 - Self::FIRST_VIRTUAL
    }

    /// A register's name: `x0`…`x30`, `sp`, `xzr`, or `v` and a number without leading zeros.
    pub fn parse(s: &str) -> Option<Reg> {
        match s {
            "sp" => return Some(Reg::SP),
            "xzr" => return Some(Reg::XZR),
            _ => {}
        }
        let (c, digits) = s.split_at_checked(1)?;
        if digits.is_empty()
            || !digits.bytes().all(|b| b.is_ascii_digit())
            || (digits.len() > 1 && digits.starts_with('0'))
        {
            return None;
        }
        let n: u64 = digits.parse().ok()?;
        match c {
            "x" if n <= 30 => Some(Reg(n as u32)),
            "v" if n < u64::from(u32::MAX - Self::FIRST_VIRTUAL) => {
                Some(Reg::virt(n as u32))
            }
            _ => None,
        }
    }
}

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Reg::SP => f.write_str("sp"),
            Reg::XZR => f.write_str("xzr"),
            r if r.is_virtual() => write!(f, "v{}", r.virt_index()),
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
