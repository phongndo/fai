//! The shape of FIR programs, mirroring `spec/Fir/Syntax.lean`.
//!
//! Everything is an op: an op has a kind, typed results, operands, nested regions, and a source
//! location. Ops live in a per-function arena ([`crate::Body`]); this module defines the values
//! stored in it. They are all small `Copy` values: strings and integers are ids into the arena's
//! side tables ([`StrId`], [`IntId`]), so an op owns no heap memory.

use std::fmt;

use crate::body::{IntId, StrId};

/// A source location, `@line:col`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Loc {
    pub line: u32,
    pub col: u32,
}

/// A type: signless integers `iN`, pointers, and byte types `bN`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Ty {
    Int(u32),
    Ptr,
    Byte(u32),
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Int(w) => write!(f, "i{w}"),
            Ty::Ptr => f.write_str("ptr"),
            Ty::Byte(w) => write!(f, "b{w}"),
        }
    }
}

/// A memory space's sizes, in bits: how much memory a pointer takes, and the address (index)
/// size used by `ptr.addr`, offsets, and allocation sizes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SpaceCfg {
    pub ptr_bits: u32,
    pub addr_bits: u32,
}

impl Default for SpaceCfg {
    fn default() -> Self {
        SpaceCfg {
            ptr_bits: 64,
            addr_bits: 64,
        }
    }
}

/// How much a fact is trusted. A violated fact is UB whatever the tag; the tag says how the
/// compiler treats it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Trust {
    Assume,
    Check,
    Proved,
}

impl Trust {
    pub fn name(self) -> &'static str {
        match self {
            Trust::Assume => "assume",
            Trust::Check => "check",
            Trust::Proved => "proved",
        }
    }
}

/// A claim about a value. Facts constrain defined values only; `poison` passes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Fact {
    /// Signed range, inclusive.
    RangeS(IntId, IntId),
    /// Unsigned range, inclusive.
    RangeU(IntId, IntId),
    NonNull,
    Align(u64),
    NoAlias,
    ReadOnly,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct TrustedFact {
    pub fact: Fact,
    pub trust: Trust,
}

/// Overflow behavior of `int.add`, `int.sub`, and `int.mul`. `bool` fields are "signed".
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Ovf {
    Wrap,
    Nsw,
    Nuw,
    NswNuw,
    Trap(bool),
    Sat(bool),
    Ub(bool),
}

/// Edge-case behaviors of division and remainder.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Edge {
    Ub,
    Trap,
    Total,
    Wrap,
}

/// Behavior of shifts when the amount is at least the bit width.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ShiftEdge {
    Ub,
    Trap,
    Mask,
    Total,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum TruncMode {
    Wrap,
    Nsw,
    Nuw,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Pred {
    Eq,
    Ne,
    Slt,
    Sle,
    Sgt,
    Sge,
    Ult,
    Ule,
    Ugt,
    Uge,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BitOp {
    And,
    Or,
    Xor,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum DivOp {
    DivS,
    DivU,
    RemS,
    RemU,
}

impl DivOp {
    pub fn signed(self) -> bool {
        matches!(self, DivOp::DivS | DivOp::RemS)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ShiftOp {
    Shl,
    ShrU,
    ShrS,
}

/// What `mem.alloc` does when allocation fails.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum AllocFail {
    Null,
    Trap,
}

/// What an op does. Mirrors `Fir.OpKind`. Alignments are 32-bit (Lean's are unbounded).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum OpKind {
    Const(IntId),
    Poison,
    Freeze,
    Copy,
    Select,
    Arith(ArithOp, Ovf),
    Bit(BitOp),
    Div(DivOp, Edge, Edge),
    Shift(ShiftOp, ShiftEdge),
    Cmp(Pred),
    Zext,
    Sext,
    Trunc(TruncMode),
    MemStack {
        size: u64,
        align: u32,
    },
    MemAlloc {
        fail: AllocFail,
        family: StrId,
        align: u32,
    },
    MemFree {
        family: StrId,
    },
    Load {
        align: u32,
    },
    Store {
        ty: Ty,
        align: u32,
    },
    PtrOffset {
        inbounds: bool,
    },
    PtrAddr,
    PtrExpose,
    PtrFromExposed,
    PtrWithAddr,
    PtrNull,
    PtrCmp(Pred),
    Call {
        callee: StrId,
    },
    If,
    Loop {
        progress: bool,
    },
    Yield,
    Break,
    Continue,
    Ret,
}

impl OpKind {
    pub fn is_terminator(&self) -> bool {
        matches!(
            self,
            OpKind::Yield | OpKind::Break | OpKind::Continue | OpKind::Ret
        )
    }
}

/// A module: functions plus the default memory space.
#[derive(Clone, Debug, Default)]
pub struct Module {
    pub space: SpaceCfg,
    pub funcs: Vec<Func>,
}

/// A function. Its parameters are the parameters of its body's entry region.
#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub rets: Vec<Ty>,
    pub file: Option<String>,
    pub body: crate::Body,
}
