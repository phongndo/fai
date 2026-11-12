//! The shape of FIR programs, mirroring `spec/Fir/Syntax.lean`.
//!
//! Everything is an op: an op has a kind, typed results, operands, nested regions, and a source
//! location. Ops live in a per-function arena ([`crate::Body`]); this module defines the values
//! stored in it. They are all small `Copy` values: strings and integers are ids into the arena's
//! side tables ([`StrId`], [`IntId`]), so an op owns no heap memory.

use std::fmt;

pub use crate::backend::aarch64::syntax::{
    AluImmOp, AluOp, Cond, CselOp, FAluOp, FSize, FUnaryOp, MemSize, MovOp, Reg, Sf, ShiftImmOp,
};
use crate::body::IntId;
pub use crate::globals::{Globals, Init};
pub use crate::ops::OpKind;
pub use crate::sem::TrapReason;
pub use crate::types::{Policy, Shape, TyId, Types};

/// A source location, `@line:col`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Loc {
    pub line: u32,
    pub col: u32,
}

/// A type. The scalar value types are signless integers `iN`, pointers, byte types `bN`, and
/// floats (`f32`, `f64`);
/// `slice` is HFIR's pointer and length; structs, arrays, unions, and function types are ids into
/// a [`Types`] table (see `types.rs`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Ty {
    Int(u32),
    Ptr,
    Byte(u32),
    Slice,
    Float(FloatTy),
    Agg(TyId),
}

impl Ty {
    /// Whether this is a scalar value type, the only types values have outside HFIR (Lean's
    /// `Ty.isValue`).
    pub fn is_value(self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Ptr | Ty::Byte(_) | Ty::Float(_))
    }

    pub fn is_float(self) -> bool {
        matches!(self, Ty::Float(_))
    }
}

/// The float types (Lean's `FloatTy`): IEEE 754 binary32 and binary64.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FloatTy {
    F32,
    F64,
}

impl FloatTy {
    /// The width in bits.
    pub fn width(self) -> u32 {
        match self {
            FloatTy::F32 => 32,
            FloatTy::F64 => 64,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            FloatTy::F32 => "f32",
            FloatTy::F64 => "f64",
        }
    }
}

/// Value types as text. A [`Ty::Agg`] needs its table to print ([`Types::write`]); here it shows
/// only its id.
impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Int(w) => write!(f, "i{w}"),
            Ty::Ptr => f.write_str("ptr"),
            Ty::Byte(w) => write!(f, "b{w}"),
            Ty::Slice => f.write_str("slice"),
            Ty::Float(t) => f.write_str(t.name()),
            Ty::Agg(id) => write!(f, "type#{}", id.index()),
        }
    }
}

/// The default integer alignments, `(width in bits, alignment in bytes)`: x86-64 System V.
pub const DEFAULT_INTS: [(u32, u32); 5] = [(8, 1), (16, 2), (32, 4), (64, 8), (128, 16)];

/// A memory space's data layout (Lean's `SpaceCfg`): how much memory a pointer takes and the
/// address (index) size used by `ptr.addr`, offsets, and allocation sizes, in bits; the pointer
/// alignment; and the integer alignments, `(width in bits, alignment in bytes)` by increasing
/// width.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SpaceCfg {
    pub ptr_bits: u32,
    pub addr_bits: u32,
    pub ptr_align: u32,
    pub ints: Vec<(u32, u32)>,
}

impl Default for SpaceCfg {
    fn default() -> Self {
        SpaceCfg {
            ptr_bits: 64,
            addr_bits: 64,
            ptr_align: 8,
            ints: DEFAULT_INTS.to_vec(),
        }
    }
}

impl SpaceCfg {
    /// A pointer's alignment when the `memspace` line doesn't give one: the largest power of two
    /// at most the pointer size in bytes, and at least 1.
    pub fn natural_align(ptr_bits: u32) -> u32 {
        let bytes = ptr_bits / 8;
        if bytes == 0 { 1 } else { 1 << bytes.ilog2() }
    }

    /// The alignment of `iN` and `bN`: the entry for the smallest width at least `w`, or else the
    /// largest's.
    pub fn int_align(&self, w: u32) -> u32 {
        match self.ints.iter().find(|e| e.0 >= w) {
            Some(e) => e.1,
            None => self.ints.last().map_or(1, |e| e.1),
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

/// `float.add`, `float.sub`, `float.mul`, `float.div`, `float.copysign`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Copysign,
}

/// `float.neg`, `float.abs`, `float.sqrt`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FUnOp {
    Neg,
    Abs,
    Sqrt,
}

/// Float comparison predicates (Lean's `FPred`): ordered (`o…`, false on NaN), unordered (`u…`,
/// true on NaN), `ord`, and `uno`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FPred {
    Oeq,
    One,
    Olt,
    Ole,
    Ogt,
    Oge,
    Ord,
    Ueq,
    Une,
    Ult,
    Ule,
    Ugt,
    Uge,
    Uno,
}

/// What `float.to_int` does with NaN and out-of-range inputs.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum CvtEdge {
    Ub,
    Sat,
    Trap,
}

/// What `mem.alloc` does when allocation fails.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum AllocFail {
    Null,
    Trap,
}

/// Memory an external function's effects can name (Lean's `MemClass`): the allocations its
/// pointer arguments point into, every exposed allocation, or the module's globals.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum MemClass {
    Args,
    Exposed,
    Globals,
}

impl MemClass {
    pub fn name(self) -> &'static str {
        match self {
            MemClass::Args => "args",
            MemClass::Exposed => "exposed",
            MemClass::Globals => "globals",
        }
    }
}

/// What an external function may do (Lean's `ExtEffect`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ExtEffect {
    Read(MemClass),
    Write(MemClass),
    Alloc,
    Free,
    Trap,
    Diverge,
    Unwind,
}

impl fmt::Display for ExtEffect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExtEffect::Read(m) => write!(f, "read({})", m.name()),
            ExtEffect::Write(m) => write!(f, "write({})", m.name()),
            ExtEffect::Alloc => f.write_str("alloc"),
            ExtEffect::Free => f.write_str("free"),
            ExtEffect::Trap => f.write_str("trap"),
            ExtEffect::Diverge => f.write_str("diverge"),
            ExtEffect::Unwind => f.write_str("unwind"),
        }
    }
}

/// `extern func @puts(ptr) -> i32 effects[read(args)] assume`: a function outside the module.
/// Its types are in the module's [`Globals::types`] table.
#[derive(Clone, Debug)]
pub struct Extern {
    pub name: String,
    pub params: Vec<Ty>,
    pub rets: Vec<Ty>,
    pub effects: Vec<ExtEffect>,
    pub trust: Trust,
}

impl Extern {
    pub fn has(&self, e: ExtEffect) -> bool {
        self.effects.contains(&e)
    }
}

/// A module: its layer, the default memory space, globals, external functions, and functions.
#[derive(Clone, Debug, Default)]
pub struct Module {
    pub layer: crate::Layer,
    pub space: SpaceCfg,
    pub globals: Globals,
    pub externs: Vec<Extern>,
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
