//! FIR's representation, the base every other compiler crate builds on.
//!
//! One op table serves HFIR, MFIR, and the LFIR `aarch64` dialect ([`OpKind`], [`OpDecl`],
//! generated from `spec/Fir/Syntax.lean` and `spec/Fir/AArch64Syntax.lean` into
//! `src/generated/`); a module's [`Layer`] says which ops it may use. Here are the types and the
//! data-oriented storage ([`Body`], [`Types`]), the text format ([`parse_module`],
//! [`Module::render`]), the verifier ([`verify_module`]), the builder ([`ModuleBuilder`]), the op
//! contracts ([`contract`]), FIR's float semantics ([`float`]), and the vocabulary of the
//! `aarch64` dialect and AAPCS64 ([`dialect::aarch64`]).
//!
//! This is an internal crate of the fai workspace, not a stable interface: its modules are public
//! so the other compiler crates can share them. Programs use the `fir` crate, which re-exports
//! what is supported.

#![forbid(unsafe_code)]

pub mod body;
pub mod builder;
#[path = "generated/builder.rs"]
#[rustfmt::skip]
mod builder_ops;
pub mod contract;
pub mod decl;
/// What the one op table needs from the `aarch64` LFIR dialect: its registers and the modifiers
/// its op names spell ([`dialect::aarch64::syntax`]), and AAPCS64's placement of values
/// ([`dialect::aarch64::abi`]), by which the machine model runs calls. Both mirror Lean
/// (`spec/Fir/AArch64Syntax.lean`, `spec/Fir/AArch64Abi.lean`); the compiler for the target is
/// the `fai-target-aarch64` crate.
pub mod dialect {
    pub mod aarch64 {
        pub mod abi;
        pub mod syntax;
    }
}
#[path = "generated/contracts.rs"]
#[rustfmt::skip]
mod generated_contracts;
pub mod float;
pub mod globals;
pub mod ir;
pub mod lex;
#[path = "generated/ops.rs"]
#[rustfmt::skip]
pub mod ops;
pub mod parse;
pub mod print;
pub mod sem;
pub mod types;
pub mod verify;

pub use body::{
    Body, Case, CasesId, HoleId, Int, IntId, OpId, Operand, OperandKind, Ops, RegionId, StrId,
    Succ, SuccId, UseId, Uses, ValueDef, ValueId, ValueSpec,
};
pub use builder::{
    BuildError, FactArg, FuncBuilder, FuncRef, GlobalRef, InsertPoint, IntImm, ModuleBuilder,
    Results, SwitchCase, Target, Values,
};
pub use decl::{Check, Effect, Field, FieldTy, Imm, Item, Layer, Layers, OpDecl, Tier, TyE};
pub use globals::Run;
pub use ir::*;
pub use ops::{TARGETS, op_kind};
pub use parse::parse_module;
pub use sem::TrapReason;
pub use types::align_up;
pub use verify::{Hole, render_loc, verify_module};
