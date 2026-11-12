//! FIR, the compiler IR, in Rust.
//!
//! The Lean semantics in `spec/` is the source of truth; this crate is checked against it. So
//! far it holds the IR, its text format, the verifier, and the interpreter: [`parse_module`]
//! reads text, [`Module::render`] prints the same canonical text as the Lean reference tool
//! (`fir-ref fmt`), [`verify_module`] accepts and rejects what `fir-ref check` does, with the
//! same messages, and [`interp::run`] runs a function and prints the same outcome as `fir-ref
//! run`. The tests check all of them on every file under `tests/`, and the interpreter also on
//! random programs.
//!
//! Each op is declared once, in `spec/Fir/Syntax.lean`; [`OpKind`] and the tables the parser,
//! printer, and verifier read ([`OpDecl`]) are generated from the declarations into
//! `src/generated/ops.rs`.
//!
//! Code is stored data-oriented ([`Body`]): per-function flat arrays, with ops, regions, and
//! values referring to each other by 32-bit index.

mod body;
mod decl;
pub mod interp;
mod ir;
mod lex;
#[path = "generated/ops.rs"]
#[rustfmt::skip]
mod ops;
mod parse;
mod print;
mod sem;
mod verify;

pub use body::{
    Body, HoleId, Int, IntId, OpId, Operand, OperandKind, Ops, RegionId, StrId, UseId, Uses,
    ValueDef, ValueId, ValueSpec,
};
pub use decl::{Check, Effect, Field, FieldTy, Imm, Item, OpDecl, Tier, TyE};
pub use ir::*;
pub use ops::op_kind;
pub use parse::parse_module;
pub use verify::{Hole, render_loc, verify_module};
