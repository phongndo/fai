//! FIR, the compiler IR, in Rust.
//!
//! The Lean semantics in `spec/` is the source of truth; this crate is checked against it. So
//! far it holds the IR, its text format, and the verifier: [`parse_module`] reads text,
//! [`Module::render`] prints the same canonical text as the Lean reference tool (`fir-ref fmt`),
//! and [`verify_module`] accepts and rejects what `fir-ref check` does, with the same messages.
//! The tests check both on every file under `tests/`.
//!
//! Code is stored data-oriented ([`Body`]): per-function flat arrays, with ops, regions, and
//! values referring to each other by 32-bit index.

mod body;
pub mod interp;
mod ir;
mod lex;
mod parse;
mod print;
mod sem;
mod verify;

pub use body::{
    Body, HoleId, Int, IntId, OpId, Operand, OperandKind, Ops, RegionId, StrId, ValueDef, ValueId,
    ValueSpec,
};
pub use ir::*;
pub use parse::{op_kind, parse_module};
pub use verify::{Hole, render_loc, verify_module};
