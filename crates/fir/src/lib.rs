//! FIR, the compiler IR, in Rust.
//!
//! The Lean semantics in `spec/` is the source of truth; this crate is checked against it. So
//! far it holds the IR and its text format: [`parse_module`] reads text, and
//! [`Module::render`] prints the same canonical text as the Lean reference tool (`fir-ref fmt`),
//! which the tests check on every file under `tests/`.
//!
//! Code is stored data-oriented ([`Body`]): per-function flat arrays, with ops, regions, and
//! values referring to each other by 32-bit index.

mod body;
mod ir;
mod lex;
mod parse;
mod print;

pub use body::{Body, OpId, Operand, Ops, RegionId, ValueDef, ValueId, ValueSpec};
pub use ir::*;
pub use parse::{op_kind, parse_module};
