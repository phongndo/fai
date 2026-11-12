//! FIR, the compiler IR, in Rust.
//!
//! The Lean semantics in `spec/` is the source of truth; this crate is checked against it. So
//! far it holds the IR, its text format, the verifier, and the interpreter: [`parse_module`]
//! reads text, [`Module::render`] prints the same canonical text as the Lean reference tool
//! (`fir-ref fmt`), [`verify_module`] accepts and rejects what `fir-ref check` does, with the
//! same messages, and [`interp::run`] runs a function and prints the same outcome as `fir-ref
//! run`. [`lower_module`] lowers an HFIR module to MFIR exactly as `fir-ref lower` does (the HFIR
//! building blocks and `ptr.field`/`ptr.index` become core ops). The tests check all of them on
//! every file under `tests/`, and the interpreter and the lowering also on random programs.
//! [`passes`] holds the pass manager and, as passes, the rewrites proved in Lean; the tests check
//! that optimized programs refine the originals in the interpreter.
//!
//! Each op is declared once, in `spec/Fir/Syntax.lean`; [`OpKind`] and the tables the parser,
//! printer, and verifier read ([`OpDecl`]) are generated from the declarations into
//! `src/generated/ops.rs`.
//!
//! Code is stored data-oriented ([`Body`]): per-function flat arrays, with ops, regions, and
//! values referring to each other by 32-bit index. Struct, array, and function types are ids into
//! an interned table ([`Types`]) owned by the body that names them, or by the module's
//! [`Globals`].
//!
//! Modules can also be built in code, through the builder API ([`ModuleBuilder`],
//! [`FuncBuilder`]): one method per op, generated from its declaration into
//! `src/generated/builder.rs`, taking every modifier as a required argument, so no UB choice is
//! left out. The `fir-capi` crate exports the same builder as a stable C API. See [`builder`]
//! for the rules.
//!
//! ```
//! use fir::{ArithOp, ModuleBuilder, Ovf, Ty};
//!
//! let mut mb = ModuleBuilder::new();
//! let i32 = Ty::Int(32);
//! let mut f = mb.func("inc", &[i32], &[i32])?;
//! let x = f.param(0);
//! f.name(x, "x")?;
//! let one = f.int_const(i32, 1)?;
//! let y = f.int_arith(ArithOp::Add, Ovf::Nsw, x, one)?;
//! f.func_ret(&[y.into()])?;
//! f.finish()?;
//! let m = mb.finish();
//! fir::verify_module(&m).unwrap();
//! assert_eq!(
//!     m.render(true),
//!     "func @inc(%x: i32) -> i32 {\n  %1: i32 = int.const 1\n  %2: i32 = int.add.nsw %x, %1\n  func.ret %2\n}\n"
//! );
//! assert_eq!(fir::interp::run(&m, "inc", &["41"], 100).unwrap(), "returned i32 42");
//! # Ok::<(), fir::BuildError>(())
//! ```

#![forbid(unsafe_code)]

pub mod backend;
mod body;
pub mod builder;
pub mod contract;
#[path = "generated/builder.rs"]
#[rustfmt::skip]
mod builder_ops;
mod decl;
#[path = "generated/contracts.rs"]
#[rustfmt::skip]
mod generated_contracts;
pub mod float;
mod globals;
pub mod interp;
mod ir;
mod lex;
mod lower;
#[path = "generated/ops.rs"]
#[rustfmt::skip]
mod ops;
mod parse;
pub mod passes;
mod print;
mod sem;
mod types;
mod verify;

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
pub use lower::{lower_checked, lower_module, support as lower_support};
pub use ops::{TARGETS, op_kind};
pub use parse::parse_module;
pub use sem::TrapReason;
pub use types::align_up;
pub use verify::{Hole, render_loc, verify_module};
