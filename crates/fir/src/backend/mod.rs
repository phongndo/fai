//! Backends: from MFIR to a target's LFIR dialect, and from there to assembly.
//!
//! The first target is AArch64 ([`aarch64`]); see `docs/design/03-plan.md` (LFIR for AArch64)
//! and the decision log (LFIR for AArch64). The second, [`x86_64`], compiles the integer subset
//! of MFIR for x86-64 Linux through machine code that isn't an LFIR dialect yet (decision:
//! x86-64 target). What both emit for globals is in [`data`]. A backend compiles MFIR:
//! [`prepare`] makes it from any verified module, lowering HFIR first.
//!
//! ```text
//! HFIR ──lower──▶ MFIR ──-O (optional)──▶ MFIR ──isel──▶ LFIR ──regalloc──▶ .s
//! ```

pub mod aarch64;
pub use crate::codegen::data;
pub mod x86_64;

pub use crate::driver::{
    optimize, optimize_observed, optimize_with, prepare, prepare_observed, prepare_with,
};
