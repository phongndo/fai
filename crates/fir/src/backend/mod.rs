//! Backends: from MFIR to a target's LFIR dialect, and from there to assembly.
//!
//! The first target is AArch64 ([`aarch64`]); see `docs/design/03-plan.md` (LFIR for AArch64)
//! and the decision log (LFIR for AArch64).

pub mod aarch64;
