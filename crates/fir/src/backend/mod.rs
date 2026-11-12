//! Backends: from MFIR to a target's LFIR dialect, and from there to assembly.
//!
//! The first target is AArch64 ([`aarch64`]); see `docs/design/03-plan.md` (LFIR for AArch64)
//! and the decision log (LFIR for AArch64). A backend compiles MFIR: [`prepare`] makes it from
//! any verified module, lowering HFIR first.
//!
//! ```text
//! HFIR ──lower──▶ MFIR ──-O (optional)──▶ MFIR ──isel──▶ LFIR ──regalloc──▶ .s
//! ```

pub mod aarch64;

use crate::Layer;
use crate::ir::Module;
use crate::passes::{Pipeline, Remarks};

/// The MFIR module a backend compiles, from a verified module: HFIR is lowered
/// ([`crate::lower_checked`], which verifies its output), MFIR is taken as it is, and with
/// `optimize` the default `-O` pipeline ([`Pipeline::default_opt`]) runs on the result, which
/// is verified again (after every pass in development builds, as `fir opt` does). LFIR is an
/// error.
pub fn prepare(m: &Module, optimize: bool) -> Result<Module, String> {
    let mut out = match m.layer {
        Layer::Hfir => crate::lower_checked(m)?,
        Layer::Mfir => m.clone(),
        Layer::Lfir(_) => return Err("the module is already LFIR".to_owned()),
    };
    if optimize {
        let mut pipeline = Pipeline::default_opt();
        pipeline.verify_each = cfg!(debug_assertions);
        pipeline
            .run(&mut out, &mut Remarks::new(false))
            .map_err(|e| e.to_string())?;
        crate::verify_module(&out)
            .map_err(|e| format!("the optimized module doesn't verify: {e}"))?;
    }
    Ok(out)
}
