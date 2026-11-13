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
use crate::passes::reference::CheckDce;
use crate::passes::{Observer, Pipeline, Remarks};

/// The MFIR module a backend compiles, from a verified module: HFIR is lowered
/// ([`crate::lower_checked`], which verifies its output), MFIR is taken as it is, and with
/// `optimize` the default `-O` pipeline runs on the result ([`optimize`]). LFIR is an error.
pub fn prepare(m: &Module, optimize: bool) -> Result<Module, String> {
    let mut out = to_mfir(m)?;
    if optimize {
        self::optimize(&mut out)?;
    }
    Ok(out)
}

/// [`prepare`], showing `observer` every pass run of `-O` (and ignoring the environment).
pub fn prepare_observed(
    m: &Module,
    optimize: bool,
    observer: &mut dyn Observer,
) -> Result<Module, String> {
    let mut out = to_mfir(m)?;
    if optimize {
        optimize_observed(&mut out, observer)?;
    }
    Ok(out)
}

fn to_mfir(m: &Module) -> Result<Module, String> {
    match m.layer {
        Layer::Hfir => crate::lower_checked(m),
        Layer::Mfir => Ok(m.clone()),
        Layer::Lfir(_) => Err("the module is already LFIR".to_owned()),
    }
}

/// Run the default `-O` pipeline ([`Pipeline::default_opt`]) on `m` and verify the result (after
/// every pass too, in development builds, as `fir opt` does). What `fir compile -O`, `fai-cc -O`,
/// and the C API's `fir_module_optimize` and `fir_module_compile` run.
///
/// With `FIR_CHECK_DCE=FIR-REF` in the environment ([`crate::passes::reference::ENV`]), every
/// step of `dce` is also checked by the proved Lean checker ([`CheckDce`]): a refusal, a path
/// that isn't an executable file, or a `fir-ref` that fails to run when a step is sent to it is
/// an error (a run where `dce` changes nothing sends it nothing), and on success one summary
/// line goes to stderr (`fir: check-dce: N steps accepted by Fir.Dce.checkModule (…)`).
pub fn optimize(m: &mut Module) -> Result<(), String> {
    let Some(mut check) = CheckDce::from_env()? else {
        return optimize_observed(m, &mut ());
    };
    let r = optimize_observed(m, &mut check);
    check.finish();
    r?;
    eprintln!("fir: {}", check.summary());
    Ok(())
}

/// [`optimize`], showing `observer` every pass run (and ignoring the environment).
pub fn optimize_observed(m: &mut Module, observer: &mut dyn Observer) -> Result<(), String> {
    let mut pipeline = Pipeline::default_opt();
    pipeline.verify_each = cfg!(debug_assertions);
    pipeline
        .run_observed(m, &mut Remarks::new(false), observer)
        .map_err(|e| e.to_string())?;
    crate::verify_module(m)
        .map(drop)
        .map_err(|e| format!("the optimized module doesn't verify: {e}"))
}
