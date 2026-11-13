//! Pipeline orchestration: from any verified module to the MFIR a backend compiles
//! ([`prepare`]: HFIR is lowered first, and the default `-O` pipeline or a named one runs), the
//! `-O` pipeline with its optional proved DCE check ([`optimize`]), and the list of components
//! that declare what they do with each op kind ([`components`]). Reached as `fir::backend::*`
//! and `fir::contract::components`.

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

/// Like [`prepare`], with `pipeline` (if any) run on the MFIR instead of the default one
/// ([`optimize_with`]): how experimental passes reach the backend (`fir compile --passes`,
/// `fcc --passes`).
pub fn prepare_with(m: &Module, pipeline: Option<&Pipeline>) -> Result<Module, String> {
    let mut out = to_mfir(m)?;
    if let Some(p) = pipeline {
        optimize_with(&mut out, p)?;
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
/// every pass too, in development builds, as `fir opt` does). What `fir compile -O`, `fcc -O`,
/// and the C API's `fir_module_optimize` and `fir_module_compile` run.
///
/// With `FIR_CHECK_DCE=FIR-REF` in the environment ([`crate::passes::reference::ENV`]), every
/// step of `dce` is also checked by the proved Lean checker ([`CheckDce`]): a refusal, a path
/// that isn't an executable file, or a `fir-ref` that fails to run when a step is sent to it is
/// an error (a run where `dce` changes nothing sends it nothing), and on success one summary
/// line goes to stderr (`fir: check-dce: N steps accepted by Fir.Dce.checkModule (…)`).
pub fn optimize(m: &mut Module) -> Result<(), String> {
    optimize_with(m, &Pipeline::default_opt())
}

/// [`optimize`] with `pipeline` instead of the default one (`FIR_CHECK_DCE` included).
pub fn optimize_with(m: &mut Module, pipeline: &Pipeline) -> Result<(), String> {
    let Some(mut check) = CheckDce::from_env()? else {
        return run_observed(m, pipeline, &mut ());
    };
    let r = run_observed(m, pipeline, &mut check);
    check.finish();
    r?;
    eprintln!("fir: {}", check.summary());
    Ok(())
}

/// [`optimize`], showing `observer` every pass run (and ignoring the environment).
pub fn optimize_observed(m: &mut Module, observer: &mut dyn Observer) -> Result<(), String> {
    run_observed(m, &Pipeline::default_opt(), observer)
}

fn run_observed(
    m: &mut Module,
    pipeline: &Pipeline,
    observer: &mut dyn Observer,
) -> Result<(), String> {
    let mut pipeline = pipeline.clone();
    pipeline.verify_each |= cfg!(debug_assertions);
    pipeline
        .run_observed(m, &mut Remarks::new(false), observer)
        .map_err(|e| e.to_string())?;
    crate::verify_module(m)
        .map(drop)
        .map_err(|e| format!("the optimized module doesn't verify: {e}"))
}

/// The components that declare their support, by name, for reports and `tests/contracts.rs`.
pub fn components() -> [(&'static str, crate::contract::SupportFn); 3] {
    [
        ("interp", crate::interp::support),
        ("isel.aarch64", crate::backend::aarch64::isel::support),
        ("isel.x86_64", crate::backend::x86_64::isel::support),
    ]
}
