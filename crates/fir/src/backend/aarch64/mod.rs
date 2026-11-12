//! The AArch64 backend: the `aarch64` LFIR dialect, instruction selection from MFIR, register
//! allocation, and GNU assembly.
//!
//! ```text
//! MFIR ──isel──▶ LFIR (virtual registers) ──regalloc, frame──▶ LFIR (physical) ──emit──▶ .s
//! ```
//!
//! The working form is [`mir::MFunc`], flat arrays of [`mir::Inst`] (one LFIR op each);
//! [`lfir::to_module`] turns it into an LFIR module at either stage, which `fir run` and
//! `fir-ref run` execute. The calling convention is AAPCS64 for integers and pointers: see the
//! decision log (LFIR for AArch64) and [`machine`]'s twin in Lean, `Fir.AArch64Machine`.

pub mod abi;
pub mod emit;
pub mod isel;
pub mod lfir;
pub mod mir;
pub mod regalloc;
pub mod syntax;

pub use emit::{Options, Os};

use crate::ir::Module;
use mir::MModule;

/// Each callee's parameter and result counts, by callee index (functions, then external
/// functions).
fn shapes(m: &Module) -> Vec<(u32, u32)> {
    let mut out: Vec<(u32, u32)> = m
        .funcs
        .iter()
        .map(|f| {
            let b = &f.body;
            (b.params(b.entry()).len() as u32, f.rets.len() as u32)
        })
        .collect();
    out.extend(
        m.externs
            .iter()
            .map(|x| (x.params.len() as u32, x.rets.len() as u32)),
    );
    out
}

/// Instruction selection for every function of a verified MFIR (or core-op HFIR) module: LFIR
/// over virtual registers.
pub fn select(m: &Module) -> Result<MModule, String> {
    isel::check_module(m)?;
    let cx = isel::ModuleCx::new(m);
    let mut mm = MModule::default();
    for i in 0..m.funcs.len() {
        let f = isel::select_func(&cx, i as u32, &mut mm.families)?;
        mm.funcs.push(f);
    }
    Ok(mm)
}

/// Allocate registers and lay out the frames of every function, in parallel.
pub fn allocate(m: &Module, mm: &mut MModule) {
    let shapes = shapes(m);
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get());
    let chunk = mm.funcs.len().div_ceil(threads).max(16);
    std::thread::scope(|s| {
        for part in mm.funcs.chunks_mut(chunk) {
            let shapes = &shapes;
            s.spawn(move || {
                for f in part {
                    let nrets = m.funcs[f.index as usize].rets.len();
                    regalloc::allocate(f, shapes, nrets);
                }
            });
        }
    });
}

/// Compile a verified module to assembly.
pub fn compile(m: &Module, o: &Options) -> Result<String, String> {
    let mut mm = select(m)?;
    allocate(m, &mut mm);
    Ok(emit::emit(m, &mm, o))
}
