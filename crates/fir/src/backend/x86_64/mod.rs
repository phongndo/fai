//! The x86-64 backend: instruction selection from MFIR, register allocation, and GNU assembly
//! for Linux (ELF), under the System V AMD64 ABI.
//!
//! ```text
//! MFIR ──isel──▶ machine code (virtual registers) ──regalloc──▶ machine code ──emit──▶ .s
//! ```
//!
//! The working form is [`mir::MFunc`], flat arrays of [`mir::Inst`], x86-64 instructions in
//! their two-address forms. Unlike AArch64's, this machine code is not yet an LFIR dialect:
//! its instructions have no Lean semantics and no op-table entries, so there is no
//! `layer lfir x86_64` module to print or run in the interpreters, and nothing checks
//! instruction selection but the native tests (decision: x86-64 target). What it covers, and
//! what it refuses, is in [`isel`]: the integer, pointer, memory, control-flow, call, and
//! exception subset of MFIR; not yet floats, variadic definitions, or structs by value.

pub mod emit;
pub mod isel;
pub mod mir;
pub mod regalloc;

pub use emit::Options;

use crate::ir::{Module, Ty};
use mir::{CallShape, MModule};

/// Each callee's argument and result registers, by callee index (functions, then external
/// functions). A variadic callee is called through its address, with the call's own shape.
pub fn shapes(m: &Module) -> Vec<CallShape> {
    let mut out: Vec<CallShape> = m
        .funcs
        .iter()
        .map(|f| {
            let b = &f.body;
            let ps: Vec<Ty> = b.params(b.entry()).map(|v| b.ty(v)).collect();
            isel::call_shape(&ps, &f.rets, false)
        })
        .collect();
    out.extend(
        m.externs
            .iter()
            .map(|x| isel::call_shape(&x.params, &x.rets, false)),
    );
    out
}

/// Instruction selection for every function of a verified MFIR (or core-op HFIR) module:
/// machine code over virtual registers.
pub fn select(m: &Module) -> Result<MModule, String> {
    isel::check_module(m)?;
    let cx = isel::ModuleCx::new(m);
    let mut mm = MModule::default();
    for i in 0..m.funcs.len() {
        mm.funcs.push(isel::select_func(&cx, i as u32)?);
    }
    Ok(mm)
}

/// Allocate registers for every function, in parallel, checking each assignment
/// ([`regalloc::check`]). The first function that fails is the error.
pub fn allocate(m: &Module, mm: &mut MModule) -> Result<(), String> {
    let shapes = shapes(m);
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get());
    let chunk = mm.funcs.len().div_ceil(threads).max(16);
    let results: Vec<Result<(), String>> = std::thread::scope(|s| {
        let handles: Vec<_> = mm
            .funcs
            .chunks_mut(chunk)
            .map(|part| {
                let shapes = &shapes;
                s.spawn(move || {
                    for f in part {
                        let own = shapes[f.index as usize].clone();
                        regalloc::allocate(f, shapes, &own)
                            .map_err(|e| format!("@{}: {e}", m.funcs[f.index as usize].name))?;
                    }
                    Ok(())
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    results.into_iter().collect()
}

/// Compile a verified MFIR module (see [`crate::backend::prepare`]) to assembly.
pub fn compile(m: &Module, o: &Options) -> Result<String, String> {
    let mut mm = select(m)?;
    allocate(m, &mut mm)?;
    Ok(emit::emit(m, &mm, o))
}
