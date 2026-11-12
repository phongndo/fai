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
pub mod regcheck;
pub mod syntax;

pub use emit::{Options, Os};

/// The bits of the float an `fmov` immediate encodes (ASL's `VFPExpandImm`).
pub fn machine_imm(fs: crate::ir::FSize, imm: u8) -> u64 {
    crate::interp::vfp_expand_imm(fs, u32::from(imm))
}

use crate::ir::Module;
use mir::MModule;

/// Each callee's argument and result registers, by callee index (functions, then external
/// functions).
pub fn shapes(m: &Module) -> Vec<abi::CallShape> {
    let mut out: Vec<abi::CallShape> = m
        .funcs
        .iter()
        .map(|f| {
            let b = &f.body;
            let ps: Vec<crate::ir::Ty> = b.params(b.entry()).map(|v| b.ty(v)).collect();
            abi::CallShape::of(&ps, &f.rets)
        })
        .collect();
    out.extend(
        m.externs
            .iter()
            .map(|x| abi::CallShape::of(&x.params, &x.rets)),
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

/// Allocate registers and lay out the frames of every function, in parallel, validating each
/// function's result ([`regcheck::validate`]). The first function that fails validation is the
/// error.
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
                        let own = &shapes[f.index as usize];
                        regalloc::allocate(f, shapes, own)?;
                    }
                    Ok(())
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    results.into_iter().collect()
}

/// A variadic function, external function, or call through a variadic signature of the module,
/// if it has one, for the message.
fn uses_varargs(m: &Module) -> Option<String> {
    if let Some(name) = m
        .funcs
        .iter()
        .filter(|f| f.variadic)
        .map(|f| &f.name)
        .chain(m.externs.iter().filter(|x| x.variadic).map(|x| &x.name))
        .next()
    {
        return Some(format!("@{name}"));
    }
    for f in &m.funcs {
        let b = &f.body;
        let mut stack = vec![b.entry()];
        while let Some(r) = stack.pop() {
            for op in b.ops(r) {
                if let crate::OpKind::CallIndirect(sig) | crate::OpKind::InvokeIndirect { sig, .. } =
                    b.kind(op)
                    && let Some(crate::Shape::Func(_, _, true)) = b.types().shape_of(sig)
                {
                    return Some(format!("a call in @{}", f.name));
                }
                stack.extend_from_slice(b.regions(op));
            }
        }
    }
    None
}

/// Compile a verified module to assembly.
pub fn compile(m: &Module, o: &Options) -> Result<String, String> {
    if o.os == Os::Darwin
        && let Some(what) = uses_varargs(m)
    {
        // Apple's AAPCS64 passes every variadic argument on the stack and makes `va_list` a
        // pointer (open item: macOS varargs).
        return Err(format!(
            "{what} is variadic, and variadic functions aren't supported on macOS yet"
        ));
    }
    let mut mm = select(m)?;
    allocate(m, &mut mm)?;
    Ok(emit::emit(m, &mm, o))
}
