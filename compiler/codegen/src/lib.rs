//! What the backends share: the assembly for global data ([`data`]), the codes the runtime's
//! trap handler takes ([`trap_code`]), and which functions may return with an exception pending
//! ([`may_throw`]).

#![forbid(unsafe_code)]

pub mod data;

use rustc_hash::FxHashMap;

use fai_ir::ir::{Module, OpKind, TrapReason};

/// The reason code `__fir_trap(reason, line, col)` receives for a trap (decision: Traps at run
/// time).
pub fn trap_code(r: TrapReason) -> u32 {
    match r {
        TrapReason::Div0 => 0,
        TrapReason::Overflow => 1,
        TrapReason::Shift => 2,
        TrapReason::Oom => 3,
        TrapReason::Bounds => 4,
        TrapReason::Tag => 5,
        TrapReason::Convert => 6,
    }
}

/// Which functions of a module may throw out of themselves: those with an `exn.throw`, a plain
/// call to one that may, or an indirect call when any function may (a `func.invoke` catches
/// what its callee throws). The least fixed point, so code without throws gets no checks.
pub fn may_throw(m: &Module) -> Vec<bool> {
    let names: FxHashMap<&str, usize> = m
        .funcs
        .iter()
        .enumerate()
        .map(|(i, f)| (f.name.as_str(), i))
        .collect();
    // Each function's own throws, direct callees (plain calls), and whether it calls indirectly.
    let mut own = vec![false; m.funcs.len()];
    let mut callees: Vec<Vec<usize>> = vec![Vec::new(); m.funcs.len()];
    let mut indirect = vec![false; m.funcs.len()];
    for (i, f) in m.funcs.iter().enumerate() {
        let b = &f.body;
        let mut stack = vec![b.entry()];
        while let Some(r) = stack.pop() {
            for op in b.ops(r) {
                match b.kind(op) {
                    OpKind::Throw => own[i] = true,
                    OpKind::Call { callee } => {
                        if let Some(&g) = names.get(b.str(callee)) {
                            callees[i].push(g);
                        }
                    }
                    OpKind::CallIndirect(_) => indirect[i] = true,
                    _ => {}
                }
                stack.extend_from_slice(b.regions(op));
            }
        }
    }
    let mut throws = own;
    loop {
        let any = throws.iter().any(|&t| t);
        let mut changed = false;
        for i in 0..throws.len() {
            if !throws[i] && ((indirect[i] && any) || callees[i].iter().any(|&g| throws[g])) {
                throws[i] = true;
                changed = true;
            }
        }
        if !changed {
            return throws;
        }
    }
}
