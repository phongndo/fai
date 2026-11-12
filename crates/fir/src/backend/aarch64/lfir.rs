//! Machine code as an LFIR module (`layer lfir aarch64`): what `fir compile --emit lfir`
//! prints, and what the interpreters run to check instruction selection and register
//! allocation against the source program.

use super::mir::{Inst, MFunc, MModule};
use crate::body::{Body, Succ, ValueSpec};
use crate::ir::*;

/// The LFIR module for `m`'s functions as `mm` has them: the same globals and external
/// functions, and each function's code as one `aarch64.code` op.
pub fn to_module(m: &Module, mm: &MModule) -> Module {
    let mut out = Module {
        layer: crate::Layer::Lfir("aarch64"),
        space: m.space.clone(),
        globals: m.globals.clone(),
        externs: m.externs.clone(),
        funcs: Vec::with_capacity(mm.funcs.len()),
    };
    for f in &mm.funcs {
        out.funcs.push(func(m, mm, f));
    }
    out
}

fn func(m: &Module, mm: &MModule, f: &MFunc) -> Func {
    let src = &m.funcs[f.index as usize];
    let sb = &src.body;
    let mut body = Body::new();
    let params: Vec<(String, Ty)> = sb
        .params(sb.entry())
        .map(|v| (sb.name(v).to_owned(), sb.ty(v)))
        .collect();
    // Parameter types: value types, which need no table.
    body.set_params(
        body.entry(),
        params.iter().map(|(n, t)| ValueSpec {
            name: n,
            ty: *t,
            facts: Vec::new(),
        }),
    );
    let entry = body.entry();
    let code = body.append_op(entry, OpKind::A64Code, [], [], [], None);
    let labels: Vec<_> = (0..f.blocks.len())
        .map(|b| body.add_str(&format!("b{b}")))
        .collect();
    let regions: Vec<_> = labels
        .iter()
        .map(|&l| body.new_block(code, l, []))
        .collect();
    body.set_regions(code, &regions);
    let succ = |body: &mut Body, b: u32| {
        body.add_succ(Succ {
            label: labels[b as usize],
            nargs: 0,
        })
    };
    let name = |m: &Module, func: u32| -> String {
        match m.funcs.get(func as usize) {
            Some(f) => f.name.clone(),
            None => m.externs[func as usize - m.funcs.len()].name.clone(),
        }
    };
    for (b, &region) in regions.iter().enumerate() {
        for i in f.block_range(b) {
            let kind = match f.insts[i] {
                Inst::Alu { op, sf, d, n, m } => OpKind::A64Alu { op, sf, d, n, m },
                Inst::AluImm { op, sf, d, n, imm } => OpKind::A64AluImm {
                    op,
                    sf,
                    d,
                    n,
                    imm: body.add_small_int(imm),
                },
                Inst::ShiftImm {
                    op,
                    sf,
                    d,
                    n,
                    amount,
                } => OpKind::A64ShiftImm {
                    op,
                    sf,
                    d,
                    n,
                    amount: amount.into(),
                },
                Inst::Ext {
                    signed,
                    sf,
                    d,
                    n,
                    width,
                } => OpKind::A64Ext {
                    signed,
                    sf,
                    d,
                    n,
                    width: width.into(),
                },
                Inst::Mov { sf, d, n } => OpKind::A64Mov { sf, d, n },
                Inst::MovWide { op, sf, d, imm, hw } => OpKind::A64MovWide {
                    op,
                    sf,
                    d,
                    imm: imm.into(),
                    hw: hw.into(),
                },
                Inst::Csel { op, c, sf, d, n, m } => OpKind::A64Csel { op, c, sf, d, n, m },
                Inst::Ldr { size, d, base, off } => OpKind::A64Ldr {
                    size,
                    d,
                    base,
                    off: body.add_small_int(off),
                },
                Inst::Str { size, s, base, off } => OpKind::A64Str {
                    size,
                    s,
                    base,
                    off: body.add_small_int(off),
                },
                Inst::Adrl { d, global } => OpKind::A64Adrl {
                    d,
                    global: body.add_str(m.globals.name(global as usize)),
                },
                Inst::AdrlFunc { d, func } => OpKind::A64AdrlFunc {
                    d,
                    callee: body.add_str(&name(m, func)),
                },
                Inst::B { t } => OpKind::A64B {
                    dest: succ(&mut body, t),
                },
                Inst::BCond { c, t, f: e } => {
                    let t = succ(&mut body, t);
                    let e = succ(&mut body, e);
                    OpKind::A64BCond { c, t, f: e }
                }
                Inst::Ret => OpKind::A64Ret,
                Inst::Trap(r) => OpKind::A64Trap(r),
                Inst::Bl { func } => OpKind::A64Bl {
                    callee: body.add_str(&name(m, func)),
                },
                Inst::Blr { n, sig } => {
                    let (ps, rs) = &f.sigs[sig as usize];
                    OpKind::A64Blr {
                        sig: body.types_mut().func(ps, rs),
                        n,
                    }
                }
                Inst::BlAlloc { family, align } => OpKind::A64BlAlloc {
                    family: body.add_str(&mm.families[family as usize]),
                    align,
                },
                Inst::BlFree { family } => OpKind::A64BlFree {
                    family: body.add_str(&mm.families[family as usize]),
                },
                Inst::ExnSet { n } => OpKind::A64ExnSet { n },
                Inst::ExnTake { d } => OpKind::A64ExnTake { d },
                Inst::BExn { t, f: e } => {
                    let t = succ(&mut body, t);
                    let e = succ(&mut body, e);
                    OpKind::A64BExn { t, f: e }
                }
            };
            body.append_op(region, kind, [], [], [], f.locs[i]);
        }
    }
    body.shrink_to_fit();
    Func {
        name: src.name.clone(),
        rets: src.rets.clone(),
        file: src.file.clone(),
        body,
    }
}
