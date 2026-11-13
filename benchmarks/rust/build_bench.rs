//! Time building a large module through the builder API against parsing the same module's text:
//! `cargo run --release --example build_bench [FUNCS] [RUNS]`.
//!
//! Each function has a loop with a `cf.if`, a `cf.blocks` with a conditional branch and a
//! switch, stack memory with loads and stores, a call, and a long chain of integer ops.

use std::time::Instant;

use fir::{
    AllocFail, ArithOp, BuildError, Edge, ModuleBuilder, Ovf, Pred, ShiftEdge, ShiftOp, SwitchCase,
    Target, TruncMode, Ty,
};

const CHAIN: usize = 200;

fn build(funcs: usize) -> Result<fir::Module, BuildError> {
    let i32 = Ty::Int(32);
    let i64 = Ty::Int(64);
    let mut mb = ModuleBuilder::new();
    let pair = mb.struct_ty(fir::Policy::C, &[i32, i64])?;
    let leaf = {
        let mut f = mb.func("leaf", &[i32], &[i32])?;
        let x = f.param(0);
        f.func_ret(&[x.into()])?;
        f.finish()?
    };
    for k in 0..funcs {
        let mut f = mb.func(&format!("f{k}"), &[i32, Ty::Ptr], &[i32])?;
        let (n, _p) = (f.param(0), f.param(1));
        // A chain of integer ops.
        let mut x = n;
        for j in 0..CHAIN {
            let c = f.int_const(i32, (j % 7) as i64 + 1)?;
            x = match j % 5 {
                0 => f.int_arith(ArithOp::Add, Ovf::Wrap, x, c)?,
                1 => f.int_arith(ArithOp::Mul, Ovf::Nsw, x, c)?,
                2 => f.int_div(fir::DivOp::DivU, Edge::Total, Edge::Wrap, x, c)?,
                3 => f.int_shift(ShiftOp::Shl, ShiftEdge::Mask, x, c)?,
                _ => {
                    let w = f.int_zext(i64, x)?;
                    f.int_trunc(i32, TruncMode::Wrap, w)?
                }
            };
        }
        // Memory.
        let s = f.mem_stack_of(pair, 8)?;
        let a = f.ptr_field(true, pair, s, 0)?;
        f.mem_store(i32, x, a, 4)?;
        let sz = f.ty_size(pair)?;
        let h = f.mem_alloc(AllocFail::Trap, "c.malloc", sz, 8)?;
        f.mem_copy(pair, h, s, 8)?;
        let y = f.mem_load(i32, h, 4)?;
        f.mem_free("c.malloc", h)?;
        // A loop with a cf.if.
        let zero = f.int_const(i32, 0)?;
        let lp = f.cf_loop(&[i32], true, &[zero.into()], |f, st| {
            let i = st.get(0);
            let done = f.int_cmp(Pred::Sge, i, n)?;
            f.cf_if(&[], done, |f| f.cf_break(&[i.into()]).map(drop), |_| Ok(()))?;
            let one = f.int_const(i32, 1)?;
            let i2 = f.int_arith(ArithOp::Add, Ovf::Nsw, i, one)?;
            f.cf_continue(&[i2.into()])?;
            Ok(())
        })?;
        // Blocks with branches.
        let bl = f.cf_blocks(&[i32], false, |f, op| {
            let entry = f.block(op, "entry", &[])?;
            let odd = f.block(op, "odd", &[i32])?;
            let out = f.block(op, "out", &[i32])?;
            f.position_at_end(entry)?;
            let c = f.int_cmp(Pred::Ult, y, lp.get(0))?;
            f.cf_cond_br(
                c,
                Target::new(odd, &[y.into()]),
                Target::new(out, &[x.into()]),
            )?;
            f.position_at_end(odd)?;
            let v = f.region_params(odd)?.get(0);
            let args = [v.into()];
            let cases = [SwitchCase {
                key: 3.into(),
                target: Target::new(out, &args),
            }];
            f.cf_switch(v, Target::new(out, &[y.into()]), &cases)?;
            f.position_at_end(out)?;
            let o = f.region_params(out)?.get(0);
            f.cf_yield(&[o.into()])?;
            Ok(())
        })?;
        let r = f.func_call(leaf, &[bl.get(0).into()])?;
        f.func_ret(&[r.get(0).into()])?;
        f.finish()?;
    }
    Ok(mb.finish())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let funcs: usize = args.first().map_or(2000, |s| s.parse().unwrap());
    let runs: u32 = args.get(1).map_or(5, |s| s.parse().unwrap());
    let m = build(funcs).unwrap();
    fir::verify_module(&m).unwrap();
    let text = m.render(true);
    let ops: usize = m.funcs.iter().map(|f| f.body.num_ops()).sum();
    let (mut t_build, mut t_parse) = (f64::MAX, f64::MAX);
    for _ in 0..runs {
        let t = Instant::now();
        let built = build(funcs).unwrap();
        t_build = t_build.min(t.elapsed().as_secs_f64());
        let t = Instant::now();
        let parsed = fir::parse_module(&text).unwrap();
        t_parse = t_parse.min(t.elapsed().as_secs_f64());
        assert_eq!(built.funcs.len(), parsed.funcs.len());
    }
    let mops = |s: f64| ops as f64 / s / 1e6;
    println!(
        "{funcs} functions, {ops} ops, {:.1} MB of text (best of {runs}): build {:.1} ms ({:.0} Mops/s), parse {:.1} ms ({:.0} Mops/s); build/parse {:.2}",
        text.len() as f64 / 1e6,
        t_build * 1e3,
        mops(t_build),
        t_parse * 1e3,
        mops(t_parse),
        t_build / t_parse
    );
}
