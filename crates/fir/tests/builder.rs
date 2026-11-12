//! The builder API, checked against the text format.
//!
//! * Every file under `tests/` that parses and verifies is rebuilt op by op through the builder
//!   (the typed method of each op, the scoped and the `_begin` forms of ops with regions, names,
//!   facts, holes, locations, globals, and external functions), and must verify and print
//!   byte for byte as the parsed module does. So the builder can say everything the text can.
//!   The fuzzer's random programs (see `progs`) are rebuilt the same way.
//! * Eager checks reject what they should, and leave nothing behind.

#[allow(dead_code)]
mod common;
#[allow(dead_code)]
mod progs;

use fir::*;

/// A type of `from` as a type of the builder's table.
fn copy_ty(from: &Types, t: Ty, mb: &mut ModuleBuilder) -> Ty {
    let Ty::Agg(id) = t else { return t };
    match from.shape(id) {
        Shape::Struct(p, fs) => {
            let fs: Vec<Ty> = fs.iter().map(|&f| copy_ty(from, f, mb)).collect();
            mb.struct_ty(p, &fs).unwrap()
        }
        Shape::Array(n, e) => {
            let e = copy_ty(from, e, mb);
            mb.array_ty(n, e).unwrap()
        }
        Shape::Func(ps, rs) => {
            let ps: Vec<Ty> = ps.iter().map(|&t| copy_ty(from, t, mb)).collect();
            let rs: Vec<Ty> = rs.iter().map(|&t| copy_ty(from, t, mb)).collect();
            mb.func_ty(&ps, &rs).unwrap()
        }
    }
}

fn int(n: Int<'_>) -> IntImm {
    match n {
        Int::Small(n) => n.into(),
        Int::Big(n) => n.clone().into(),
    }
}

fn copy_init(g: &Globals, init: Init, mb: &mut ModuleBuilder) -> Result<Init, BuildError> {
    Ok(match init {
        Init::Zero | Init::Null => init,
        Init::Int(i) => mb.init_int(g.int(i).clone()),
        Init::Sym(r) => {
            let name = g.text(r);
            match (mb.func_ref(name), mb.global_ref(name)) {
                (Some(f), _) => mb.init_func(f)?,
                (_, Some(gl)) => mb.init_global(gl)?,
                _ => panic!("@{name} names nothing"),
            }
        }
        Init::Bytes(r) => mb.init_bytes(g.bytes(r)),
        Init::List(r) => {
            let items = g
                .items(r)
                .iter()
                .map(|&i| copy_init(g, i, mb))
                .collect::<Result<Vec<_>, _>>()?;
            mb.init_list(&items)
        }
    })
}

/// Rebuild a parsed module through the builder.
fn rebuild(m: &Module) -> Result<Module, BuildError> {
    let mut mb = ModuleBuilder::new();
    mb.set_space(m.space.clone());
    mb.set_layer(m.layer);
    let gt = &m.globals.types;
    for x in &m.externs {
        let ps: Vec<Ty> = x.params.iter().map(|&t| copy_ty(gt, t, &mut mb)).collect();
        let rs: Vec<Ty> = x.rets.iter().map(|&t| copy_ty(gt, t, &mut mb)).collect();
        mb.extern_func(&x.name, &ps, &rs, &x.effects, x.trust)?;
    }
    let mut refs = Vec::new();
    for f in &m.funcs {
        let b = &f.body;
        let ps: Vec<Ty> = b.params(b.entry()).map(|v| b.ty(v)).collect();
        refs.push(mb.declare_func(&f.name, &ps, &f.rets)?);
    }
    let g = &m.globals;
    for i in 0..g.len() {
        let t = copy_ty(gt, g.ty(i), &mut mb);
        mb.global(g.name(i), t, g.is_const(i), g.align(i), Init::Zero)?;
    }
    for i in 0..g.len() {
        let init = copy_init(g, g.init(i), &mut mb)?;
        mb.set_global_init(GlobalRef::from_raw(i as u32), init)?;
    }
    for (f, &r) in m.funcs.iter().zip(&refs) {
        let mut fb = mb.define(r)?;
        fb.set_file(f.file.as_deref());
        let mut rp = Replay {
            src: &f.body,
            values: vec![None; f.body.num_values()],
            labels: Vec::new(),
        };
        let entry = f.body.entry();
        for (i, p) in f.body.params(entry).enumerate() {
            let v = fb.param(i);
            rp.define(&mut fb, p, v)?;
        }
        rp.region(&mut fb, entry)?;
        fb.finish()?;
    }
    Ok(mb.finish())
}

struct Replay<'a> {
    src: &'a Body,
    /// Each source value's new value.
    values: Vec<Option<ValueId>>,
    /// The blocks of the enclosing `cf.blocks` ops, innermost last: label and new block.
    labels: Vec<Vec<(&'a str, RegionId)>>,
}

impl<'a> Replay<'a> {
    fn ty(&self, f: &mut FuncBuilder<'_>, t: Ty) -> Ty {
        copy_ty(self.src.types(), t, f.module())
    }

    fn tys(&self, f: &mut FuncBuilder<'_>, ts: impl Iterator<Item = Ty>) -> Vec<Ty> {
        ts.map(|t| self.ty(f, t)).collect()
    }

    /// Map a source value to a new one, with its name and facts.
    fn define(
        &mut self,
        f: &mut FuncBuilder<'_>,
        old: ValueId,
        new: ValueId,
    ) -> Result<(), BuildError> {
        let s = self.src;
        self.values[old.index()] = Some(new);
        f.name(new, s.name(old))?;
        let facts: Vec<(FactArg, Trust)> = s
            .facts(old)
            .iter()
            .map(|tf| {
                let fact = match tf.fact {
                    Fact::RangeS(lo, hi) => FactArg::RangeS(int(s.int(lo)), int(s.int(hi))),
                    Fact::RangeU(lo, hi) => FactArg::RangeU(int(s.int(lo)), int(s.int(hi))),
                    Fact::NonNull => FactArg::NonNull,
                    Fact::Align(n) => FactArg::Align(n),
                    Fact::NoAlias => FactArg::NoAlias,
                    Fact::ReadOnly => FactArg::ReadOnly,
                };
                (fact, tf.trust)
            })
            .collect();
        if !facts.is_empty() {
            f.set_facts(new, &facts)?;
        }
        Ok(())
    }

    fn operand(&self, f: &mut FuncBuilder<'_>, o: Operand) -> Result<Operand, BuildError> {
        Ok(match o.get() {
            OperandKind::Value(v) => Operand::value(self.values[v.index()].expect("defined")),
            OperandKind::Hole(h) => {
                let t = self.ty(f, self.src.hole_ty(h));
                f.hole(self.src.hole_name(h), t)?
            }
        })
    }

    fn region(&mut self, f: &mut FuncBuilder<'_>, r: RegionId) -> Result<(), BuildError> {
        for op in self.src.ops(r) {
            self.op(f, op)?;
        }
        Ok(())
    }

    fn block(&self, label: StrId) -> RegionId {
        let l = self.src.str(label);
        let blocks = self.labels.last().expect("inside cf.blocks");
        blocks
            .iter()
            .find(|(n, _)| *n == l)
            .expect("a known label")
            .1
    }

    fn op(&mut self, f: &mut FuncBuilder<'_>, op: OpId) -> Result<(), BuildError> {
        let s = self.src;
        f.set_loc(s.loc(op));
        let ops = s
            .operands(op)
            .iter()
            .map(|&o| self.operand(f, o))
            .collect::<Result<Vec<_>, _>>()?;
        let res = self.tys(f, s.results(op).map(|v| s.ty(v)));
        let func = |f: &mut FuncBuilder<'_>, name: StrId| f.module().func_ref(s.str(name)).unwrap();
        let one = |v: ValueId| Some(v);
        // The new op, from its first result when the method returns that.
        let made: Option<ValueId>;
        let mut new_op: Option<OpId> = None;
        match s.kind(op) {
            OpKind::Const(n) => made = one(f.int_const(res[0], int(s.int(n)))?),
            OpKind::Poison => made = one(f.poison(res[0])?),
            OpKind::Freeze => made = one(f.freeze(ops[0])?),
            OpKind::Copy => made = one(f.copy(ops[0])?),
            OpKind::Select => made = one(f.select(ops[0], ops[1], ops[2])?),
            OpKind::Arith(a, o) => made = one(f.int_arith(a, o, ops[0], ops[1])?),
            OpKind::Bit(b) => made = one(f.int_bit(b, ops[0], ops[1])?),
            OpKind::Div(d, z, o) => made = one(f.int_div(d, z, o, ops[0], ops[1])?),
            OpKind::Shift(sh, e) => made = one(f.int_shift(sh, e, ops[0], ops[1])?),
            OpKind::Cmp(p) => made = one(f.int_cmp(p, ops[0], ops[1])?),
            OpKind::Zext => made = one(f.int_zext(res[0], ops[0])?),
            OpKind::Sext => made = one(f.int_sext(res[0], ops[0])?),
            OpKind::Trunc(m) => made = one(f.int_trunc(res[0], m, ops[0])?),
            OpKind::MemStack { size, align } => made = one(f.mem_stack(size, align)?),
            OpKind::MemAlloc {
                fail,
                family,
                align,
            } => made = one(f.mem_alloc(fail, s.str(family), ops[0], align)?),
            OpKind::MemFree { family } => {
                made = None;
                new_op = Some(f.mem_free(s.str(family), ops[0])?);
            }
            OpKind::Load { align } => made = one(f.mem_load(res[0], ops[0], align)?),
            OpKind::Store { ty, align } => {
                made = None;
                let ty = self.ty(f, ty);
                new_op = Some(f.mem_store(ty, ops[0], ops[1], align)?);
            }
            OpKind::PtrOffset { inbounds } => made = one(f.ptr_offset(inbounds, ops[0], ops[1])?),
            OpKind::PtrAddr => made = one(f.ptr_addr(ops[0])?),
            OpKind::PtrExpose => made = one(f.ptr_expose(ops[0])?),
            OpKind::PtrFromExposed => made = one(f.ptr_from_exposed(ops[0])?),
            OpKind::PtrWithAddr => made = one(f.ptr_with_addr(ops[0], ops[1])?),
            OpKind::PtrNull => made = one(f.ptr_null()?),
            OpKind::PtrCmp(p) => made = one(f.ptr_cmp(p, ops[0], ops[1])?),
            OpKind::Call { callee } => {
                made = None;
                let callee = func(f, callee);
                new_op = Some(f.func_call(callee, &ops)?.op);
            }
            OpKind::If => {
                // The `_begin` form, positioned by hand, as the C API builds it.
                made = None;
                let new = f.cf_if_begin(&res, ops[0])?;
                let at = f.insert_point();
                for (i, &r) in s.regions(op).iter().enumerate() {
                    f.position_at_end(f.region(new, i)?)?;
                    self.region(f, r)?;
                }
                f.set_insert_point(at)?;
                new_op = Some(new);
            }
            OpKind::Loop { progress } => {
                made = None;
                let inner = s.regions(op)[0];
                let r = f.cf_loop(&res, progress, &ops, |f, params| {
                    for (old, new) in s.params(inner).zip(params.iter()) {
                        self.define(f, old, new)?;
                    }
                    self.region(f, inner)
                })?;
                new_op = Some(r.op);
            }
            OpKind::Yield => {
                made = None;
                new_op = Some(f.cf_yield(&ops)?);
            }
            OpKind::Break => {
                made = None;
                new_op = Some(f.cf_break(&ops)?);
            }
            OpKind::Continue => {
                made = None;
                new_op = Some(f.cf_continue(&ops)?);
            }
            OpKind::Ret => {
                made = None;
                new_op = Some(f.func_ret(&ops)?);
            }
            OpKind::Blocks { progress } => {
                made = None;
                let r = f.cf_blocks(&res, progress, |f, bop| {
                    let mut blocks = Vec::new();
                    for &r in s.regions(op) {
                        let label = s.str(s.label(r).expect("a block has a label"));
                        let ps = self.tys(f, s.params(r).map(|v| s.ty(v)));
                        let new = f.block(bop, label, &ps)?;
                        for (old, nv) in s.params(r).zip(f.region_params(new)?.iter()) {
                            self.define(f, old, nv)?;
                        }
                        blocks.push((label, new));
                    }
                    self.labels.push(blocks);
                    for (i, &r) in s.regions(op).iter().enumerate() {
                        f.position_at_end(self.labels.last().unwrap()[i].1)?;
                        self.region(f, r)?;
                    }
                    self.labels.pop();
                    Ok(())
                })?;
                new_op = Some(r.op);
            }
            OpKind::Br { dest } => {
                made = None;
                let t = Target::new(self.block(s.succ(dest).label), &ops);
                new_op = Some(f.cf_br(t)?);
            }
            OpKind::CondBr { t, f: e } => {
                made = None;
                let (t, e) = (s.succ(t), s.succ(e));
                let split = 1 + t.nargs as usize;
                let tt = Target::new(self.block(t.label), &ops[1..split]);
                let et = Target::new(self.block(e.label), &ops[split..]);
                new_op = Some(f.cf_cond_br(ops[0], tt, et)?);
            }
            OpKind::Switch { dflt, cases } => {
                made = None;
                let d = s.succ(dflt);
                let mut next = 1 + d.nargs as usize;
                let dt = Target::new(self.block(d.label), &ops[1..next]);
                let mut cs = Vec::new();
                for c in s.cases(cases) {
                    let end = next + c.succ.nargs as usize;
                    cs.push(SwitchCase {
                        key: int(s.int(c.key)),
                        target: Target::new(self.block(c.succ.label), &ops[next..end]),
                    });
                    next = end;
                }
                new_op = Some(f.cf_switch(ops[0], dt, &cs)?);
            }
            OpKind::TySize(t) => {
                let t = self.ty(f, t);
                made = one(f.ty_size(t)?);
            }
            OpKind::TyAlign(t) => {
                let t = self.ty(f, t);
                made = one(f.ty_align(t)?);
            }
            OpKind::TyOffset { ty, index } => {
                let t = self.ty(f, ty);
                made = one(f.ty_offset(t, index)?);
            }
            OpKind::PtrField {
                inbounds,
                ty,
                index,
            } => {
                let t = self.ty(f, ty);
                made = one(f.ptr_field(inbounds, t, ops[0], index)?);
            }
            OpKind::PtrIndex { inbounds, ty } => {
                let t = self.ty(f, ty);
                made = one(f.ptr_index(inbounds, t, ops[0], ops[1])?);
            }
            OpKind::MemStackOf { ty, align } => {
                let t = self.ty(f, ty);
                made = one(f.mem_stack_of(t, align)?);
            }
            OpKind::MemCopy { ty, align } => {
                made = None;
                let t = self.ty(f, ty);
                new_op = Some(f.mem_copy(t, ops[0], ops[1], align)?);
            }
            OpKind::MemGlobal { global } => {
                let g = f.module().global_ref(s.str(global)).unwrap();
                made = one(f.mem_global(g)?);
            }
            OpKind::FuncAddr { callee } => {
                let c = func(f, callee);
                made = one(f.func_addr(c)?);
            }
            OpKind::CallIndirect(sig) => {
                made = None;
                let sig = self.ty(f, sig);
                new_op = Some(f.func_call_indirect(sig, ops[0], &ops[1..])?.op);
            }
        }
        let new_op = match (made, new_op) {
            (Some(v), _) => match f.body().def(v) {
                ValueDef::Result { op, .. } => op,
                ValueDef::Param { .. } => unreachable!(),
            },
            (None, Some(op)) => op,
            (None, None) => unreachable!(),
        };
        let news = f.results(new_op)?;
        assert_eq!(news.len(), s.results(op).len());
        for (old, new) in s.results(op).zip(news.values.iter()) {
            self.define(f, old, new)?;
        }
        Ok(())
    }
}

#[test]
fn builder_rebuilds_every_verified_file() {
    let mut fails = Vec::new();
    let mut rebuilt = 0;
    for file in common::fir_files() {
        let name = common::display_name(&file);
        let text = std::fs::read_to_string(&file).unwrap();
        let Ok(m) = parse_module(&text) else { continue };
        if verify_module(&m).is_err() {
            continue;
        }
        check_rebuilds(&name, &m, &mut fails);
        rebuilt += 1;
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
    assert!(rebuilt >= 30, "only {rebuilt} files rebuilt");
}

/// Rebuild a module and compare it with the original, as text.
fn check_rebuilds(name: &str, m: &Module, fails: &mut Vec<String>) {
    let m2 = match rebuild(m) {
        Ok(m2) => m2,
        Err(e) => {
            fails.push(format!("{name}: {e}"));
            return;
        }
    };
    if let Err(e) = verify_module(&m2) {
        fails.push(format!("{name}: the rebuilt module doesn't verify: {e}"));
    }
    for f in &m2.funcs {
        if let Err(e) = f.body.check_invariants() {
            fails.push(format!("{name}: @{}: broken body: {e}", f.name));
        }
    }
    for show_locs in [true, false] {
        let (want, got) = (m.render(show_locs), m2.render(show_locs));
        if want != got {
            fails.push(format!(
                "{name}: the rebuilt module prints differently:\n--- parsed\n{want}\n--- rebuilt\n{got}"
            ));
        }
    }
}

#[test]
fn builder_rebuilds_random_programs() {
    let mut fails = Vec::new();
    for k in 0..300 {
        let mut rng = progs::Rng::new(0x5eed ^ (k << 20));
        let prog = progs::program(&mut rng);
        let m = parse_module(&prog.text).unwrap();
        verify_module(&m).unwrap();
        check_rebuilds(&format!("program {k}"), &m, &mut fails);
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}

fn i32() -> Ty {
    Ty::Int(32)
}

/// A function `@f(i32, i64, ptr) -> i32` being built.
fn with_func(test: impl FnOnce(&mut FuncBuilder<'_>)) {
    let mut mb = ModuleBuilder::new();
    let mut f = mb
        .func("f", &[i32(), Ty::Int(64), Ty::Ptr], &[i32()])
        .unwrap();
    test(&mut f);
}

fn message<T: std::fmt::Debug>(r: Result<T, BuildError>) -> String {
    r.unwrap_err().message().to_owned()
}

#[test]
fn eager_checks_reject_and_leave_nothing() {
    with_func(|f| {
        let (a, w, p) = (f.param(0), f.param(1), f.param(2));
        let ops = f.body().num_ops();
        assert_eq!(
            message(f.int_arith(ArithOp::Add, Ovf::Nsw, a, w)),
            "int.add.nsw: operands: expected (i32) but got (i64)"
        );
        assert_eq!(
            message(f.int_arith(ArithOp::Add, Ovf::Nsw, p, p)),
            "int.add.nsw: expected integers but got (ptr)"
        );
        assert_eq!(
            message(f.mem_load(i32(), a, 4)),
            "mem.load: operands: expected (ptr) but got (i32)"
        );
        assert_eq!(
            message(f.mem_load(i32(), p, 3)),
            "mem.load: alignment must be a power of two"
        );
        assert_eq!(
            message(f.int_zext(i32(), w)),
            "int.zext: cannot extend i64 to i32"
        );
        assert_eq!(
            message(f.int_trunc(Ty::Int(64), TruncMode::Wrap, a)),
            "int.trunc.wrap: cannot truncate i32 to i64"
        );
        assert_eq!(
            message(f.ptr_cmp(Pred::Slt, p, p)),
            "ptr.cmp.slt: pointer comparisons are unsigned"
        );
        assert_eq!(
            message(f.copy(ValueId::from_raw(99))),
            "copy: value 99 does not exist in this function"
        );
        assert_eq!(f.body().num_ops(), ops, "a rejected op is not added");
        // Result types follow from the operands, and from the address size.
        let s = f.int_arith(ArithOp::Mul, Ovf::Ub(true), w, w).unwrap();
        assert_eq!(f.ty(s), Ty::Int(64));
        let addr = f.ptr_addr(p).unwrap();
        assert_eq!(f.ty(addr), Ty::Int(64));
        let c = f.int_cmp(Pred::Ult, a, a).unwrap();
        assert_eq!(f.ty(c), Ty::Int(1));
    });
}

#[test]
fn calls_check_the_signature_and_declarations_clash() {
    let mut mb = ModuleBuilder::new();
    let g = mb.declare_func("g", &[i32()], &[i32(), Ty::Ptr]).unwrap();
    assert_eq!(
        message(mb.declare_func("g", &[], &[])),
        "@g is defined more than once"
    );
    let s = mb.struct_ty(Policy::C, &[i32()]).unwrap();
    assert_eq!(
        message(mb.declare_func("h", &[s], &[])),
        "func @h: struct<C>{i32} is not a value type"
    );
    assert_eq!(
        message(mb.global("g", i32(), false, 1, Init::Zero)),
        "@g is defined more than once"
    );
    let mut f = mb.func("f", &[Ty::Int(64)], &[]).unwrap();
    let x = f.param(0);
    assert_eq!(
        message(f.func_call(g, &[x.into()])),
        "func.call: arguments of @g: expected (i32) but got (i64)"
    );
    let x32 = f.int_trunc(i32(), TruncMode::Wrap, x).unwrap();
    let r = f.func_call(g, &[x32.into()]).unwrap();
    assert_eq!((f.ty(r.get(0)), f.ty(r.get(1))), (i32(), Ty::Ptr));
    f.func_ret(&[]).unwrap();
    f.finish().unwrap();
    // `@g` is declared but not defined: the verifier says so.
    let m = mb.finish();
    assert_eq!(verify_module(&m).unwrap_err(), "in @f: @?: no function @g");
}

/// Names default to ids, types are copied into each function once, and a builder that
/// continues a parsed module adds after its functions.
#[test]
fn names_types_and_continuing_a_parsed_module() {
    let m =
        parse_module("func @one() -> i32 {\n  %x: i32 = int.const 1\n  func.ret %x\n}\n").unwrap();
    let mut mb = ModuleBuilder::from_module(m).unwrap();
    let one = mb.func_ref("one").unwrap();
    let pair = mb.struct_ty(Policy::C, &[i32(), i32()]).unwrap();
    let mut f = mb.func("two", &[], &[i32()]).unwrap();
    f.set_file(Some("two.c"));
    f.set_loc(Some(Loc { line: 3, col: 7 }));
    let p = f.mem_stack_of(pair, 4).unwrap();
    let q = f.ptr_field(true, pair, p, 1).unwrap();
    f.set_loc(None);
    let x = f.func_call(one, &[]).unwrap().get(0);
    f.name(x, "x").unwrap();
    f.set_facts(x, &[(FactArg::RangeS(1.into(), 1.into()), Trust::Check)])
        .unwrap();
    f.mem_store(i32(), x, q, 4).unwrap();
    let y = f.mem_load(i32(), q, 4).unwrap();
    let two = f.int_arith(ArithOp::Add, Ovf::Nsw, x, y).unwrap();
    f.func_ret(&[two.into()]).unwrap();
    f.finish().unwrap();
    let m = mb.finish();
    verify_module(&m).unwrap();
    assert_eq!(
        m.render(true),
        "func @one() -> i32 {
  %x: i32 = int.const 1
  func.ret %x
}

func @two() -> i32 loc \"two.c\" {
  %0: ptr = mem.stack.of struct<C>{i32, i32}, align 4 @3:7
  %1: ptr = ptr.field.inbounds struct<C>{i32, i32} %0, 1 @3:7
  %x: i32 [range.s(1, 1) check] = func.call @one()
  mem.store i32 %x, %1, align 4
  %3: i32 = mem.load %1, align 4
  %4: i32 = int.add.nsw %x, %3
  func.ret %4
}
"
    );
    assert_eq!(m.funcs[1].body.types().len(), 1);
    assert_eq!(interp::run(&m, "two", &[], 100).unwrap(), "returned i32 2");
}
