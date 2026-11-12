//! Lowering HFIR to MFIR, mirroring `spec/Fir/Lower.lean` so that the result prints exactly as
//! `fir-ref lower` prints Lean's.
//!
//! Lean lowers each function in two passes: scalarizing (aggregates, unions, and slices become
//! their scalars, and the building-block ops become core ops) and expanding (checked arithmetic,
//! `ptr.field`, and `ptr.index` become core ops). The ops expanding changes take and give
//! scalars, and scalarizing passes them through, so one walk does both here: it scalarizes each
//! op into a new [`Body`], expanding those ops as it emits them. Each pass numbers its own
//! temporaries (`%.s0`, … and `%.e0`, …) in the order its ops are emitted, which is the same
//! order in one walk as in two.
//!
//! The walk follows the crate's data-oriented rules: each source value maps to a run of target
//! values in one flat array, and the operand, result, and leaf lists are reused buffers.

use num_bigint::BigInt;

use crate::body::{
    Body, Case, Int, OpId, Operand, OperandKind, RegionId, Succ, ValueId, ValueSpec,
};
use crate::decl::{Imm, Layer};
use crate::ir::*;
use crate::types::Shape;
use crate::verify::render_loc;

/// Lower an HFIR module to MFIR (Lean's `Lower.lowerModule`). Globals and external functions
/// stay as they are.
pub fn lower_module(m: &Module) -> Result<Module, String> {
    if m.layer != Layer::Hfir {
        return Err(format!(
            "lowering takes an HFIR module, not layer {}",
            m.layer
        ));
    }
    let mut funcs = Vec::with_capacity(m.funcs.len());
    for f in &m.funcs {
        funcs.push(lower_func(&m.space, f).map_err(|e| format!("in @{}: {e}", f.name))?);
    }
    Ok(Module {
        layer: Layer::Mfir,
        space: m.space.clone(),
        globals: m.globals.clone(),
        externs: m.externs.clone(),
        funcs,
    })
}

/// Lower a verified HFIR module and verify the result (what `fir lower` and `fir-ref lower` do).
pub fn lower_checked(m: &Module) -> Result<Module, String> {
    let l = lower_module(m)?;
    match crate::verify_module(&l) {
        Ok(_) => Ok(l),
        Err(e) => Err(format!("the lowering doesn't verify: {e}")),
    }
}

/// A value to create in the target, owning its name until it is created.
struct Spec {
    name: String,
    ty: Ty,
    facts: Vec<TrustedFact>,
}

/// Borrow specs as the body wants them.
fn specs(ss: &[Spec]) -> impl Iterator<Item = ValueSpec<'_>> {
    ss.iter().map(|s| ValueSpec {
        name: &s.name,
        ty: s.ty,
        facts: s.facts.clone(),
    })
}

/// A run of target values in [`Lowerer::leaves`].
#[derive(Clone, Copy, Default)]
struct Run {
    start: u32,
    len: u32,
}

struct Lowerer<'a> {
    sp: &'a SpaceCfg,
    aw: u32,
    src: &'a Body,
    dst: Body,
    /// Each source value's scalars, by source id.
    map: Vec<Run>,
    leaves: Vec<ValueId>,
    s_count: u32,
    e_count: u32,
}

fn lower_func(sp: &SpaceCfg, f: &Func) -> Result<Func, String> {
    let src = &f.body;
    let mut lw = Lowerer {
        sp,
        aw: sp.addr_bits,
        src,
        dst: Body::new(),
        map: vec![Run::default(); src.num_values()],
        leaves: Vec::new(),
        s_count: 0,
        e_count: 0,
    };
    let entry = src.entry();
    let params: Vec<ValueId> = src.params(entry).collect();
    let specs_ = lw.explode_values(&params);
    let dentry = lw.dst.entry();
    lw.dst.set_params(dentry, specs(&specs_));
    lw.map_params(&params, dentry);
    lw.region(entry, dentry)?;
    let mut rets = Vec::new();
    for &t in &f.rets {
        let mut ts = Vec::new();
        src.types().scalars(lw.aw, t, &mut ts);
        for t in ts {
            rets.push(lw.dst.types_mut().import(src.types(), t));
        }
    }
    let mut body = lw.dst;
    body.shrink_to_fit();
    Ok(Func {
        name: f.name.clone(),
        rets,
        file: f.file.clone(),
        body,
    })
}

impl<'a> Lowerer<'a> {
    fn import_ty(&mut self, t: Ty) -> Ty {
        self.dst.types_mut().import(self.src.types(), t)
    }

    /// A source fact, with its integers stored in the target.
    fn import_fact(&mut self, f: TrustedFact) -> TrustedFact {
        let fact = match f.fact {
            Fact::RangeS(lo, hi) => Fact::RangeS(self.import_int(lo), self.import_int(hi)),
            Fact::RangeU(lo, hi) => Fact::RangeU(self.import_int(lo), self.import_int(hi)),
            x => x,
        };
        TrustedFact {
            fact,
            trust: f.trust,
        }
    }

    fn import_int(&mut self, n: crate::body::IntId) -> crate::body::IntId {
        match self.src.int(n) {
            Int::Small(n) => self.dst.add_small_int(n),
            Int::Big(n) => self.dst.add_int(n.clone()),
        }
    }

    /// A kind with its immediates stored in the target.
    fn import_kind(&mut self, k: OpKind) -> OpKind {
        let mut k = k;
        for i in 0..k.decl().imms.len() {
            let v = match k.imm(i) {
                Some(Imm::Int(n)) => Imm::Int(self.import_int(n)),
                Some(Imm::Str(s)) => Imm::Str(self.dst.add_str(self.src.str(s))),
                Some(Imm::Ty(t)) => Imm::Ty(self.import_ty(t)),
                Some(Imm::Succ(s)) => {
                    let s = self.src.succ(s);
                    let label = self.dst.add_str(self.src.str(s.label));
                    Imm::Succ(self.dst.add_succ(Succ {
                        label,
                        nargs: s.nargs,
                    }))
                }
                Some(Imm::Cases(c)) => {
                    let cases: Vec<Case> = self.src.cases(c).to_vec();
                    let mut out = Vec::with_capacity(cases.len());
                    for c in cases {
                        let key = self.import_int(c.key);
                        let label = self.dst.add_str(self.src.str(c.succ.label));
                        out.push(Case {
                            key,
                            succ: Succ {
                                label,
                                nargs: c.succ.nargs,
                            },
                        });
                    }
                    Imm::Cases(self.dst.add_cases(out))
                }
                Some(x) => x,
                None => continue,
            };
            k.set_imm(i, v);
        }
        k
    }

    /// The scalar types of a source type, in the target's table (Lean's `scalars`).
    fn scalar_tys(&mut self, t: Ty) -> Vec<Ty> {
        let mut ts = Vec::new();
        self.src.types().scalars(self.aw, t, &mut ts);
        ts.into_iter().map(|t| self.import_ty(t)).collect()
    }

    /// The values a source value becomes (Lean's `explodeResult`).
    fn explode_into(&mut self, v: ValueId, out: &mut Vec<Spec>) {
        let src: &'a Body = self.src;
        let t = src.ty(v);
        if t.is_value() {
            let facts = src.facts(v).to_vec();
            let facts = facts.into_iter().map(|f| self.import_fact(f)).collect();
            let ty = self.import_ty(t);
            out.push(Spec {
                name: src.name(v).to_owned(),
                ty,
                facts,
            });
        } else {
            for (i, ty) in self.scalar_tys(t).into_iter().enumerate() {
                out.push(Spec {
                    name: format!("{}.{i}", src.name(v)),
                    ty,
                    facts: Vec::new(),
                });
            }
        }
    }

    fn explode_values(&mut self, vs: &[ValueId]) -> Vec<Spec> {
        let mut out = Vec::new();
        for &v in vs {
            self.explode_into(v, &mut out);
        }
        out
    }

    /// Record which target values source values became, from consecutive target values.
    fn map_values(&mut self, vs: &[ValueId], targets: impl Iterator<Item = ValueId>) {
        let mut targets = targets;
        for &v in vs {
            let n = self.src.types().num_scalars(self.src.ty(v)) as u32;
            let start = self.leaves.len() as u32;
            for _ in 0..n {
                if let Some(t) = targets.next() {
                    self.leaves.push(t);
                }
            }
            self.map[v.index()] = Run {
                start,
                len: self.leaves.len() as u32 - start,
            };
        }
    }

    fn map_params(&mut self, vs: &[ValueId], r: RegionId) {
        let ps = self.dst.params(r);
        self.map_values(vs, ps);
    }

    fn map_results(&mut self, op: OpId, dop: OpId) {
        let rs: Vec<ValueId> = self.src.results(op).collect();
        let ts = self.dst.results(dop);
        self.map_values(&rs, ts);
    }

    /// The operands a source operand becomes (Lean's `Ctx.explode`).
    fn explode_operand(&mut self, o: Operand, out: &mut Vec<Operand>) {
        match o.get() {
            OperandKind::Value(v) => {
                let r = self.map[v.index()];
                out.extend(
                    self.leaves[r.start as usize..(r.start + r.len) as usize]
                        .iter()
                        .map(|&t| Operand::value(t)),
                );
            }
            OperandKind::Hole(h) => {
                let src: &'a Body = self.src;
                let (name, t) = (src.hole_name(h), src.hole_ty(h));
                if t.is_value() {
                    let t = self.import_ty(t);
                    out.push(self.dst.add_hole(name, t));
                } else {
                    // Holes of the same name, so a run reaches the same hole.
                    for ty in self.scalar_tys(t) {
                        out.push(self.dst.add_hole(name, ty));
                    }
                }
            }
        }
    }

    fn explode_all(&mut self, os: &[Operand]) -> Vec<Operand> {
        let mut out = Vec::new();
        for &o in os {
            self.explode_operand(o, &mut out);
        }
        out
    }

    /// The type of a source operand.
    fn ty_of(&self, o: Operand) -> Ty {
        match o.get() {
            OperandKind::Value(v) => self.src.ty(v),
            OperandKind::Hole(h) => self.src.hole_ty(h),
        }
    }

    fn fresh(&mut self, expand: bool) -> String {
        let (pre, k) = if expand {
            self.e_count += 1;
            ('e', self.e_count - 1)
        } else {
            self.s_count += 1;
            ('s', self.s_count - 1)
        };
        format!(".{pre}{k}")
    }

    fn spec(name: String, ty: Ty) -> Spec {
        Spec {
            name,
            ty,
            facts: Vec::new(),
        }
    }

    /// Append an op without regions, expanding checked arithmetic, `ptr.field`, and `ptr.index`
    /// (Lean's `expandFlat`). Gives the op that defines the results asked for, if any.
    fn emit(
        &mut self,
        r: RegionId,
        k: OpKind,
        operands: Vec<Operand>,
        results: Vec<Spec>,
        loc: Option<Loc>,
    ) -> Result<Vec<ValueId>, String> {
        let aw = self.aw;
        match k {
            OpKind::Overflow { op, signed } if results.len() == 2 && operands.len() == 2 => {
                let mut results = results;
                let ov = results.pop().unwrap();
                let res = results.pop().unwrap();
                let w = match res.ty {
                    Ty::Int(w) => w,
                    _ => 0,
                };
                let wide = Ty::Int(if op == ArithOp::Mul { 2 * w } else { w + 1 });
                let ext = if signed { OpKind::Sext } else { OpKind::Zext };
                let mut names: Vec<String> = (0..4).map(|_| self.fresh(true)).collect();
                let t0 = self.op1(
                    r,
                    ext,
                    &[operands[0]],
                    Self::spec(std::mem::take(&mut names[0]), wide),
                    loc,
                );
                let t1 = self.op1(
                    r,
                    ext,
                    &[operands[1]],
                    Self::spec(std::mem::take(&mut names[1]), wide),
                    loc,
                );
                let t2 = self.op1(
                    r,
                    OpKind::Arith(op, Ovf::Wrap),
                    &[Operand::value(t0), Operand::value(t1)],
                    Self::spec(std::mem::take(&mut names[2]), wide),
                    loc,
                );
                let rv = self.op1(
                    r,
                    OpKind::Trunc(TruncMode::Wrap),
                    &[Operand::value(t2)],
                    res,
                    loc,
                );
                let t3 = self.op1(
                    r,
                    ext,
                    &[Operand::value(rv)],
                    Self::spec(std::mem::take(&mut names[3]), wide),
                    loc,
                );
                let ov = self.op1(
                    r,
                    OpKind::Cmp(Pred::Ne),
                    &[Operand::value(t2), Operand::value(t3)],
                    ov,
                    loc,
                );
                Ok(vec![rv, ov])
            }
            OpKind::PtrField {
                inbounds,
                ty,
                index,
            } if results.len() == 1 && operands.len() == 1 => {
                let off = self
                    .dst
                    .types()
                    .field_offset(self.sp, ty, index)
                    .unwrap_or(0);
                if aw <= 128 && off >= 1u128 << (aw - 1) {
                    return Err(format!(
                        "{}: cannot lower: field {index} of {} is at offset {off}, which doesn't fit a signed i{aw}",
                        render_loc(loc),
                        self.dst.types().show(ty)
                    ));
                }
                let c = self.fresh(true);
                let k = OpKind::Const(self.dst.add_int(BigInt::from(off)));
                let c = self.op1(r, k, &[], Self::spec(c, Ty::Int(aw)), loc);
                let res = results.into_iter().next().unwrap();
                let v = self.op1(
                    r,
                    OpKind::PtrOffset { inbounds },
                    &[operands[0], Operand::value(c)],
                    res,
                    loc,
                );
                Ok(vec![v])
            }
            OpKind::PtrIndex { inbounds, ty } if results.len() == 1 && operands.len() == 2 => {
                let stride = self.dst.types().stride(self.sp, ty);
                if inbounds && aw < 128 && stride >= 1u128 << aw {
                    return Err(format!(
                        "{}: cannot lower: the stride of {}, {stride}, doesn't fit an i{aw}",
                        render_loc(loc),
                        self.dst.types().show(ty)
                    ));
                }
                let res = results.into_iter().next().unwrap();
                let v = if inbounds {
                    let wide = Ty::Int(2 * aw);
                    let mut names: Vec<String> = (0..4).map(|_| self.fresh(true)).collect();
                    let t0 = self.op1(
                        r,
                        OpKind::Sext,
                        &[operands[1]],
                        Self::spec(std::mem::take(&mut names[0]), wide),
                        loc,
                    );
                    let k = OpKind::Const(self.dst.add_int(BigInt::from(stride)));
                    let t1 = self.op1(
                        r,
                        k,
                        &[],
                        Self::spec(std::mem::take(&mut names[1]), wide),
                        loc,
                    );
                    let t2 = self.op1(
                        r,
                        OpKind::Arith(ArithOp::Mul, Ovf::Wrap),
                        &[Operand::value(t0), Operand::value(t1)],
                        Self::spec(std::mem::take(&mut names[2]), wide),
                        loc,
                    );
                    let t3 = self.op1(
                        r,
                        OpKind::Trunc(TruncMode::Nsw),
                        &[Operand::value(t2)],
                        Self::spec(std::mem::take(&mut names[3]), Ty::Int(aw)),
                        loc,
                    );
                    self.op1(
                        r,
                        OpKind::PtrOffset { inbounds: true },
                        &[operands[0], Operand::value(t3)],
                        res,
                        loc,
                    )
                } else {
                    let mut names: Vec<String> = (0..2).map(|_| self.fresh(true)).collect();
                    let k = OpKind::Const(self.dst.add_int(BigInt::from(stride)));
                    let t0 = self.op1(
                        r,
                        k,
                        &[],
                        Self::spec(std::mem::take(&mut names[0]), Ty::Int(aw)),
                        loc,
                    );
                    let t1 = self.op1(
                        r,
                        OpKind::Arith(ArithOp::Mul, Ovf::Wrap),
                        &[operands[1], Operand::value(t0)],
                        Self::spec(std::mem::take(&mut names[1]), Ty::Int(aw)),
                        loc,
                    );
                    self.op1(
                        r,
                        OpKind::PtrOffset { inbounds: false },
                        &[operands[0], Operand::value(t1)],
                        res,
                        loc,
                    )
                };
                Ok(vec![v])
            }
            _ => {
                let op = self.dst.append_op(r, k, operands, specs(&results), [], loc);
                Ok(self.dst.results(op).collect())
            }
        }
    }

    /// Append an op with one result and give the result.
    fn op1(
        &mut self,
        r: RegionId,
        k: OpKind,
        operands: &[Operand],
        result: Spec,
        loc: Option<Loc>,
    ) -> ValueId {
        let op = self.dst.append_op(
            r,
            k,
            operands.iter().copied(),
            specs(std::slice::from_ref(&result)),
            [],
            loc,
        );
        self.dst.results(op).next().unwrap()
    }

    /// Append an op with no results.
    fn op0(&mut self, r: RegionId, k: OpKind, operands: &[Operand], loc: Option<Loc>) {
        self.dst
            .append_op(r, k, operands.iter().copied(), [], [], loc);
    }

    /// Copies of `from` into results `to` (Lean's `copies`), mapped to source result `res`.
    fn copies(
        &mut self,
        r: RegionId,
        to: Vec<Spec>,
        from: &[Operand],
        loc: Option<Loc>,
    ) -> Vec<ValueId> {
        let mut out = Vec::new();
        for (spec, &o) in to.into_iter().zip(from) {
            out.push(self.op1(r, OpKind::Copy, &[o], spec, loc));
        }
        out
    }

    /// The address of the leaf at offset `off` of an aggregate at `p` (Lean's `leafAddr`).
    fn leaf_addr(&mut self, r: RegionId, p: Operand, off: u128, loc: Option<Loc>) -> Operand {
        if off == 0 {
            return p;
        }
        let aw = self.aw;
        let c = self.fresh(false);
        let q = self.fresh(false);
        let k = OpKind::Const(self.dst.add_int(BigInt::from(off)));
        let c = self.op1(r, k, &[], Self::spec(c, Ty::Int(aw)), loc);
        let q = self.op1(
            r,
            OpKind::PtrOffset { inbounds: false },
            &[p, Operand::value(c)],
            Self::spec(q, Ty::Ptr),
            loc,
        );
        Operand::value(q)
    }

    /// A load of a value of source type `t` from `p` into `results` (Lean's `loadTo`).
    fn load_to(
        &mut self,
        r: RegionId,
        t: Ty,
        results: Vec<Spec>,
        align: u32,
        p: Operand,
        loc: Option<Loc>,
    ) -> Vec<ValueId> {
        if t.is_value() {
            return results
                .into_iter()
                .map(|spec| self.op1(r, OpKind::Load { align }, &[p], spec, loc))
                .collect();
        }
        let mut leaves = Vec::new();
        self.src.types().leaves(self.sp, t, 0, &mut leaves);
        let mut out = Vec::new();
        for (&(off, _), spec) in leaves.iter().zip(results) {
            let q = self.leaf_addr(r, p, off, loc);
            let a = leaf_align(align, off);
            out.push(self.op1(r, OpKind::Load { align: a }, &[q], spec, loc));
        }
        out
    }

    /// A store of a value of source type `t`, as scalars `vs`, to `p` (Lean's `storeFrom`).
    fn store_from(
        &mut self,
        r: RegionId,
        t: Ty,
        align: u32,
        vs: &[Operand],
        p: Operand,
        loc: Option<Loc>,
    ) {
        if t.is_value() {
            let ty = self.import_ty(t);
            let mut ops = vs.to_vec();
            ops.push(p);
            self.op0(r, OpKind::Store { ty, align }, &ops, loc);
            return;
        }
        let mut leaves = Vec::new();
        self.src.types().leaves(self.sp, t, 0, &mut leaves);
        for (&(off, lt), &v) in leaves.iter().zip(vs) {
            let q = self.leaf_addr(r, p, off, loc);
            let ty = self.import_ty(lt);
            let a = leaf_align(align, off);
            self.op0(r, OpKind::Store { ty, align: a }, &[v, q], loc);
        }
    }

    /// The address of element `i` of a slice (Lean's `elemAddr`).
    #[allow(clippy::too_many_arguments)]
    fn elem_addr(
        &mut self,
        r: RegionId,
        trap: bool,
        t: Ty,
        p: Operand,
        n: Operand,
        i: Operand,
        loc: Option<Loc>,
    ) -> Operand {
        let aw = self.aw;
        if trap {
            let ok = self.fresh(false);
            let ok = self.op1(
                r,
                OpKind::Cmp(Pred::Ult),
                &[i, n],
                Self::spec(ok, Ty::Int(1)),
                loc,
            );
            self.op0(
                r,
                OpKind::Check(TrapReason::Bounds),
                &[Operand::value(ok)],
                loc,
            );
        }
        let st = self.fresh(false);
        let off = self.fresh(false);
        let q = self.fresh(false);
        let stride = self.src.types().stride(self.sp, t);
        let k = OpKind::Const(self.dst.add_int(BigInt::from(stride)));
        let st = self.op1(r, k, &[], Self::spec(st, Ty::Int(aw)), loc);
        let off = self.op1(
            r,
            OpKind::Arith(ArithOp::Mul, Ovf::Wrap),
            &[i, Operand::value(st)],
            Self::spec(off, Ty::Int(aw)),
            loc,
        );
        let q = self.op1(
            r,
            OpKind::PtrOffset { inbounds: true },
            &[p, Operand::value(off)],
            Self::spec(q, Ty::Ptr),
            loc,
        );
        Operand::value(q)
    }

    /// Lower the ops of source region `sr` into target region `dr`.
    fn region(&mut self, sr: RegionId, dr: RegionId) -> Result<(), String> {
        let ops: Vec<OpId> = self.src.ops(sr).collect();
        for op in ops {
            self.op(op, dr)?;
        }
        Ok(())
    }

    fn op(&mut self, op: OpId, r: RegionId) -> Result<(), String> {
        let src: &'a Body = self.src;
        let k = src.kind(op);
        let loc = src.loc(op);
        let args = src.operands(op);
        let rs: Vec<ValueId> = src.results(op).collect();
        let regions = src.regions(op);
        let mut specs = Vec::new();
        for &v in &rs {
            self.explode_into(v, &mut specs);
        }
        if !regions.is_empty() {
            let operands = self.explode_all(args);
            let k = self.import_kind(k);
            let mut params = Vec::with_capacity(regions.len());
            for &sr in regions {
                let ps: Vec<ValueId> = src.params(sr).collect();
                params.push(self.explode_values(&ps));
            }
            let dop = self.dst.append_op(
                r,
                k,
                operands,
                self::specs(&specs),
                params.iter().map(|ps| self::specs(ps).collect::<Vec<_>>()),
                loc,
            );
            self.map_results(op, dop);
            for (i, &sr) in regions.iter().enumerate() {
                let dr = self.dst.regions(dop)[i];
                if let Some(l) = src.label(sr) {
                    let l = self.dst.add_str(src.str(l));
                    self.dst.set_label(dr, l);
                }
                let ps: Vec<ValueId> = src.params(sr).collect();
                self.map_params(&ps, dr);
                self.region(sr, dr)?;
            }
            return Ok(());
        }
        let types = src.types();
        let defined: Vec<ValueId> = match (k, rs.len(), args) {
            (OpKind::AggMake | OpKind::Copy | OpKind::SliceMake, 1, _) => {
                let from = self.explode_all(args);
                self.copies(r, specs, &from, loc)
            }
            (OpKind::AggExtract { index }, 1, &[a]) => {
                let (start, n) = part_range(types, self.ty_of(a), index);
                let mut la = Vec::new();
                self.explode_operand(a, &mut la);
                let from: Vec<Operand> = la.into_iter().skip(start).take(n).collect();
                self.copies(r, specs, &from, loc)
            }
            (OpKind::AggInsert { index }, 1, &[a, v]) => {
                let (start, n) = part_range(types, self.ty_of(a), index);
                let mut la = Vec::new();
                self.explode_operand(a, &mut la);
                let mut from: Vec<Operand> = la.iter().copied().take(start).collect();
                self.explode_operand(v, &mut from);
                from.extend(la.iter().copied().skip(start + n));
                self.copies(r, specs, &from, loc)
            }
            (OpKind::UnionMake { index }, 1, &[v]) => {
                let (start, n) = variant_range(types, src.ty(rs[0]), index);
                let mut lv = Vec::new();
                self.explode_operand(v, &mut lv);
                let mut out = Vec::new();
                for (j, spec) in specs.into_iter().enumerate() {
                    let d = if j == 0 {
                        let k = OpKind::Const(self.dst.add_small_int(i64::from(index)));
                        self.op1(r, k, &[], spec, loc)
                    } else if start <= j && j < start + n {
                        let from = lv.get(j - start).copied().unwrap_or(v);
                        self.op1(r, OpKind::Copy, &[from], spec, loc)
                    } else {
                        self.op1(r, OpKind::Poison, &[], spec, loc)
                    };
                    out.push(d);
                }
                out
            }
            (OpKind::UnionTag | OpKind::SlicePtr, 1, &[u]) => {
                let mut lu = Vec::new();
                self.explode_operand(u, &mut lu);
                lu.truncate(1);
                self.copies(r, specs, &lu, loc)
            }
            (OpKind::SliceLen, 1, &[s]) => {
                let mut ls = Vec::new();
                self.explode_operand(s, &mut ls);
                let from: Vec<Operand> = ls.into_iter().skip(1).collect();
                self.copies(r, specs, &from, loc)
            }
            (OpKind::UnionGet { trap, index }, 1, &[u]) => {
                let mut lu = Vec::new();
                self.explode_operand(u, &mut lu);
                let (start, n) = variant_range(types, self.ty_of(u), index);
                if trap {
                    let c = self.fresh(false);
                    let ok = self.fresh(false);
                    let k = OpKind::Const(self.dst.add_small_int(i64::from(index)));
                    let c = self.op1(r, k, &[], Self::spec(c, Ty::Int(32)), loc);
                    let tag = lu.first().copied().unwrap_or(u);
                    let ok = self.op1(
                        r,
                        OpKind::Cmp(Pred::Eq),
                        &[tag, Operand::value(c)],
                        Self::spec(ok, Ty::Int(1)),
                        loc,
                    );
                    self.op0(
                        r,
                        OpKind::Check(TrapReason::Tag),
                        &[Operand::value(ok)],
                        loc,
                    );
                }
                let from: Vec<Operand> = lu.into_iter().skip(start).take(n).collect();
                self.copies(r, specs, &from, loc)
            }
            (OpKind::SliceGet { trap, align }, 1, &[s, i]) => {
                let mut ls = Vec::new();
                self.explode_operand(s, &mut ls);
                let (p, n) = (
                    ls.first().copied().unwrap_or(s),
                    ls.get(1).copied().unwrap_or(s),
                );
                let mut li = Vec::new();
                self.explode_operand(i, &mut li);
                let i = li.first().copied().unwrap_or(i);
                let t = src.ty(rs[0]);
                let q = self.elem_addr(r, trap, t, p, n, i, loc);
                self.load_to(r, t, specs, align, q, loc)
            }
            (OpKind::SliceSet { trap, ty, align }, 0, &[v, s, i]) => {
                let mut ls = Vec::new();
                self.explode_operand(s, &mut ls);
                let (p, n) = (
                    ls.first().copied().unwrap_or(s),
                    ls.get(1).copied().unwrap_or(s),
                );
                let mut li = Vec::new();
                self.explode_operand(i, &mut li);
                let i = li.first().copied().unwrap_or(i);
                let q = self.elem_addr(r, trap, ty, p, n, i, loc);
                let mut lv = Vec::new();
                self.explode_operand(v, &mut lv);
                self.store_from(r, ty, align, &lv, q, loc);
                Vec::new()
            }
            (OpKind::Load { align }, 1, &[p]) => {
                let mut lp = Vec::new();
                self.explode_operand(p, &mut lp);
                let p = lp.first().copied().unwrap_or(p);
                self.load_to(r, src.ty(rs[0]), specs, align, p, loc)
            }
            (OpKind::Store { ty, align }, 0, &[v, p]) => {
                let mut lp = Vec::new();
                self.explode_operand(p, &mut lp);
                let p = lp.first().copied().unwrap_or(p);
                let mut lv = Vec::new();
                self.explode_operand(v, &mut lv);
                self.store_from(r, ty, align, &lv, p, loc);
                Vec::new()
            }
            _ => {
                let (k, operands) = self.fix_succs(k, args);
                self.emit(r, k, operands, specs, loc)?
            }
        };
        let rs_src: Vec<ValueId> = rs;
        self.map_values(&rs_src, defined.into_iter());
        Ok(())
    }

    /// A flat op's kind, with its immediates in the target and its branch targets' argument
    /// counts to match its operands replaced by their scalars (Lean's `fixSuccs`).
    fn fix_succs(&mut self, k: OpKind, args: &[Operand]) -> (OpKind, Vec<Operand>) {
        let src: &'a Body = self.src;
        let k2 = self.import_kind(k);
        let with_nargs = |me: &mut Self, s: crate::body::SuccId, n: usize| {
            let s = me.dst.succ(s);
            me.dst.add_succ(Succ {
                label: s.label,
                nargs: n as u32,
            })
        };
        match (k, k2) {
            (OpKind::Br { .. }, OpKind::Br { dest }) => {
                let a = self.explode_all(args);
                let dest = with_nargs(self, dest, a.len());
                (OpKind::Br { dest }, a)
            }
            (OpKind::CondBr { t: st, .. }, OpKind::CondBr { t, f }) if !args.is_empty() => {
                let tn = src.succ(st).nargs as usize;
                let rest = &args[1..];
                let tn = tn.min(rest.len());
                let ta = self.explode_all(&rest[..tn]);
                let fa = self.explode_all(&rest[tn..]);
                let t = with_nargs(self, t, ta.len());
                let f = with_nargs(self, f, fa.len());
                let mut ops = self.explode_all(&args[..1]);
                ops.extend(ta);
                ops.extend(fa);
                (OpKind::CondBr { t, f }, ops)
            }
            (
                OpKind::Switch {
                    dflt: sd,
                    cases: sc,
                },
                OpKind::Switch { dflt, cases },
            ) if !args.is_empty() => {
                let rest = &args[1..];
                let mut at = (src.succ(sd).nargs as usize).min(rest.len());
                let da = self.explode_all(&rest[..at]);
                let dflt = with_nargs(self, dflt, da.len());
                let src_cases: Vec<Case> = src.cases(sc).to_vec();
                let dst_cases: Vec<Case> = self.dst.cases(cases).to_vec();
                let mut ca = Vec::new();
                let mut out = Vec::with_capacity(dst_cases.len());
                for (sc, dc) in src_cases.iter().zip(&dst_cases) {
                    let end = (at + sc.succ.nargs as usize).min(rest.len());
                    let a = self.explode_all(&rest[at..end]);
                    at = end;
                    out.push(Case {
                        key: dc.key,
                        succ: Succ {
                            label: dc.succ.label,
                            nargs: a.len() as u32,
                        },
                    });
                    ca.extend(a);
                }
                let cases = self.dst.add_cases(out);
                let mut ops = self.explode_all(&args[..1]);
                ops.extend(da);
                ops.extend(ca);
                (OpKind::Switch { dflt, cases }, ops)
            }
            (_, OpKind::CallIndirect(sig)) => {
                let flat = match self.dst.types().shape_of(sig) {
                    Some(Shape::Func(ps, rs)) => {
                        let (ps, rs) = (ps.to_vec(), rs.to_vec());
                        let mut fps = Vec::new();
                        let mut frs = Vec::new();
                        for t in ps {
                            self.dst.types().scalars(self.aw, t, &mut fps);
                        }
                        for t in rs {
                            self.dst.types().scalars(self.aw, t, &mut frs);
                        }
                        self.dst.types_mut().func(&fps, &frs)
                    }
                    _ => sig,
                };
                (OpKind::CallIndirect(flat), self.explode_all(args))
            }
            (_, k2) => (k2, self.explode_all(args)),
        }
    }
}

/// Where part `i` of a struct or array type starts among its scalars, and how many it has
/// (Lean's `partRange`).
fn part_range(types: &Types, t: Ty, i: u32) -> (usize, usize) {
    match types.shape_of(t) {
        Some(Shape::Struct(_, fs)) => {
            let start = fs
                .iter()
                .take(i as usize)
                .map(|&f| types.num_scalars(f))
                .sum();
            let n = fs.get(i as usize).map_or(1, |&f| types.num_scalars(f));
            (start, n)
        }
        Some(Shape::Array(_, e)) => {
            let k = types.num_scalars(e);
            (i as usize * k, k)
        }
        _ => (0, 0),
    }
}

/// Where variant `i` of a union type starts among its scalars, and how many it has (Lean's
/// `variantRange`).
fn variant_range(types: &Types, t: Ty, i: u32) -> (usize, usize) {
    match types.shape_of(t) {
        Some(Shape::Union(vs)) => {
            let start = 1 + vs
                .iter()
                .take(i as usize)
                .map(|&v| types.num_scalars(v))
                .sum::<usize>();
            let n = vs.get(i as usize).map_or(1, |&v| types.num_scalars(v));
            (start, n)
        }
        _ => (0, 0),
    }
}

/// `Nat.gcd align off`, the alignment a leaf keeps.
fn leaf_align(align: u32, off: u128) -> u32 {
    let (mut a, mut b) = (u128::from(align), off);
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a as u32
}
