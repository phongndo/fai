//! The verifier, mirroring `spec/Fir/Verify.lean`: the same rules, checked in the same order,
//! with the same messages, so the first error matches the Lean reference tool's (`fir-ref
//! check`) byte for byte.
//!
//! The parser already resolves names, so for parsed modules it reports undefined and repeated
//! values itself (with a `line:col:` position). The checks here still cover modules built
//! directly.

use rustc_hash::{FxHashMap, FxHashSet};

use num_bigint::{BigInt, Sign};

use crate::body::{Body, Int, OpId, Operand, OperandKind, RegionId, Succ, ValueId};
use crate::decl::{Check, Imm, TyE};
use crate::ir::*;

/// A hole (`?name: T`) found while verifying: the type it must have, and the location of its op.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Hole {
    pub name: String,
    pub ty: Ty,
    pub loc: Option<Loc>,
}

/// `@line:col`, or `@?` without a location (Lean's `Loc.render`).
pub fn render_loc(loc: Option<Loc>) -> String {
    match loc {
        Some(l) => format!("@{}:{}", l.line, l.col),
        None => "@?".to_owned(),
    }
}

/// Verify a module. On success, returns the holes it contains, in order.
pub fn verify_module(m: &Module) -> Result<Vec<Hole>, String> {
    let sp = m.space;
    if !(sp.ptr_bits > 0
        && sp.ptr_bits.is_multiple_of(8)
        && sp.addr_bits > 0
        && sp.addr_bits.is_multiple_of(8)
        && sp.addr_bits <= sp.ptr_bits)
    {
        return Err(format!(
            "memspace: pointer size {} and address size {} must be positive multiples of 8, with the address size at most the pointer size",
            sp.ptr_bits, sp.addr_bits
        ));
    }
    let mut sigs = FxHashMap::default();
    for f in &m.funcs {
        if sigs.contains_key(f.name.as_str()) {
            return Err(format!("function @{} is defined more than once", f.name));
        }
        let entry = f.body.entry();
        let params: Vec<Ty> = f.body.params(entry).map(|v| f.body.ty(v)).collect();
        sigs.insert(f.name.as_str(), (params, f.rets.clone()));
    }
    let mut holes = Vec::new();
    for f in &m.funcs {
        let mut v = FuncVerifier {
            body: &f.body,
            space: sp,
            sigs: &sigs,
            holes: &mut holes,
            defined: FxHashSet::default(),
            visible: vec![false; f.body.num_values()],
            scope: Vec::new(),
            ctx: Vec::new(),
        };
        v.func(&f.rets)
            .map_err(|e| format!("in @{}: {e}", f.name))?;
    }
    Ok(holes)
}

type VResult<T> = Result<T, String>;

fn verr<T>(loc: Option<Loc>, msg: impl std::fmt::Display) -> VResult<T> {
    Err(format!("{}: {msg}", render_loc(loc)))
}

/// The region being checked (Lean's `RegionCtx`).
enum RegionCtx<'a> {
    Func(Vec<Ty>),
    IfBranch(Vec<Ty>),
    LoopBody {
        params: Vec<Ty>,
        results: Vec<Ty>,
    },
    /// A block of `cf.blocks`: the labels of its blocks with their parameter types, and the
    /// `cf.blocks`'s results. One entry serves all the blocks of a `cf.blocks`.
    Block {
        blocks: Vec<(&'a str, Vec<Ty>)>,
        results: Vec<Ty>,
    },
}

fn check_ty(loc: Option<Loc>, t: Ty) -> VResult<()> {
    match t {
        Ty::Int(0) => verr(loc, "i0 is not a valid type"),
        Ty::Byte(w) if !(w > 0 && w.is_multiple_of(8)) => {
            verr(loc, format!("b{w} is not a valid type"))
        }
        _ => Ok(()),
    }
}

fn width(t: Ty) -> u32 {
    match t {
        Ty::Int(w) | Ty::Byte(w) => w,
        Ty::Ptr => 0,
    }
}

fn is_int(t: Ty) -> bool {
    matches!(t, Ty::Int(_))
}

fn is_pow2(n: u64) -> bool {
    n > 0 && n & (n - 1) == 0
}

/// `-2^(w-1) ≤ n < 2^(w-1)`, with `w - 1` truncated at 0 as for Lean's naturals (so `i0`
/// holds `-1` and `0`).
fn fits_signed(w: u32, n: Int<'_>) -> bool {
    let k = w.saturating_sub(1);
    match n {
        // Every `i64` fits once `k ≥ 63`.
        Int::Small(n) => k >= 63 || (-(1i128 << k)..1i128 << k).contains(&i128::from(n)),
        Int::Big(n) => {
            let k = u64::from(k);
            if n.sign() == Sign::Minus {
                (-n - 1u32).bits() <= k
            } else {
                n.bits() <= k
            }
        }
    }
}

/// `0 ≤ n < 2^w`
fn fits_unsigned(w: u32, n: Int<'_>) -> bool {
    match n {
        Int::Small(n) => n >= 0 && (w >= 63 || n < 1i64 << w),
        Int::Big(n) => n.sign() != Sign::Minus && n.bits() <= u64::from(w),
    }
}

/// `a ≤ b`
fn int_le(a: Int<'_>, b: Int<'_>) -> bool {
    match (a, b) {
        (Int::Small(a), Int::Small(b)) => a <= b,
        _ => a.to_bigint() <= b.to_bigint(),
    }
}

fn check_fact(
    body: &Body,
    loc: Option<Loc>,
    is_param: bool,
    name: &str,
    t: Ty,
    fact: TrustedFact,
) -> VResult<()> {
    match fact.fact {
        Fact::RangeS(lo, hi) => {
            let (lo, hi) = (body.int(lo), body.int(hi));
            if !(is_int(t)
                && fits_signed(width(t), lo)
                && fits_signed(width(t), hi)
                && int_le(lo, hi))
            {
                return verr(
                    loc,
                    format!("range.s({lo}, {hi}) is not a valid signed range for {t}"),
                );
            }
        }
        Fact::RangeU(lo, hi) => {
            let (lo, hi) = (body.int(lo), body.int(hi));
            if !(is_int(t)
                && fits_unsigned(width(t), lo)
                && fits_unsigned(width(t), hi)
                && int_le(lo, hi))
            {
                return verr(
                    loc,
                    format!("range.u({lo}, {hi}) is not a valid unsigned range for {t}"),
                );
            }
        }
        Fact::NonNull => {
            if t != Ty::Ptr {
                return verr(loc, format!("nonnull applies to pointers, not {t}"));
            }
        }
        Fact::Align(n) => {
            if !(t == Ty::Ptr && is_pow2(n)) {
                return verr(
                    loc,
                    format!("align({n}) needs a pointer and a power of two"),
                );
            }
        }
        Fact::NoAlias | Fact::ReadOnly => {
            if !(t == Ty::Ptr && is_param) {
                return verr(
                    loc,
                    format!(
                        "%{name}: noalias and readonly apply only to pointer parameters of functions"
                    ),
                );
            }
        }
    }
    Ok(())
}

/// An op's operand or result types. The usual few stay off the heap.
struct Tys {
    len: usize,
    flat: [Ty; 4],
    spill: Vec<Ty>,
}

impl Default for Tys {
    fn default() -> Tys {
        Tys {
            len: 0,
            flat: [Ty::Ptr; 4],
            spill: Vec::new(),
        }
    }
}

impl Tys {
    fn push(&mut self, t: Ty) {
        if self.spill.is_empty() && self.len < self.flat.len() {
            self.flat[self.len] = t;
            self.len += 1;
        } else {
            if self.spill.is_empty() {
                self.spill.extend_from_slice(&self.flat[..self.len]);
            }
            self.spill.push(t);
        }
    }
}

impl std::ops::Deref for Tys {
    type Target = [Ty];

    fn deref(&self) -> &[Ty] {
        if self.spill.is_empty() {
            &self.flat[..self.len]
        } else {
            &self.spill
        }
    }
}

/// `(t1, t2)`
fn tys(ts: &[Ty]) -> String {
    let parts: Vec<String> = ts.iter().map(Ty::to_string).collect();
    format!("({})", parts.join(", "))
}

fn expect_tys(loc: Option<Loc>, what: &str, got: &[Ty], want: &[Ty]) -> VResult<()> {
    if got == want {
        Ok(())
    } else {
        verr(
            loc,
            format!("{what}: expected {} but got {}", tys(want), tys(got)),
        )
    }
}

fn is_loadable(space: SpaceCfg, t: Ty) -> bool {
    match t {
        Ty::Int(w) => w.is_multiple_of(8),
        Ty::Ptr => space.ptr_bits.is_multiple_of(8),
        Ty::Byte(_) => true,
    }
}

fn ints(loc: Option<Loc>, ts: &[Ty]) -> VResult<()> {
    if ts.iter().all(|t| is_int(*t)) {
        Ok(())
    } else {
        verr(loc, format!("expected integers but got {}", tys(ts)))
    }
}

/// Check the operand and result types of an op without regions by its declared rule (Lean's
/// `checkSimple`).
fn check_simple(
    body: &Body,
    loc: Option<Loc>,
    space: SpaceCfg,
    sigs: &FxHashMap<&str, (Vec<Ty>, Vec<Ty>)>,
    k: OpKind,
    ins: &[Ty],
    outs: &[Ty],
) -> VResult<()> {
    let Some(rule) = k.decl().rule else {
        return verr(loc, "unexpected op");
    };
    // The types named so far.
    let mut vars = [Ty::Ptr; 4];
    let mut named = 0;
    let field = |i: u8| k.imm(i.into());
    for check in rule {
        let ty = |e: &TyE| match *e {
            TyE::Ptr => Ty::Ptr,
            TyE::Addr => Ty::Int(space.addr_bits),
            TyE::Int(w) => Ty::Int(w),
            TyE::Var(i) => vars[usize::from(i)],
            TyE::Field(i) => match field(i) {
                Some(Imm::Ty(t)) => t,
                _ => Ty::Ptr,
            },
        };
        let tys_of = |es: &[TyE]| -> Tys {
            let mut ts = Tys::default();
            for e in es {
                ts.push(ty(e));
            }
            ts
        };
        // Compare without building the expected list, unless the message needs it.
        let same = |got: &[Ty], want: &[TyE]| {
            got.len() == want.len() && got.iter().zip(want).all(|(g, w)| *g == ty(w))
        };
        match *check {
            Check::TakeIns(n, msg) | Check::TakeOuts(n, msg) => {
                let got = if matches!(check, Check::TakeIns(..)) {
                    ins
                } else {
                    outs
                };
                if got.len() != usize::from(n) {
                    return verr(loc, msg);
                }
                vars[named..named + got.len()].copy_from_slice(got);
                named += got.len();
            }
            Check::Ins(label, want) => {
                if !same(ins, want) {
                    expect_tys(loc, label, ins, &tys_of(want))?;
                }
            }
            Check::Outs(want) => {
                if !same(outs, want) {
                    expect_tys(loc, "results", outs, &tys_of(want))?;
                }
            }
            Check::NoOuts => {
                if !outs.is_empty() {
                    return verr(loc, "this op has no results");
                }
            }
            Check::Same(label, got, want) => {
                let got = tys_of(got);
                if !same(&got, want) {
                    expect_tys(loc, label, &got, &tys_of(want))?;
                }
            }
            Check::Ints(ts) => {
                if !ts.iter().all(|e| is_int(ty(e))) {
                    ints(loc, &tys_of(ts))?;
                }
            }
            Check::Pow2(i) => {
                let Some(Imm::Align(align)) = field(i) else {
                    return verr(loc, "malformed op");
                };
                if !is_pow2(align.into()) {
                    return verr(loc, "alignment must be a power of two");
                }
            }
            Check::Fits(i, t) => {
                let Some(Imm::Int(n)) = field(i) else {
                    return verr(loc, "malformed op");
                };
                let (n, t) = (body.int(n), ty(&t));
                if !(fits_signed(width(t), n) || fits_unsigned(width(t), n)) {
                    return verr(loc, format!("{n} does not fit in {t}"));
                }
            }
            Check::Widens(a, t) => {
                let (a, t) = (ty(&a), ty(&t));
                if width(t) <= width(a) {
                    return verr(loc, format!("cannot extend {a} to {t}"));
                }
            }
            Check::Narrows(a, t) => {
                let (a, t) = (ty(&a), ty(&t));
                if width(t) >= width(a) {
                    return verr(loc, format!("cannot truncate {a} to {t}"));
                }
            }
            Check::Loadable(t, verb) => {
                let t = ty(&t);
                if !is_loadable(space, t) {
                    return verr(
                        loc,
                        format!("{t} can't be {verb}: its size isn't whole bytes"),
                    );
                }
            }
            Check::Deny(names, msg) => {
                if names.contains(&k.mnemonic()) {
                    return verr(loc, msg);
                }
            }
            Check::Call(i) => {
                let Some(Imm::Str(callee)) = field(i) else {
                    return verr(loc, "malformed op");
                };
                let callee = body.str(callee);
                let Some((params, rets)) = sigs.get(callee) else {
                    return verr(loc, format!("no function @{callee}"));
                };
                expect_tys(loc, &format!("arguments of @{callee}"), ins, params)?;
                expect_tys(loc, &format!("results of @{callee}"), outs, rets)?;
            }
        }
    }
    Ok(())
}

/// Verifies one function. Lean threads a name-to-type scope through the ops; here the visible
/// values are a stack (`scope`) that is cut back when a region ends, mirrored in a set
/// (`visible`) for lookups.
struct FuncVerifier<'a> {
    body: &'a Body,
    space: SpaceCfg,
    sigs: &'a FxHashMap<&'a str, (Vec<Ty>, Vec<Ty>)>,
    holes: &'a mut Vec<Hole>,
    /// Every name defined so far in the function.
    defined: FxHashSet<&'a str>,
    /// Whether each value is visible here, by id.
    visible: Vec<bool>,
    scope: Vec<ValueId>,
    /// The enclosing regions, innermost last.
    ctx: Vec<RegionCtx<'a>>,
}

impl<'a> FuncVerifier<'a> {
    fn func(&mut self, rets: &[Ty]) -> VResult<()> {
        for &t in rets {
            check_ty(None, t)?;
        }
        let entry = self.body.entry();
        for v in self.body.params(entry) {
            self.define(None, v, true)?;
        }
        self.ctx.push(RegionCtx::Func(rets.to_vec()));
        self.ops(entry, None)
    }

    fn define(&mut self, loc: Option<Loc>, v: ValueId, is_param: bool) -> VResult<()> {
        let body = self.body;
        let (name, ty) = (body.name(v), body.ty(v));
        check_ty(loc, ty)?;
        for f in body.facts(v) {
            check_fact(body, loc, is_param, name, ty, *f)?;
        }
        if !self.defined.insert(name) {
            return verr(loc, format!("%{name} is defined more than once"));
        }
        self.visible[v.index()] = true;
        self.scope.push(v);
        Ok(())
    }

    /// Forget the values defined since the scope had `mark` entries.
    fn restore(&mut self, mark: usize) {
        for v in self.scope.drain(mark..) {
            self.visible[v.index()] = false;
        }
    }

    fn operand_ty(&mut self, loc: Option<Loc>, operand: Operand) -> VResult<Ty> {
        match operand.get() {
            OperandKind::Value(v) => {
                if self.visible[v.index()] {
                    Ok(self.body.ty(v))
                } else {
                    verr(loc, format!("%{} is not defined here", self.body.name(v)))
                }
            }
            OperandKind::Hole(h) => {
                let ty = self.body.hole_ty(h);
                check_ty(loc, ty)?;
                self.holes.push(Hole {
                    name: self.body.hole_name(h).to_owned(),
                    ty,
                    loc,
                });
                Ok(ty)
            }
        }
    }

    /// Check the ops of `region`, whose context is the top of `ctx`. Values it defines are
    /// visible only inside it. Lean's `verifyOps`.
    fn ops(&mut self, region: RegionId, region_loc: Option<Loc>) -> VResult<()> {
        let mark = self.scope.len();
        let mut ops = self.body.ops(region).peekable();
        while let Some(op) = ops.next() {
            self.op(op)?;
            if self.body.kind(op).is_terminator() {
                if ops.peek().is_some() {
                    return verr(
                        self.body.loc(op),
                        "a terminator must be the last op of its region",
                    );
                }
                self.restore(mark);
                return Ok(());
            }
        }
        match self.ctx.last() {
            Some(RegionCtx::IfBranch(rs)) if rs.is_empty() => {}
            Some(RegionCtx::IfBranch(_)) => {
                return verr(region_loc, "this cf.if region must end with cf.yield");
            }
            Some(RegionCtx::LoopBody { .. }) => {
                return verr(
                    region_loc,
                    "a loop body must end with cf.break or cf.continue",
                );
            }
            Some(RegionCtx::Block { .. }) => {
                return verr(region_loc, "a block must end with a terminator");
            }
            _ => return verr(region_loc, "the function body must end with func.ret"),
        }
        self.restore(mark);
        Ok(())
    }

    fn nearest_loop(&self) -> Option<(&[Ty], &[Ty])> {
        self.ctx.iter().rev().find_map(|c| match c {
            RegionCtx::LoopBody { params, results } => Some((&params[..], &results[..])),
            _ => None,
        })
    }

    /// The blocks of the nearest enclosing `cf.blocks`.
    fn nearest_blocks(&self) -> Option<&[(&'a str, Vec<Ty>)]> {
        self.ctx.iter().rev().find_map(|c| match c {
            RegionCtx::Block { blocks, .. } => Some(&blocks[..]),
            _ => None,
        })
    }

    /// Check a jump to `s` with arguments of types `args` (Lean's `checkSucc`).
    fn check_succ(&self, loc: Option<Loc>, s: Succ, args: &[Ty]) -> VResult<()> {
        let label = self.body.str(s.label);
        let blocks = self.nearest_blocks().unwrap_or_default();
        let Some((_, ps)) = blocks.iter().find(|(l, _)| *l == label) else {
            return verr(loc, format!("no block ^{label} in the enclosing cf.blocks"));
        };
        expect_tys(loc, &format!("arguments of ^{label}"), args, ps)
    }

    /// Check jumps to `targets`, whose arguments are `args` in order (Lean's `splitArgs`).
    fn check_succs(
        &self,
        loc: Option<Loc>,
        targets: impl Iterator<Item = Succ>,
        args: &[Ty],
    ) -> VResult<()> {
        let mut next = 0;
        for s in targets {
            let end = next + s.nargs as usize;
            self.check_succ(loc, s, &args[next..end])?;
            next = end;
        }
        Ok(())
    }

    /// `cf.blocks` (Lean's `verifyOp` on `.blocks`).
    fn blocks(
        &mut self,
        loc: Option<Loc>,
        ins: &[Ty],
        outs: &[Ty],
        rs: &[RegionId],
    ) -> VResult<()> {
        let body = self.body;
        if !ins.is_empty() {
            return verr(loc, "malformed op");
        }
        let Some(&entry) = rs.first() else {
            return verr(loc, "cf.blocks needs at least one block");
        };
        let mut blocks: Vec<(&'a str, Vec<Ty>)> = Vec::with_capacity(rs.len());
        let mut seen = FxHashSet::default();
        for &r in rs {
            let Some(l) = body.label(r) else {
                return verr(loc, "every block of cf.blocks needs a label");
            };
            let l = body.str(l);
            if !seen.insert(l) {
                return verr(loc, format!("block ^{l} is defined more than once"));
            }
            blocks.push((l, body.params(r).map(|v| body.ty(v)).collect()));
        }
        if body.params(entry).len() != 0 {
            return verr(loc, "the entry block of cf.blocks has no parameters");
        }
        self.ctx.push(RegionCtx::Block {
            blocks,
            results: outs.to_vec(),
        });
        for &r in rs {
            let mark = self.scope.len();
            for v in body.params(r) {
                self.define(loc, v, false)?;
            }
            self.ops(r, loc)?;
            self.restore(mark);
        }
        self.ctx.pop();
        Ok(())
    }

    fn func_rets(&self) -> &[Ty] {
        match self.ctx.first() {
            Some(RegionCtx::Func(rets)) => rets,
            _ => &[],
        }
    }

    /// Check an op, then define its results. Lean's `verifyOp`.
    fn op(&mut self, op: OpId) -> VResult<()> {
        let body = self.body;
        let loc = body.loc(op);
        let mut ins = Tys::default();
        for a in body.operands(op) {
            ins.push(self.operand_ty(loc, *a)?);
        }
        let mut outs = Tys::default();
        for v in body.results(op) {
            outs.push(body.ty(v));
        }
        let kind = body.kind(op);
        match (kind, body.regions(op)) {
            (OpKind::Yield, []) => match self.ctx.last() {
                Some(RegionCtx::IfBranch(rs) | RegionCtx::Block { results: rs, .. }) => {
                    expect_tys(loc, "cf.yield", &ins, rs)?;
                }
                _ => return verr(loc, "cf.yield must end a cf.if region or a block"),
            },
            (OpKind::Break, []) => {
                let Some((_, rs)) = self.nearest_loop() else {
                    return verr(loc, "cf.break outside a loop");
                };
                expect_tys(loc, "cf.break", &ins, rs)?;
            }
            (OpKind::Continue, []) => {
                let Some((ps, _)) = self.nearest_loop() else {
                    return verr(loc, "cf.continue outside a loop");
                };
                expect_tys(loc, "cf.continue", &ins, ps)?;
            }
            (OpKind::Ret, []) => expect_tys(loc, "func.ret", &ins, self.func_rets())?,
            (OpKind::Br { dest }, []) => {
                if self.nearest_blocks().is_none() {
                    return verr(loc, "cf.br outside cf.blocks");
                }
                let dest = body.succ(dest);
                if ins.len() != dest.nargs as usize {
                    return verr(loc, "malformed op");
                }
                self.check_succ(loc, dest, &ins)?;
            }
            (OpKind::CondBr { t, f }, []) => {
                if self.nearest_blocks().is_none() {
                    return verr(loc, "cf.cond_br outside cf.blocks");
                }
                let (t, f) = (body.succ(t), body.succ(f));
                if ins.len() != 1 + t.nargs as usize + f.nargs as usize {
                    return verr(loc, "malformed op");
                }
                expect_tys(loc, "cf.cond_br condition", &ins[..1], &[Ty::Int(1)])?;
                self.check_succs(loc, [t, f].into_iter(), &ins[1..])?;
            }
            (OpKind::Switch { dflt, cases }, []) => {
                if self.nearest_blocks().is_none() {
                    return verr(loc, "cf.switch outside cf.blocks");
                }
                let (dflt, cases) = (body.succ(dflt), body.cases(cases));
                let targets = || std::iter::once(dflt).chain(cases.iter().map(|c| c.succ));
                if ins.len() != 1 + targets().map(|s| s.nargs as usize).sum::<usize>() {
                    return verr(loc, "malformed op");
                }
                let t = ins[0];
                if !is_int(t) {
                    return verr(
                        loc,
                        format!("cf.switch value: expected an integer but got {t}"),
                    );
                }
                let w = width(t);
                let modulus = BigInt::from(1) << w;
                let mut seen = FxHashSet::default();
                for c in cases {
                    let k = body.int(c.key);
                    if !(fits_signed(w, k) || fits_unsigned(w, k)) {
                        return verr(loc, format!("{k} does not fit in {t}"));
                    }
                    let r = k.to_bigint() % &modulus;
                    let r = if r.sign() == Sign::Minus {
                        r + &modulus
                    } else {
                        r
                    };
                    if !seen.insert(r) {
                        return verr(loc, format!("cf.switch has more than one case {k}"));
                    }
                }
                self.check_succs(loc, targets(), &ins[1..])?;
            }
            (OpKind::Blocks { .. }, rs) => self.blocks(loc, &ins, &outs, rs)?,
            (OpKind::If, &[thn, els]) => {
                expect_tys(loc, "cf.if condition", &ins, &[Ty::Int(1)])?;
                for r in [thn, els] {
                    if body.params(r).len() != 0 {
                        return verr(loc, "cf.if regions have no parameters");
                    }
                    if body.label(r).is_some() {
                        return verr(loc, "only blocks of cf.blocks have labels");
                    }
                    self.ctx.push(RegionCtx::IfBranch(outs.to_vec()));
                    self.ops(r, loc)?;
                    self.ctx.pop();
                }
            }
            (OpKind::Loop { .. }, &[inner]) => {
                if body.label(inner).is_some() {
                    return verr(loc, "only blocks of cf.blocks have labels");
                }
                let ps: Vec<Ty> = body.params(inner).map(|v| body.ty(v)).collect();
                expect_tys(loc, "cf.loop initial values", &ins, &ps)?;
                let mark = self.scope.len();
                for v in body.params(inner) {
                    self.define(loc, v, false)?;
                }
                self.ctx.push(RegionCtx::LoopBody {
                    params: ps,
                    results: outs.to_vec(),
                });
                self.ops(inner, loc)?;
                self.ctx.pop();
                self.restore(mark);
            }
            (k, []) => {
                if k.is_terminator() || matches!(k, OpKind::If | OpKind::Loop { .. }) {
                    return verr(loc, "malformed op");
                }
                check_simple(body, loc, self.space, self.sigs, k, &ins, &outs)?;
            }
            _ => return verr(loc, "malformed op"),
        }
        for v in body.results(op) {
            self.define(loc, v, false)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn fits_matches_unbounded_integers() {
        let pow = |w: u32| BigInt::from(1) << w;
        for w in 0..70u32 {
            let half = pow(w.saturating_sub(1));
            for n in [-&half - 1, -&half, BigInt::ZERO, &half - 1, half.clone()] {
                let want = -&half <= n && n < half;
                assert_eq!(fits_signed(w, Int::Big(&n)), want, "i{w} {n}");
                if let Ok(small) = i64::try_from(&n) {
                    assert_eq!(fits_signed(w, Int::Small(small)), want, "i{w} {n} small");
                }
            }
            for n in [BigInt::from(-1), BigInt::ZERO, pow(w) - 1, pow(w)] {
                let want = n >= BigInt::ZERO && n < pow(w);
                assert_eq!(fits_unsigned(w, Int::Big(&n)), want, "u{w} {n}");
                if let Ok(small) = i64::try_from(&n) {
                    assert_eq!(fits_unsigned(w, Int::Small(small)), want, "u{w} {n} small");
                }
            }
        }
    }
}
