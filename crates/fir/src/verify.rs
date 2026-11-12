//! The verifier, mirroring `spec/Fir/Verify.lean`: the same rules, checked in the same order,
//! with the same messages, so the first error matches the Lean reference tool's (`fir-ref
//! check`) byte for byte.
//!
//! The parser already resolves names, so for parsed modules it reports undefined and repeated
//! values itself (with a `line:col:` position). The checks here still cover modules built
//! directly.

use rustc_hash::{FxHashMap, FxHashSet};

use num_bigint::Sign;

use crate::body::{Body, Int, OpId, Operand, OperandKind, RegionId, ValueId};
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
enum RegionCtx {
    Func(Vec<Ty>),
    IfBranch(Vec<Ty>),
    LoopBody { params: Vec<Ty>, results: Vec<Ty> },
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

/// `msg` unless `xs` has exactly one item.
fn single<T: Copy>(loc: Option<Loc>, xs: &[T], msg: &str) -> VResult<T> {
    match xs {
        [x] => Ok(*x),
        _ => verr(loc, msg),
    }
}

/// Check the operand and result types of an op without regions (Lean's `checkSimple`).
fn check_simple(
    body: &Body,
    loc: Option<Loc>,
    space: SpaceCfg,
    sigs: &FxHashMap<&str, (Vec<Ty>, Vec<Ty>)>,
    k: OpKind,
    ins: &[Ty],
    outs: &[Ty],
) -> VResult<()> {
    let addr = Ty::Int(space.addr_bits);
    let one = |t: Ty| expect_tys(loc, "results", outs, &[t]);
    let align_pow2 = |align: u64| {
        if is_pow2(align) {
            Ok(())
        } else {
            verr(loc, "alignment must be a power of two")
        }
    };
    let no_results = || {
        if outs.is_empty() {
            Ok(())
        } else {
            verr(loc, "this op has no results")
        }
    };
    match k {
        OpKind::Const(n) => {
            expect_tys(loc, "operands", ins, &[])?;
            let t = single(loc, outs, "int.const has one result")?;
            ints(loc, &[t])?;
            let n = body.int(n);
            if !(fits_signed(width(t), n) || fits_unsigned(width(t), n)) {
                return verr(loc, format!("{n} does not fit in {t}"));
            }
            Ok(())
        }
        OpKind::Poison => {
            expect_tys(loc, "operands", ins, &[])?;
            let t = single(loc, outs, "poison has one result")?;
            ints(loc, &[t])
        }
        OpKind::Freeze => {
            let t = single(loc, ins, "freeze takes one operand")?;
            ints(loc, &[t])?;
            one(t)
        }
        OpKind::Copy => {
            let t = single(loc, ins, "copy takes one operand")?;
            one(t)
        }
        OpKind::Select => {
            let &[c, a, b] = ins else {
                return verr(loc, "select takes three operands");
            };
            expect_tys(loc, "select", &[c, b], &[Ty::Int(1), a])?;
            ints(loc, &[a])?;
            one(a)
        }
        OpKind::Arith(..) | OpKind::Bit(_) | OpKind::Div(..) | OpKind::Shift(..) => {
            let &[a, b] = ins else {
                return verr(loc, "this op takes two operands");
            };
            expect_tys(loc, "operands", &[b], &[a])?;
            ints(loc, &[a])?;
            one(a)
        }
        OpKind::Cmp(_) => {
            let &[a, b] = ins else {
                return verr(loc, "int.cmp takes two operands");
            };
            expect_tys(loc, "operands", &[b], &[a])?;
            ints(loc, &[a])?;
            one(Ty::Int(1))
        }
        OpKind::Zext | OpKind::Sext => {
            let a = single(loc, ins, "this op takes one operand")?;
            let t = single(loc, outs, "this op has one result")?;
            ints(loc, &[a, t])?;
            if width(t) <= width(a) {
                return verr(loc, format!("cannot extend {a} to {t}"));
            }
            Ok(())
        }
        OpKind::Trunc(_) => {
            let a = single(loc, ins, "int.trunc takes one operand")?;
            let t = single(loc, outs, "int.trunc has one result")?;
            ints(loc, &[a, t])?;
            if width(t) >= width(a) {
                return verr(loc, format!("cannot truncate {a} to {t}"));
            }
            Ok(())
        }
        OpKind::MemStack { align, .. } => {
            align_pow2(align.into())?;
            expect_tys(loc, "operands", ins, &[])?;
            one(Ty::Ptr)
        }
        OpKind::MemAlloc { align, .. } => {
            align_pow2(align.into())?;
            expect_tys(loc, "mem.alloc size", ins, &[addr])?;
            one(Ty::Ptr)
        }
        OpKind::MemFree { .. } => {
            expect_tys(loc, "operands", ins, &[Ty::Ptr])?;
            no_results()
        }
        OpKind::Load { align } => {
            align_pow2(align.into())?;
            expect_tys(loc, "operands", ins, &[Ty::Ptr])?;
            let t = single(loc, outs, "mem.load has one result")?;
            if !is_loadable(space, t) {
                return verr(
                    loc,
                    format!("{t} can't be loaded: its size isn't whole bytes"),
                );
            }
            Ok(())
        }
        OpKind::Store { ty, align } => {
            align_pow2(align.into())?;
            expect_tys(loc, "operands", ins, &[ty, Ty::Ptr])?;
            if !is_loadable(space, ty) {
                return verr(
                    loc,
                    format!("{ty} can't be stored: its size isn't whole bytes"),
                );
            }
            no_results()
        }
        OpKind::PtrOffset { .. } | OpKind::PtrWithAddr => {
            expect_tys(loc, "operands", ins, &[Ty::Ptr, addr])?;
            one(Ty::Ptr)
        }
        OpKind::PtrAddr | OpKind::PtrExpose => {
            expect_tys(loc, "operands", ins, &[Ty::Ptr])?;
            one(addr)
        }
        OpKind::PtrFromExposed => {
            expect_tys(loc, "operands", ins, &[addr])?;
            one(Ty::Ptr)
        }
        OpKind::PtrNull => {
            expect_tys(loc, "operands", ins, &[])?;
            one(Ty::Ptr)
        }
        OpKind::PtrCmp(p) => {
            if matches!(p, Pred::Slt | Pred::Sle | Pred::Sgt | Pred::Sge) {
                return verr(loc, "pointer comparisons are unsigned");
            }
            expect_tys(loc, "operands", ins, &[Ty::Ptr, Ty::Ptr])?;
            one(Ty::Int(1))
        }
        OpKind::Call { callee } => {
            let callee = body.str(callee);
            let Some((params, rets)) = sigs.get(callee) else {
                return verr(loc, format!("no function @{callee}"));
            };
            expect_tys(loc, &format!("arguments of @{callee}"), ins, params)?;
            expect_tys(loc, &format!("results of @{callee}"), outs, rets)
        }
        OpKind::If
        | OpKind::Loop { .. }
        | OpKind::Yield
        | OpKind::Break
        | OpKind::Continue
        | OpKind::Ret => verr(loc, "unexpected op"),
    }
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
    ctx: Vec<RegionCtx>,
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
            (OpKind::Yield, []) => {
                let Some(RegionCtx::IfBranch(rs)) = self.ctx.last() else {
                    return verr(loc, "cf.yield must end a cf.if region");
                };
                expect_tys(loc, "cf.yield", &ins, rs)?;
            }
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
            (OpKind::If, &[thn, els]) => {
                expect_tys(loc, "cf.if condition", &ins, &[Ty::Int(1)])?;
                for r in [thn, els] {
                    if body.params(r).len() != 0 {
                        return verr(loc, "cf.if regions have no parameters");
                    }
                    self.ctx.push(RegionCtx::IfBranch(outs.to_vec()));
                    self.ops(r, loc)?;
                    self.ctx.pop();
                }
            }
            (OpKind::Loop { .. }, &[inner]) => {
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
