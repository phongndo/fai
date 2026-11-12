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
use crate::decl::{Check, Imm, Layer, TyE};
use crate::ir::*;
use crate::ops::TARGETS;
use crate::types::Shape;

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
    let sp = &m.space;
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
    if !is_pow2(sp.ptr_align.into()) {
        return Err(format!(
            "memspace: pointer alignment {} must be a power of two",
            sp.ptr_align
        ));
    }
    let mut last = 0;
    for &(w, a) in &sp.ints {
        if w <= last {
            return Err("memspace: integer alignments must be listed by increasing width".into());
        }
        if !is_pow2(a.into()) {
            return Err(format!(
                "memspace: alignment {a} of i{w} must be a power of two"
            ));
        }
        last = w;
    }
    // Names: globals and functions share them.
    let gs = &m.globals;
    let mut globals = FxHashSet::default();
    for i in 0..gs.len() {
        if !globals.insert(gs.name(i)) {
            return Err(format!("global @{} is defined more than once", gs.name(i)));
        }
    }
    let mut sigs = FxHashMap::default();
    for x in &m.externs {
        if sigs.contains_key(x.name.as_str())
            || (!globals.is_empty() && globals.contains(x.name.as_str()))
        {
            return Err(format!("function @{} is defined more than once", x.name));
        }
        sigs.insert(
            x.name.as_str(),
            (x.params.clone(), x.rets.clone(), &gs.types),
        );
    }
    for f in &m.funcs {
        if sigs.contains_key(f.name.as_str())
            || (!globals.is_empty() && globals.contains(f.name.as_str()))
        {
            return Err(format!("function @{} is defined more than once", f.name));
        }
        let entry = f.body.entry();
        let params: Vec<Ty> = f.body.params(entry).map(|v| f.body.ty(v)).collect();
        sigs.insert(f.name.as_str(), (params, f.rets.clone(), f.body.types()));
    }
    for i in 0..gs.len() {
        let name = gs.name(i);
        let t = gs.ty(i);
        check_sized(&gs.types, sp, m.layer, None, t)
            .map_err(|e| format!("global @{name}: {}", e.strip_prefix("@?: ").unwrap_or(&e)))?;
        if !is_pow2(gs.align(i).into()) {
            return Err(format!("global @{name}: alignment must be a power of two"));
        }
        let named = |s: &str| globals.contains(s) || sigs.contains_key(s);
        check_init(gs, &named, sp, name, t, gs.init(i))?;
    }
    // External functions.
    for x in &m.externs {
        for &t in x.params.iter().chain(&x.rets) {
            if !t.is_value() {
                return Err(format!(
                    "extern @{}: {} is not a value type",
                    x.name,
                    gs.types.show(t)
                ));
            }
        }
        for (i, e) in x.effects.iter().enumerate() {
            if x.effects[..i].contains(e) {
                return Err(format!("extern @{}: {e} is listed twice", x.name));
            }
            if *e == ExtEffect::Unwind {
                return Err(format!(
                    "extern @{}: unwinding out of an external function is not supported yet",
                    x.name
                ));
            }
        }
        if x.trust == Trust::Proved {
            return Err(format!(
                "extern @{}: the effects of an external function can be assumed or checked, not proved",
                x.name
            ));
        }
    }
    // Signatures.
    for f in &m.funcs {
        let entry = f.body.entry();
        for t in f
            .body
            .params(entry)
            .map(|v| f.body.ty(v))
            .chain(f.rets.iter().copied())
        {
            if !value_ty(m.layer, f.body.types(), t) {
                return Err(format!(
                    "in @{}: @?: {} is not a value type",
                    f.name,
                    f.body.types().show(t)
                ));
            }
        }
    }
    let mut holes = Vec::new();
    for f in &m.funcs {
        let mut v = FuncVerifier {
            body: &f.body,
            cx: Cx {
                space: sp,
                layer: m.layer,
                sigs: &sigs,
                globals: &globals,
            },
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

/// Check a global's initializer against its type (Lean's `checkInit`).
fn check_init(
    gs: &Globals,
    named: &dyn Fn(&str) -> bool,
    sp: &SpaceCfg,
    g: &str,
    t: Ty,
    init: Init,
) -> Result<(), String> {
    let types = &gs.types;
    let show = |t: Ty| types.show(t);
    match (init, t) {
        (Init::Zero, _) => {}
        (Init::Int(i), Ty::Int(w) | Ty::Byte(w)) => {
            let n = gs.int(i);
            if !(fits_signed(w, Int::Big(n)) || fits_unsigned(w, Int::Big(n))) {
                return Err(format!("global @{g}: {n} does not fit in {}", show(t)));
            }
        }
        (Init::Int(_), _) => {
            return Err(format!(
                "global @{g}: an integer can't initialize {}",
                show(t)
            ));
        }
        (Init::Null, Ty::Ptr) => {}
        (Init::Null, _) => return Err(format!("global @{g}: null can't initialize {}", show(t))),
        (Init::Sym(r), Ty::Ptr) => {
            let s = gs.text(r);
            if !named(s) {
                return Err(format!("global @{g}: no global or function @{s}"));
            }
        }
        (Init::Sym(r), _) => {
            return Err(format!(
                "global @{g}: @{} can't initialize {}",
                gs.text(r),
                show(t)
            ));
        }
        (Init::Bytes(r), _) => {
            let n = gs.bytes(r).len();
            let size = types.size(sp, t);
            if n as u128 != size {
                return Err(format!(
                    "global @{g}: {n} bytes can't initialize {}, which takes {size}",
                    show(t)
                ));
            }
        }
        (Init::List(r), Ty::Agg(id)) => {
            let items = gs.items(r);
            match types.shape(id) {
                Shape::Struct(_, fs) => {
                    if items.len() != fs.len() {
                        return Err(format!(
                            "global @{g}: {} takes {} initializers but got {}",
                            show(t),
                            fs.len(),
                            items.len()
                        ));
                    }
                    for (&f, &i) in fs.iter().zip(items) {
                        check_init(gs, named, sp, g, f, i)?;
                    }
                }
                Shape::Array(n, e) => {
                    if items.len() as u64 != n {
                        return Err(format!(
                            "global @{g}: {} takes {n} initializers but got {}",
                            show(t),
                            items.len()
                        ));
                    }
                    for &i in items {
                        check_init(gs, named, sp, g, e, i)?;
                    }
                }
                Shape::Func(..) | Shape::Union(_) => {
                    return Err(format!("global @{g}: a list can't initialize {}", show(t)));
                }
            }
        }
        (Init::List(_), _) => {
            return Err(format!("global @{g}: a list can't initialize {}", show(t)));
        }
    }
    Ok(())
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
    /// A block of a target's code op (`aarch64.code`): the op's name and its blocks' labels.
    Code {
        name: &'static str,
        labels: Vec<&'a str>,
    },
    /// A region of `cf.try`, with the op's results. Jumps can't leave it.
    TryRegion(Vec<Ty>),
}

/// Whether values of type `t` can exist in a module of this layer (Lean's `Layer.valueTy`):
/// in HFIR anything but a function type, elsewhere the scalars.
fn value_ty(layer: Layer, types: &Types, t: Ty) -> bool {
    match layer {
        Layer::Hfir => types.is_hvalue(t),
        _ => t.is_value(),
    }
}

/// Check that a type is well formed: valid widths, parts with a layout, unions of value types,
/// function types of the layer's value types, and sizes that fit the address space (Lean's
/// `checkTy`).
fn check_ty(types: &Types, sp: &SpaceCfg, layer: Layer, loc: Option<Loc>, t: Ty) -> VResult<()> {
    match t {
        Ty::Int(0) => verr(loc, "i0 is not a valid type"),
        Ty::Byte(w) if !(w > 0 && w.is_multiple_of(8)) => {
            verr(loc, format!("b{w} is not a valid type"))
        }
        Ty::Int(_) | Ty::Ptr | Ty::Byte(_) | Ty::Slice | Ty::Float(_) => Ok(()),
        Ty::Agg(id) => {
            let part = |x: Ty| -> VResult<()> {
                check_ty(types, sp, layer, loc, x)?;
                if has_layout(types, x) {
                    Ok(())
                } else {
                    verr(
                        loc,
                        format!("{} can't be part of {}", types.show(x), types.show(t)),
                    )
                }
            };
            match types.shape(id) {
                Shape::Struct(_, fs) => {
                    for &f in fs {
                        part(f)?;
                    }
                }
                Shape::Array(_, e) => part(e)?,
                Shape::Func(ps, rs) => {
                    for &x in ps.iter().chain(rs) {
                        check_ty(types, sp, layer, loc, x)?;
                        if !value_ty(layer, types, x) {
                            return verr(
                                loc,
                                format!(
                                    "{} can't be a parameter or result of {}",
                                    types.show(x),
                                    types.show(t)
                                ),
                            );
                        }
                    }
                    return Ok(());
                }
                Shape::Union(vs) => {
                    if vs.is_empty() {
                        return verr(loc, format!("{} needs at least one variant", types.show(t)));
                    }
                    for &v in vs {
                        check_ty(types, sp, layer, loc, v)?;
                        if !types.is_hvalue(v) {
                            return verr(
                                loc,
                                format!(
                                    "{} can't be a variant of {}",
                                    types.show(v),
                                    types.show(t)
                                ),
                            );
                        }
                    }
                    return Ok(());
                }
            }
            let size = types.size(sp, t);
            if sp.addr_bits < 128 && size >= 1u128 << sp.addr_bits {
                return verr(
                    loc,
                    format!("{} is too large for the address space", types.show(t)),
                );
            }
            Ok(())
        }
    }
}

/// Whether values of the type can be part of memory (Lean's `Ty.hasLayout`).
fn has_layout(types: &Types, t: Ty) -> bool {
    match t {
        Ty::Int(w) => w.is_multiple_of(8),
        Ty::Agg(id) => !matches!(types.shape(id), Shape::Func(..) | Shape::Union(_)),
        _ => true,
    }
}

/// Check that a value's type is a well-formed value type of the layer.
#[inline]
fn check_value_ty(
    types: &Types,
    sp: &SpaceCfg,
    layer: Layer,
    loc: Option<Loc>,
    t: Ty,
) -> VResult<()> {
    match t {
        Ty::Int(w) if w > 0 => Ok(()),
        Ty::Ptr => Ok(()),
        Ty::Byte(w) if w > 0 && w.is_multiple_of(8) => Ok(()),
        _ => check_value_ty_slow(types, sp, layer, loc, t),
    }
}

#[cold]
fn check_value_ty_slow(
    types: &Types,
    sp: &SpaceCfg,
    layer: Layer,
    loc: Option<Loc>,
    t: Ty,
) -> VResult<()> {
    check_ty(types, sp, layer, loc, t)?;
    if value_ty(layer, types, t) {
        Ok(())
    } else {
        verr(loc, format!("{} is not a value type", types.show(t)))
    }
}

/// Check that a type is well formed and has a layout.
fn check_sized(types: &Types, sp: &SpaceCfg, layer: Layer, loc: Option<Loc>, t: Ty) -> VResult<()> {
    check_ty(types, sp, layer, loc, t)?;
    if has_layout(types, t) {
        Ok(())
    } else {
        verr(loc, format!("{} has no size in memory", types.show(t)))
    }
}

fn width(t: Ty) -> u32 {
    match t {
        Ty::Int(w) | Ty::Byte(w) => w,
        Ty::Float(f) => f.width(),
        _ => 0,
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

fn expect_tys(types: &Types, loc: Option<Loc>, what: &str, got: &[Ty], want: &[Ty]) -> VResult<()> {
    if got == want {
        Ok(())
    } else {
        verr(
            loc,
            format!(
                "{what}: expected {} but got {}",
                types.show_list(want),
                types.show_list(got)
            ),
        )
    }
}

fn is_loadable_scalar(space: &SpaceCfg, t: Ty) -> bool {
    match t {
        Ty::Int(w) => w.is_multiple_of(8),
        Ty::Ptr => space.ptr_bits.is_multiple_of(8),
        Ty::Byte(_) | Ty::Float(_) => true,
        Ty::Slice | Ty::Agg(_) => false,
    }
}

/// A scalar in whole bytes, or an aggregate with a layout whose leaves are (Lean's
/// `isLoadable`).
fn is_loadable(types: &Types, space: &SpaceCfg, t: Ty) -> bool {
    if t.is_value() {
        return is_loadable_scalar(space, t);
    }
    if !has_layout(types, t) {
        return false;
    }
    let mut leaves = Vec::new();
    types.leaves(space, t, 0, &mut leaves);
    leaves.iter().all(|&(_, l)| is_loadable_scalar(space, l))
}

/// Compare types from two tables, as `expect_tys` does within one.
fn expect_tys_in(
    got_types: &Types,
    want_types: &Types,
    loc: Option<Loc>,
    what: &str,
    got: &[Ty],
    want: &[Ty],
) -> VResult<()> {
    let same = got.len() == want.len()
        && got
            .iter()
            .zip(want)
            .all(|(&g, &w)| got_types.same(g, want_types, w));
    if same {
        Ok(())
    } else {
        verr(
            loc,
            format!(
                "{what}: expected {} but got {}",
                want_types.show_list(want),
                got_types.show_list(got)
            ),
        )
    }
}

fn ints(types: &Types, loc: Option<Loc>, ts: &[Ty]) -> VResult<()> {
    if ts.iter().all(|t| is_int(*t)) {
        Ok(())
    } else {
        verr(
            loc,
            format!("expected integers but got {}", types.show_list(ts)),
        )
    }
}

/// Check the operand and result types of an op without regions by its declared rule (Lean's
/// `checkSimple`).
fn check_simple(
    cx: &Cx<'_>,
    body: &Body,
    loc: Option<Loc>,
    k: OpKind,
    ins: &[Ty],
    outs: &[Ty],
) -> VResult<()> {
    let Cx {
        space,
        layer,
        sigs,
        globals,
    } = *cx;
    let Some(rule) = k.decl().rule else {
        return verr(loc, "unexpected op");
    };
    let types = body.types();
    let show = |t: Ty| types.show(t);
    // The types named so far.
    let mut vars = [Ty::Ptr; 4];
    let mut named = 0;
    let field = |i: u8| k.imm(i.into());
    for check in rule {
        let ty = |e: &TyE| match *e {
            TyE::Ptr => Ty::Ptr,
            TyE::Addr => Ty::Int(space.addr_bits),
            TyE::Slice => Ty::Slice,
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
                    expect_tys(types, loc, label, ins, &tys_of(want))?;
                }
            }
            Check::Outs(want) => {
                if !same(outs, want) {
                    expect_tys(types, loc, "results", outs, &tys_of(want))?;
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
                    expect_tys(types, loc, label, &got, &tys_of(want))?;
                }
            }
            Check::Ints(ts) => {
                if !ts.iter().all(|e| is_int(ty(e))) {
                    ints(types, loc, &tys_of(ts))?;
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
                    return verr(loc, format!("{n} does not fit in {}", show(t)));
                }
            }
            Check::Widens(a, t) => {
                let (a, t) = (ty(&a), ty(&t));
                if width(t) <= width(a) {
                    return verr(loc, format!("cannot extend {} to {}", show(a), show(t)));
                }
            }
            Check::Narrows(a, t) => {
                let (a, t) = (ty(&a), ty(&t));
                if width(t) >= width(a) {
                    return verr(loc, format!("cannot truncate {} to {}", show(a), show(t)));
                }
            }
            Check::Loadable(t, verb) => {
                let t = ty(&t);
                if !value_ty(layer, types, t) {
                    return verr(
                        loc,
                        format!("{} can't be {verb}: it is not a value type", show(t)),
                    );
                }
                if !(t.is_value() || has_layout(types, t)) {
                    return verr(
                        loc,
                        format!("{} can't be {verb}: it has no layout", show(t)),
                    );
                }
                if !is_loadable(types, space, t) {
                    return verr(
                        loc,
                        format!("{} can't be {verb}: its size isn't whole bytes", show(t)),
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
                let Some((params, rets, ctypes)) = sigs.get(callee) else {
                    return verr(loc, format!("no function @{callee}"));
                };
                let what = format!("arguments of @{callee}");
                expect_tys_in(types, ctypes, loc, &what, ins, params)?;
                let what = format!("results of @{callee}");
                expect_tys_in(types, ctypes, loc, &what, outs, rets)?;
            }
            Check::Sized(t) => check_sized(types, space, layer, loc, ty(&t))?,
            Check::Field(t, i) => {
                let t = ty(&t);
                check_sized(types, space, layer, loc, t)?;
                let Some(Imm::Index(i)) = field(i) else {
                    return verr(loc, "malformed op");
                };
                match types.shape_of(t) {
                    Some(Shape::Struct(_, fs)) => {
                        if i as usize >= fs.len() {
                            return verr(loc, format!("{} has no field {i}", show(t)));
                        }
                    }
                    _ => return verr(loc, format!("{} is not a struct", show(t))),
                }
            }
            Check::Sig(i) => {
                let Some(Imm::Ty(t)) = field(i) else {
                    return verr(loc, "malformed op");
                };
                check_ty(types, space, layer, loc, t)?;
                let Some(Shape::Func(ps, rs)) = types.shape_of(t) else {
                    return verr(loc, format!("{} is not a function type", show(t)));
                };
                let ok = ins.len() == ps.len() + 1 && ins[0] == Ty::Ptr && ins[1..] == *ps;
                if !ok {
                    let mut want = vec![Ty::Ptr];
                    want.extend_from_slice(ps);
                    expect_tys(types, loc, "operands", ins, &want)?;
                }
                expect_tys(types, loc, "results", outs, rs)?;
            }
            Check::Global(i) => {
                let Some(Imm::Str(g)) = field(i) else {
                    return verr(loc, "malformed op");
                };
                let g = body.str(g);
                if !globals.contains(g) {
                    return verr(loc, format!("no global @{g}"));
                }
            }
            Check::Func(i) => {
                let Some(Imm::Str(f)) = field(i) else {
                    return verr(loc, "malformed op");
                };
                let f = body.str(f);
                if !sigs.contains_key(f) {
                    return verr(loc, format!("no function @{f}"));
                }
            }
            Check::Parts(t) => match ty(&t) {
                t @ Ty::Agg(id) => match types.shape(id) {
                    Shape::Struct(_, fs) => expect_tys(types, loc, "operands", ins, fs)?,
                    Shape::Array(n, e) => {
                        if !(ins.len() as u64 == n && ins.iter().all(|&x| x == e)) {
                            return verr(
                                loc,
                                format!(
                                    "operands: expected {n} values of type {} for {} but got {}",
                                    show(e),
                                    show(t),
                                    types.show_list(ins)
                                ),
                            );
                        }
                    }
                    _ => return verr(loc, format!("{} is not a struct or an array", show(t))),
                },
                t => return verr(loc, format!("{} is not a struct or an array", show(t))),
            },
            Check::Part(a, i, t) => {
                let (a, t) = (ty(&a), ty(&t));
                let Some(Imm::Index(i)) = field(i) else {
                    return verr(loc, "malformed op");
                };
                let part = match types.shape_of(a) {
                    Some(Shape::Struct(_, fs)) => Some(fs.get(i as usize).copied()),
                    Some(Shape::Array(n, e)) => Some((u64::from(i) < n).then_some(e)),
                    _ => None,
                };
                match part {
                    Some(Some(p)) => {
                        expect_tys(types, loc, &format!("part {i} of {}", show(a)), &[t], &[p])?
                    }
                    Some(None) => return verr(loc, format!("{} has no part {i}", show(a))),
                    None => {
                        return verr(loc, format!("{} is not a struct or an array", show(a)));
                    }
                }
            }
            Check::Variant(u, i, t) => {
                let (u, t) = (ty(&u), ty(&t));
                let Some(Imm::Index(i)) = field(i) else {
                    return verr(loc, "malformed op");
                };
                match types.shape_of(u) {
                    Some(Shape::Union(vs)) => match vs.get(i as usize) {
                        Some(&v) => expect_tys(
                            types,
                            loc,
                            &format!("variant {i} of {}", show(u)),
                            &[t],
                            &[v],
                        )?,
                        None => return verr(loc, format!("{} has no variant {i}", show(u))),
                    },
                    _ => return verr(loc, format!("{} is not a union", show(u))),
                }
            }
            Check::Union(u) => {
                let u = ty(&u);
                if !matches!(types.shape_of(u), Some(Shape::Union(_))) {
                    return verr(loc, format!("{} is not a union", show(u)));
                }
            }
            Check::Scalar(t) => {
                let t = ty(&t);
                if !t.is_value() {
                    return verr(loc, format!("{} is not a scalar type", show(t)));
                }
            }
            Check::Floats(ts) => {
                if !ts.iter().all(|e| ty(e).is_float()) {
                    return verr(
                        loc,
                        format!("expected floats but got {}", types.show_list(&tys_of(ts))),
                    );
                }
            }
            Check::Numeric(ts) => {
                if !ts
                    .iter()
                    .all(|e| matches!(ty(e), Ty::Int(_) | Ty::Float(_)))
                {
                    return verr(
                        loc,
                        format!(
                            "expected integers or floats but got {}",
                            types.show_list(&tys_of(ts))
                        ),
                    );
                }
            }
            Check::SameWidth(a, t) => {
                let (a, t) = (ty(&a), ty(&t));
                if width(a) != width(t) {
                    return verr(
                        loc,
                        format!("{} and {} have different widths", show(a), show(t)),
                    );
                }
            }
            Check::FloatBits(i, t) => {
                let Some(Imm::Nat(n)) = field(i) else {
                    return verr(loc, "malformed op");
                };
                let t = ty(&t);
                if width(t) < 64 && n >> width(t) != 0 {
                    return verr(loc, format!("{n} is not the bits of a {}", show(t)));
                }
            }
        }
    }
    Ok(())
}

/// Verifies one function. Lean threads a name-to-type scope through the ops; here the visible
/// values are a stack (`scope`) that is cut back when a region ends, mirrored in a set
/// (`visible`) for lookups.
/// What the whole module tells the checks of one function.
#[derive(Clone, Copy)]
struct Cx<'a> {
    space: &'a SpaceCfg,
    layer: Layer,
    /// Each function's parameter and result types.
    sigs: &'a FxHashMap<&'a str, (Vec<Ty>, Vec<Ty>, &'a Types)>,
    globals: &'a FxHashSet<&'a str>,
}

struct FuncVerifier<'a> {
    body: &'a Body,
    cx: Cx<'a>,
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
            check_value_ty(self.body.types(), self.cx.space, self.cx.layer, None, t)?;
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
        check_value_ty(body.types(), self.cx.space, self.cx.layer, loc, ty)?;
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
                check_value_ty(self.body.types(), self.cx.space, self.cx.layer, loc, ty)?;
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
            Some(RegionCtx::TryRegion(rs)) if rs.is_empty() => {}
            Some(RegionCtx::TryRegion(_)) => {
                return verr(region_loc, "this cf.try region must end with cf.yield");
            }
            Some(RegionCtx::LoopBody { .. }) => {
                return verr(
                    region_loc,
                    "a loop body must end with cf.break or cf.continue",
                );
            }
            Some(RegionCtx::Block { .. } | RegionCtx::Code { .. }) => {
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

    /// The blocks of the nearest enclosing `cf.blocks`, unless a `cf.try` region is nearer.
    fn nearest_blocks(&self) -> Option<&[(&'a str, Vec<Ty>)]> {
        for c in self.ctx.iter().rev() {
            match c {
                RegionCtx::Block { blocks, .. } => return Some(&blocks[..]),
                RegionCtx::TryRegion(_) => return None,
                _ => {}
            }
        }
        None
    }

    /// Why a jump has no blocks to go to (Lean's `noBlocks`).
    fn no_blocks(&self, what: &str) -> String {
        for c in self.ctx.iter().rev() {
            if matches!(c, RegionCtx::TryRegion(_)) {
                return format!("{what} can't leave a cf.try region");
            }
        }
        format!("{what} outside cf.blocks")
    }

    /// The nearest enclosing target code op's name and labels (Lean's `nearestCode`).
    fn nearest_code(&self) -> Option<(&'static str, &[&'a str])> {
        self.ctx.iter().rev().find_map(|c| match c {
            RegionCtx::Code { name, labels } => Some((*name, &labels[..])),
            _ => None,
        })
    }

    /// A target's code op: labeled blocks without parameters, as a function's whole body.
    fn code(&mut self, loc: Option<Loc>, kind: OpKind, rs: &[RegionId]) -> VResult<()> {
        let body = self.body;
        let name = kind.mnemonic();
        if !matches!(&self.ctx[..], [RegionCtx::Func(_)]) {
            return verr(loc, format!("{name} must be a function's whole body"));
        }
        let mut labels: Vec<&'a str> = Vec::with_capacity(rs.len());
        for &r in rs {
            let Some(l) = body.label(r) else {
                return verr(loc, format!("every block of {name} needs a label"));
            };
            let l = body.str(l);
            if labels.contains(&l) {
                return verr(loc, format!("block ^{l} is defined more than once"));
            }
            if body.params(r).len() != 0 {
                return verr(loc, format!("blocks of {name} have no parameters"));
            }
            labels.push(l);
        }
        self.ctx.push(RegionCtx::Code { name, labels });
        for &r in rs {
            self.ops(r, loc)?;
        }
        self.ctx.pop();
        Ok(())
    }

    /// Check a jump to `s` with arguments of types `args` (Lean's `checkSucc`).
    fn check_succ(&self, loc: Option<Loc>, s: Succ, args: &[Ty]) -> VResult<()> {
        let label = self.body.str(s.label);
        let blocks = self.nearest_blocks().unwrap_or_default();
        let Some((_, ps)) = blocks.iter().find(|(l, _)| *l == label) else {
            return verr(loc, format!("no block ^{label} in the enclosing cf.blocks"));
        };
        expect_tys(
            self.body.types(),
            loc,
            &format!("arguments of ^{label}"),
            args,
            ps,
        )
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
        let kind = body.kind(op);
        let layer = self.cx.layer;
        if !layer.allows(kind.decl()) {
            return verr(
                loc,
                format!(
                    "{} is not allowed in layer {layer}; it is allowed in {}",
                    kind.mnemonic(),
                    kind.decl().layers_text()
                ),
            );
        }
        let mut ins = Tys::default();
        for a in body.operands(op) {
            ins.push(self.operand_ty(loc, *a)?);
        }
        let mut outs = Tys::default();
        for v in body.results(op) {
            outs.push(body.ty(v));
        }
        match (kind, body.regions(op)) {
            (OpKind::Yield, []) => match self.ctx.last() {
                Some(
                    RegionCtx::IfBranch(rs)
                    | RegionCtx::Block { results: rs, .. }
                    | RegionCtx::TryRegion(rs),
                ) => {
                    expect_tys(body.types(), loc, "cf.yield", &ins, rs)?;
                }
                _ => return verr(loc, "cf.yield must end a cf.if or cf.try region or a block"),
            },
            (OpKind::Break, []) => {
                let Some((_, rs)) = self.nearest_loop() else {
                    return verr(loc, "cf.break outside a loop");
                };
                expect_tys(body.types(), loc, "cf.break", &ins, rs)?;
            }
            (OpKind::Continue, []) => {
                let Some((ps, _)) = self.nearest_loop() else {
                    return verr(loc, "cf.continue outside a loop");
                };
                expect_tys(body.types(), loc, "cf.continue", &ins, ps)?;
            }
            (OpKind::Ret, []) => {
                if let Some((name, _)) = self.nearest_code() {
                    return verr(loc, format!("func.ret can't be inside {name}"));
                }
                expect_tys(body.types(), loc, "func.ret", &ins, self.func_rets())?
            }
            (OpKind::Br { dest }, []) => {
                if self.nearest_blocks().is_none() {
                    return verr(loc, self.no_blocks("cf.br"));
                }
                let dest = body.succ(dest);
                if ins.len() != dest.nargs as usize {
                    return verr(loc, "malformed op");
                }
                self.check_succ(loc, dest, &ins)?;
            }
            (OpKind::CondBr { t, f }, []) => {
                if self.nearest_blocks().is_none() {
                    return verr(loc, self.no_blocks("cf.cond_br"));
                }
                let (t, f) = (body.succ(t), body.succ(f));
                if ins.len() != 1 + t.nargs as usize + f.nargs as usize {
                    return verr(loc, "malformed op");
                }
                expect_tys(
                    body.types(),
                    loc,
                    "cf.cond_br condition",
                    &ins[..1],
                    &[Ty::Int(1)],
                )?;
                self.check_succs(loc, [t, f].into_iter(), &ins[1..])?;
            }
            (OpKind::Switch { dflt, cases }, []) => {
                if self.nearest_blocks().is_none() {
                    return verr(loc, self.no_blocks("cf.switch"));
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
                expect_tys(body.types(), loc, "cf.if condition", &ins, &[Ty::Int(1)])?;
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
            (OpKind::Try, &[inner, handler]) => {
                if !ins.is_empty() {
                    return verr(loc, "malformed op");
                }
                if body.params(inner).len() != 0 {
                    return verr(loc, "the first region of cf.try has no parameters");
                }
                if body.label(inner).is_some() || body.label(handler).is_some() {
                    return verr(loc, "only blocks of cf.blocks have labels");
                }
                self.ctx.push(RegionCtx::TryRegion(outs.to_vec()));
                self.ops(inner, loc)?;
                self.ctx.pop();
                let ps = body.params(handler);
                if ps.len() != 1 || ps.clone().any(|v| body.ty(v) != Ty::Ptr) {
                    return verr(
                        loc,
                        "the catch region of cf.try takes one parameter, the exception, a ptr",
                    );
                }
                let mark = self.scope.len();
                for v in body.params(handler) {
                    self.define(loc, v, false)?;
                }
                self.ctx.push(RegionCtx::TryRegion(outs.to_vec()));
                self.ops(handler, loc)?;
                self.ctx.pop();
                self.restore(mark);
            }
            (OpKind::Throw, []) => {
                expect_tys(body.types(), loc, "exn.throw", &ins, &[Ty::Ptr])?;
                if !outs.is_empty() {
                    return verr(loc, "exn.throw has no results");
                }
            }
            (k @ (OpKind::Invoke { unwind, .. } | OpKind::InvokeIndirect { unwind, .. }), []) => {
                let s = body.succ(unwind);
                if s.nargs != 0 {
                    return verr(
                        loc,
                        "a handler takes the exception only; unwind passes no arguments",
                    );
                }
                check_simple(&self.cx, body, loc, k, &ins, &outs)?;
                let Some(blocks) = self.nearest_blocks() else {
                    return verr(
                        loc,
                        format!("{} names a handler outside cf.blocks", k.mnemonic()),
                    );
                };
                let label = body.str(s.label);
                let Some((_, ps)) = blocks.iter().find(|(l, _)| *l == label) else {
                    return verr(loc, format!("no block ^{label} in the enclosing cf.blocks"));
                };
                expect_tys(
                    body.types(),
                    loc,
                    &format!("parameters of handler ^{label}"),
                    ps,
                    &[Ty::Ptr],
                )?;
            }
            (OpKind::Loop { .. }, &[inner]) => {
                if body.label(inner).is_some() {
                    return verr(loc, "only blocks of cf.blocks have labels");
                }
                let ps: Vec<Ty> = body.params(inner).map(|v| body.ty(v)).collect();
                expect_tys(body.types(), loc, "cf.loop initial values", &ins, &ps)?;
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
            (k, []) if k.is_terminator() && k.decl().rule.is_some() => {
                // A target's branch, return, or trap: it ends a block of the target's code.
                let Some((name, labels)) = self.nearest_code() else {
                    return verr(
                        loc,
                        format!("{} must be inside a block of a target's code", k.mnemonic()),
                    );
                };
                check_simple(&self.cx, body, loc, k, &ins, &outs)?;
                for i in 0..k.decl().imms.len() {
                    if let Some(Imm::Succ(s)) = k.imm(i) {
                        let label = body.str(body.succ(s).label);
                        if !labels.contains(&label) {
                            return verr(loc, format!("no block ^{label} in the enclosing {name}"));
                        }
                    }
                }
            }
            (k, []) => {
                if k.is_terminator() || matches!(k, OpKind::If | OpKind::Loop { .. } | OpKind::Try)
                {
                    return verr(loc, "malformed op");
                }
                if TARGETS.contains(&k.decl().dialect)
                    && !matches!(self.ctx.last(), Some(RegionCtx::Code { .. }))
                {
                    return verr(
                        loc,
                        format!("{} must be inside a block of a target's code", k.mnemonic()),
                    );
                }
                check_simple(&self.cx, body, loc, k, &ins, &outs)?;
            }
            (k, rs) => {
                if !(k.decl().has_blocks() && ins.is_empty() && outs.is_empty()) {
                    return verr(loc, "malformed op");
                }
                self.code(loc, k, rs)?;
            }
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
