//! Struct, array, and function types, and their layout, mirroring the `Ty` constructors of
//! `spec/Fir/Syntax.lean` and `spec/Fir/Layout.lean`.
//!
//! [`Ty`] stays a small `Copy` value: value types (`iN`, `ptr`, `bN`) are inline, and every other
//! type is [`Ty::Agg`], an id into a [`Types`] table. Each function's [`Body`](crate::Body) owns
//! the table for the types its values and ops name; the module's globals own another. Tables
//! intern their entries, so two equal types in one table have the same id and `==` compares
//! them structurally. Types from different tables are never compared: values only ever have value
//! types, and the verifier checks every signature before any body (see `verify.rs`).

use std::fmt::Write;
use std::hash::{Hash, Hasher};

use rustc_hash::{FxHashMap, FxHasher};

use crate::ir::{SpaceCfg, Ty};

/// An entry in a [`Types`] table.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct TyId(u32);

impl TyId {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// The id as a 32-bit number, as the C API passes it.
    pub fn raw(self) -> u32 {
        self.0
    }

    /// The id a [`raw`](Self::raw) number stands for. Nothing checks that it exists.
    pub fn from_raw(n: u32) -> TyId {
        TyId(n)
    }
}

/// How a struct's fields are laid out (Lean's `Policy`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Policy {
    /// `struct<C>`: the platform C layout.
    C,
    /// `struct<packed>`: no padding, alignment 1.
    Packed,
    /// `struct<auto>`: by decreasing alignment.
    Auto,
}

impl Policy {
    pub fn name(self) -> &'static str {
        match self {
            Policy::C => "C",
            Policy::Packed => "packed",
            Policy::Auto => "auto",
        }
    }
}

/// What a [`Ty::Agg`] is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Shape<'a> {
    /// `struct<C>{i32, ptr}`
    Struct(Policy, &'a [Ty]),
    /// `array<4 x i32>`
    Array(u64, Ty),
    /// `func<(i32, ptr) -> i32>`: parameters, results, and whether it is variadic
    /// (`func<(ptr, ...) -> i32>`).
    Func(&'a [Ty], &'a [Ty], bool),
    /// `union<i32, ptr>`: the variants.
    Union(&'a [Ty]),
}

/// A run of entries in `parts`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Run {
    start: u32,
    len: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Entry {
    Struct {
        policy: Policy,
        fields: Run,
    },
    Array {
        n: u64,
        elem: Ty,
    },
    Func {
        params: Run,
        rets: Run,
        variadic: bool,
    },
    Union {
        variants: Run,
    },
}

/// A table of struct, array, and function types.
#[derive(Clone, Debug, Default)]
pub struct Types {
    entries: Vec<Entry>,
    /// Struct fields and function parameters and results, as runs.
    parts: Vec<Ty>,
    /// The first entry with each content hash; `same_hash` links the others.
    index: FxHashMap<u64, u32>,
    same_hash: Vec<u32>,
}

const NONE: u32 = u32::MAX;

impl Types {
    pub fn new() -> Types {
        Types::default()
    }

    pub fn clear(&mut self) {
        self.entries.clear();
        self.parts.clear();
        self.index.clear();
        self.same_hash.clear();
    }

    /// Whether the two tables hold the same types under the same ids, so a [`Ty`] means the
    /// same in both. (The hash index is derived from the entries.)
    pub fn same_as(&self, other: &Types) -> bool {
        self.entries == other.entries && self.parts == other.parts
    }

    pub fn shrink_to_fit(&mut self) {
        self.entries.shrink_to_fit();
        self.parts.shrink_to_fit();
        self.index.shrink_to_fit();
        self.same_hash.shrink_to_fit();
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn run(&self, r: Run) -> &[Ty] {
        &self.parts[r.start as usize..(r.start + r.len) as usize]
    }

    pub fn shape(&self, id: TyId) -> Shape<'_> {
        match self.entries[id.index()] {
            Entry::Struct { policy, fields } => Shape::Struct(policy, self.run(fields)),
            Entry::Array { n, elem } => Shape::Array(n, elem),
            Entry::Func {
                params,
                rets,
                variadic,
            } => Shape::Func(self.run(params), self.run(rets), variadic),
            Entry::Union { variants } => Shape::Union(self.run(variants)),
        }
    }

    /// The shape of `t`, if it is in a table.
    pub fn shape_of(&self, t: Ty) -> Option<Shape<'_>> {
        match t {
            Ty::Agg(id) => Some(self.shape(id)),
            _ => None,
        }
    }

    fn intern(&mut self, shape: Shape<'_>) -> Ty {
        let mut h = FxHasher::default();
        match shape {
            Shape::Struct(p, fs) => (0u8, p, fs).hash(&mut h),
            Shape::Array(n, t) => (1u8, n, t).hash(&mut h),
            Shape::Func(ps, rs, v) => (2u8, ps, rs, v).hash(&mut h),
            Shape::Union(vs) => (3u8, vs).hash(&mut h),
        }
        let hash = h.finish();
        let mut cur = self.index.get(&hash).copied().unwrap_or(NONE);
        while cur != NONE {
            if self.shape(TyId(cur)) == shape {
                return Ty::Agg(TyId(cur));
            }
            cur = self.same_hash[cur as usize];
        }
        let mut push = |ts: &[Ty]| {
            let start = self.parts.len() as u32;
            self.parts.extend_from_slice(ts);
            Run {
                start,
                len: ts.len() as u32,
            }
        };
        let entry = match shape {
            Shape::Struct(policy, fs) => Entry::Struct {
                policy,
                fields: push(fs),
            },
            Shape::Array(n, elem) => Entry::Array { n, elem },
            Shape::Func(ps, rs, variadic) => Entry::Func {
                params: push(ps),
                rets: push(rs),
                variadic,
            },
            Shape::Union(vs) => Entry::Union { variants: push(vs) },
        };
        let id = u32::try_from(self.entries.len()).expect("fewer than 2^32 types");
        self.entries.push(entry);
        let prev = self.index.insert(hash, id).unwrap_or(NONE);
        self.same_hash.push(prev);
        Ty::Agg(TyId(id))
    }

    /// `struct<policy>{fields}`; its fields must be types of this table.
    pub fn structure(&mut self, policy: Policy, fields: &[Ty]) -> Ty {
        self.intern(Shape::Struct(policy, fields))
    }

    /// `array<n x elem>`
    pub fn array(&mut self, n: u64, elem: Ty) -> Ty {
        self.intern(Shape::Array(n, elem))
    }

    /// `func<(params) -> rets>`
    pub fn func(&mut self, params: &[Ty], rets: &[Ty]) -> Ty {
        self.intern(Shape::Func(params, rets, false))
    }

    /// `func<(params, ...) -> rets>` when `variadic`, else `func<(params) -> rets>`.
    pub fn func_va(&mut self, params: &[Ty], rets: &[Ty], variadic: bool) -> Ty {
        self.intern(Shape::Func(params, rets, variadic))
    }

    /// `union<variants>`
    pub fn union(&mut self, variants: &[Ty]) -> Ty {
        self.intern(Shape::Union(variants))
    }

    /// `t` from table `from`, interned in this one.
    pub fn import(&mut self, from: &Types, t: Ty) -> Ty {
        let Ty::Agg(id) = t else { return t };
        let list = |me: &mut Types, ts: &[Ty]| -> Vec<Ty> {
            ts.iter().map(|&x| me.import(from, x)).collect()
        };
        match from.shape(id) {
            Shape::Struct(p, fs) => {
                let fs = list(self, fs);
                self.structure(p, &fs)
            }
            Shape::Array(n, e) => {
                let e = self.import(from, e);
                self.array(n, e)
            }
            Shape::Func(ps, rs, v) => {
                let (ps, rs) = (list(self, ps), list(self, rs));
                self.func_va(&ps, &rs, v)
            }
            Shape::Union(vs) => {
                let vs = list(self, vs);
                self.union(&vs)
            }
        }
    }

    /// Whether `a` in this table is the type `b` in table `other`.
    pub fn same(&self, a: Ty, other: &Types, b: Ty) -> bool {
        let list = |xs: &[Ty], ys: &[Ty]| {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(&x, &y)| self.same(x, other, y))
        };
        match (a, b) {
            (Ty::Agg(x), Ty::Agg(y)) => match (self.shape(x), other.shape(y)) {
                (Shape::Struct(p, fs), Shape::Struct(q, gs)) => p == q && list(fs, gs),
                (Shape::Array(n, e), Shape::Array(m, f)) => n == m && self.same(e, other, f),
                (Shape::Func(ps, rs, v), Shape::Func(qs, ss, w)) => {
                    v == w && list(ps, qs) && list(rs, ss)
                }
                (Shape::Union(vs), Shape::Union(ws)) => list(vs, ws),
                _ => false,
            },
            _ => a == b,
        }
    }

    /// Whether values of this type can exist in HFIR: anything but a function type or a
    /// `va_list` (Lean's `Ty.isHValue`).
    pub fn is_hvalue(&self, t: Ty) -> bool {
        t != Ty::VaList && !matches!(self.shape_of(t), Some(Shape::Func(..)))
    }

    /// Whether calls pass values of this type whole outside HFIR, as the C ABI's unit (Lean's
    /// `Ty.isComposite`): a struct or array of scalars and of such aggregates.
    pub fn is_composite(&self, t: Ty) -> bool {
        match self.shape_of(t) {
            Some(Shape::Struct(_, fs)) => fs.iter().all(|&f| f.is_value() || self.is_composite(f)),
            Some(Shape::Array(_, e)) => e.is_value() || self.is_composite(e),
            _ => false,
        }
    }

    /// Whether a variadic argument can be this composite (Lean's `Ty.isCComposite`): a nonempty
    /// `struct<C>` or array of scalars and of such composites.
    pub fn is_c_composite(&self, t: Ty) -> bool {
        match self.shape_of(t) {
            Some(Shape::Struct(Policy::C, fs)) => {
                !fs.is_empty() && fs.iter().all(|&f| f.is_value() || self.is_c_composite(f))
            }
            Some(Shape::Array(n, e)) => n > 0 && (e.is_value() || self.is_c_composite(e)),
            _ => false,
        }
    }

    /// Whether a variadic argument can have this type in memory space `space` (Lean's
    /// `SpaceCfg.isVararg`): a scalar that fits an argument slot, or a C composite.
    pub fn is_vararg(&self, space: &SpaceCfg, t: Ty) -> bool {
        space.is_vararg(t) || self.is_c_composite(t)
    }

    /// Whether `t` here is `u` of `other` up to Lean's `Ty.canon`, which makes arrays structs of
    /// their elements. `u` is canonical (a variadic argument's type: scalars and `struct<C>`s).
    pub fn canon_is(&self, t: Ty, other: &Types, u: Ty) -> bool {
        match (self.shape_of(t), other.shape_of(u)) {
            (Some(Shape::Struct(p, fs)), Some(Shape::Struct(q, gs))) => {
                p == q
                    && fs.len() == gs.len()
                    && fs.iter().zip(gs).all(|(&f, &g)| self.canon_is(f, other, g))
            }
            (Some(Shape::Array(n, e)), Some(Shape::Struct(Policy::C, gs))) => {
                n == gs.len() as u64 && gs.iter().all(|&g| self.canon_is(e, other, g))
            }
            (None, None) => t == u,
            _ => false,
        }
    }

    /// Whether a type has a `va_list` in it, which values can't (Lean's `Ty.hasVaList`).
    pub fn has_va_list(&self, t: Ty) -> bool {
        match t {
            Ty::VaList => true,
            Ty::Agg(id) => match self.shape(id) {
                Shape::Struct(_, fs) | Shape::Union(fs) => fs.iter().any(|&f| self.has_va_list(f)),
                Shape::Array(_, e) => self.has_va_list(e),
                Shape::Func(..) => false,
            },
            _ => false,
        }
    }

    /// The scalar types a value of type `t` becomes when lowered (Lean's `Lower.scalars`).
    pub fn scalars(&self, aw: u32, t: Ty, out: &mut Vec<Ty>) {
        match t {
            Ty::Slice => out.extend([Ty::Ptr, Ty::Int(aw)]),
            Ty::Agg(id) => match self.shape(id) {
                Shape::Struct(_, fs) => fs.iter().for_each(|&f| self.scalars(aw, f, out)),
                Shape::Array(n, e) => {
                    let start = out.len();
                    self.scalars(aw, e, out);
                    let k = out.len() - start;
                    for _ in 1..n {
                        out.extend_from_within(start..start + k);
                    }
                    if n == 0 {
                        out.truncate(start);
                    }
                }
                Shape::Union(vs) => {
                    out.push(Ty::Int(32));
                    vs.iter().for_each(|&v| self.scalars(aw, v, out));
                }
                Shape::Func(..) => out.push(t),
            },
            _ => out.push(t),
        }
    }

    /// How many scalars `t` becomes.
    pub fn num_scalars(&self, t: Ty) -> usize {
        match t {
            Ty::Slice => 2,
            Ty::Agg(id) => match self.shape(id) {
                Shape::Struct(_, fs) => fs.iter().map(|&f| self.num_scalars(f)).sum(),
                Shape::Array(n, e) => n as usize * self.num_scalars(e),
                Shape::Union(vs) => 1 + vs.iter().map(|&v| self.num_scalars(v)).sum::<usize>(),
                Shape::Func(..) => 1,
            },
            _ => 1,
        }
    }

    /// The scalars a value of type `t` is stored as, with their offsets from `base`, in order
    /// (Lean's `Ty.leaves`).
    pub fn leaves(&self, sp: &SpaceCfg, t: Ty, base: u128, out: &mut Vec<(u128, Ty)>) {
        match t {
            Ty::Slice => {
                out.push((base, Ty::Ptr));
                out.push((base + slice_layout(sp).0, Ty::Int(sp.addr_bits)));
            }
            Ty::Agg(id) => match self.shape(id) {
                Shape::Struct(p, fs) => {
                    let (offs, _, _) = self.place(sp, p, fs);
                    for (&f, &o) in fs.iter().zip(&offs) {
                        self.leaves(sp, f, base + o, out);
                    }
                }
                Shape::Array(n, e) => {
                    let stride = self.stride(sp, e);
                    for j in 0..u128::from(n) {
                        self.leaves(sp, e, base + j * stride, out);
                    }
                }
                _ => out.push((base, t)),
            },
            _ => out.push((base, t)),
        }
    }

    /// Append a type as text (Lean's `Ty.render`).
    pub fn write(&self, out: &mut String, t: Ty) {
        let list = |out: &mut String, ts: &[Ty]| {
            for (i, &t) in ts.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                self.write(out, t);
            }
        };
        match t {
            Ty::Int(w) => write!(out, "i{w}").unwrap(),
            Ty::Ptr => out.push_str("ptr"),
            Ty::Byte(w) => write!(out, "b{w}").unwrap(),
            Ty::Float(f) => out.push_str(f.name()),
            Ty::Agg(id) => match self.shape(id) {
                Shape::Struct(p, fs) => {
                    write!(out, "struct<{}>{{", p.name()).unwrap();
                    list(out, fs);
                    out.push('}');
                }
                Shape::Array(n, e) => {
                    write!(out, "array<{n} x ").unwrap();
                    self.write(out, e);
                    out.push('>');
                }
                Shape::Func(ps, rs, v) => {
                    out.push_str("func<(");
                    list(out, ps);
                    if v {
                        out.push_str(if ps.is_empty() { "..." } else { ", ..." });
                    }
                    out.push(')');
                    write_rets(out, rs, |out, t| self.write(out, *t));
                    out.push('>');
                }
                Shape::Union(vs) => {
                    out.push_str("union<");
                    list(out, vs);
                    out.push('>');
                }
            },
            Ty::Slice => out.push_str("slice"),
            Ty::VaList => out.push_str("va_list"),
        }
    }

    /// A type as text.
    pub fn show(&self, t: Ty) -> String {
        let mut out = String::new();
        self.write(&mut out, t);
        out
    }

    /// `(t1, t2)`, for messages.
    pub fn show_list(&self, ts: &[Ty]) -> String {
        let mut out = String::from("(");
        for (i, &t) in ts.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            self.write(&mut out, t);
        }
        out.push(')');
        out
    }

    // Layout (Lean's `Fir.Layout`). Sizes are 128-bit, so that the verifier sees a type that is
    // too large for the address space instead of an overflow; a verified type's size fits its
    // address space, which is at most 64 bits here.

    /// A type's size and alignment, in bytes (Lean's `Ty.dims`).
    pub fn dims(&self, sp: &SpaceCfg, t: Ty) -> (u128, u64) {
        match t {
            Ty::Int(w) | Ty::Byte(w) => (u128::from(w / 8), u64::from(sp.int_align(w))),
            Ty::Float(f) => (
                u128::from(f.width() / 8),
                u64::from(sp.int_align(f.width())),
            ),
            Ty::Ptr => (u128::from(sp.ptr_bits / 8), u64::from(sp.ptr_align)),
            Ty::Slice => {
                let (_, size, align) = slice_layout(sp);
                (size, align)
            }
            Ty::VaList => (u128::from(sp.va_size), u64::from(sp.va_align)),
            Ty::Agg(id) => match self.shape(id) {
                Shape::Struct(p, fs) => {
                    let (_, size, align) = self.place(sp, p, fs);
                    (size, align)
                }
                Shape::Array(n, e) => {
                    let (s, a) = self.dims(sp, e);
                    (u128::from(n).saturating_mul(align_up(s, a)), a)
                }
                Shape::Func(..) | Shape::Union(_) => (0, 1),
            },
        }
    }

    pub fn size(&self, sp: &SpaceCfg, t: Ty) -> u128 {
        self.dims(sp, t).0
    }

    pub fn align(&self, sp: &SpaceCfg, t: Ty) -> u64 {
        self.dims(sp, t).1
    }

    /// How far apart array elements of type `t` are.
    pub fn stride(&self, sp: &SpaceCfg, t: Ty) -> u128 {
        let (s, a) = self.dims(sp, t);
        align_up(s, a)
    }

    /// A struct's fields' offsets in declared order, its size, and its alignment (Lean's
    /// `placeFields` of `Ty.strides`).
    pub fn place(&self, sp: &SpaceCfg, p: Policy, fs: &[Ty]) -> (Vec<u128>, u128, u64) {
        let mut ds: Vec<(usize, u128, u64)> = fs
            .iter()
            .enumerate()
            .map(|(i, &f)| {
                let (s, a) = self.dims(sp, f);
                (i, align_up(s, a), a)
            })
            .collect();
        let align = ds.iter().fold(1, |m, d| m.max(d.2));
        if p == Policy::Auto {
            // Stable, like Lean's `mergeSort`.
            ds.sort_by_key(|d| std::cmp::Reverse(d.2));
        }
        let mut offs = vec![0; fs.len()];
        let mut o: u128 = 0;
        for &(i, s, a) in &ds {
            if p != Policy::Packed {
                o = align_up(o, a);
            }
            offs[i] = o;
            o = o.saturating_add(s);
        }
        match p {
            Policy::Packed => (offs, o, 1),
            _ => (offs, align_up(o, align), align),
        }
    }

    /// The offset of field `i` of a struct.
    pub fn field_offset(&self, sp: &SpaceCfg, t: Ty, i: u32) -> Option<u128> {
        match self.shape_of(t)? {
            Shape::Struct(p, fs) => self.place(sp, p, fs).0.get(i as usize).copied(),
            _ => None,
        }
    }
}

/// A slice's layout, as `struct<C>{ptr, iA}`: the length's offset, the size, and the alignment
/// (Lean's `SpaceCfg.sliceLayout`).
pub fn slice_layout(sp: &SpaceCfg) -> (u128, u128, u64) {
    let pa = u64::from(sp.ptr_align);
    let ia = u64::from(sp.int_align(sp.addr_bits));
    let ps = align_up(u128::from(sp.ptr_bits / 8), pa);
    let is = align_up(u128::from(sp.addr_bits / 8), ia);
    let off = align_up(ps, ia);
    let align = pa.max(ia);
    (off, align_up(off + is, align), align)
}

/// `x` rounded up to a multiple of `a` (Lean's `alignUp`).
pub fn align_up(x: u128, a: u64) -> u128 {
    let a = u128::from(a);
    if a <= 1 {
        x
    } else {
        x.saturating_add(a - 1) / a * a
    }
}

/// ` -> T`, ` -> (T, U)`, or nothing: how function headers and types write results (Lean's
/// `retsText`).
pub fn write_rets<T>(out: &mut String, rs: &[T], mut write: impl FnMut(&mut String, &T)) {
    match rs {
        [] => {}
        [t] => {
            out.push_str(" -> ");
            write(out, t);
        }
        ts => {
            out.push_str(" -> (");
            for (i, t) in ts.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write(out, t);
            }
            out.push(')');
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_types_share_an_entry() {
        let mut t = Types::new();
        let a = t.array(4, Ty::Int(32));
        let s = t.structure(Policy::C, &[Ty::Int(8), a, Ty::Ptr]);
        let a2 = t.array(4, Ty::Int(32));
        let s2 = t.structure(Policy::C, &[Ty::Int(8), a2, Ty::Ptr]);
        assert_eq!((a, s), (a2, s2));
        assert_ne!(s, t.structure(Policy::Packed, &[Ty::Int(8), a, Ty::Ptr]));
        assert_ne!(t.func(&[Ty::Ptr], &[]), t.func(&[], &[Ty::Ptr]));
        assert_eq!(t.len(), 5);
        assert_eq!(t.show(s), "struct<C>{i8, array<4 x i32>, ptr}");
        let sp = SpaceCfg::default();
        assert_eq!(t.dims(&sp, s), (32, 8));
        assert_eq!(t.field_offset(&sp, s, 2), Some(24));
    }
}
