//! A function's code, stored data-oriented. This is the default for every IR structure in the
//! crate:
//!
//! * **Ids, not pointers.** Ops, regions, values, strings, integers, and holes are 32-bit ids
//!   into flat arrays owned by the function's [`Body`]. Nothing points into another body, so
//!   functions can be built, checked, and dropped independently.
//! * **Columns by access pattern.** Op and value fields that passes read separately live in
//!   separate arrays indexed by id (an op's kind, its operand and result lists, its list links,
//!   and its location are four columns), so a pass reads only what it needs. Fields always used
//!   together stay together, to keep the number of arrays (and allocations) per body small.
//! * **No heap data per op.** [`OpKind`], [`Operand`], and facts are small `Copy` values. What
//!   varies in size (names, big integers, holes) lives once in a side table, and lists (operands,
//!   results, regions) are runs in shared pools.
//! * **Stable ids.** A region's ops form an index-based doubly linked list, so inserting and
//!   removing ops never moves other ops.

use std::fmt;

use num_bigint::BigInt;

use crate::ir::{Loc, OpKind, TrustedFact, Ty};

macro_rules! id {
    ($(#[$m:meta])* $name:ident) => {
        $(#[$m])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        pub struct $name(u32);

        impl $name {
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

id!(
    /// An op in a [`Body`].
    OpId
);
id!(
    /// A region in a [`Body`].
    RegionId
);
id!(
    /// An SSA value (an op result or a region parameter) in a [`Body`].
    ValueId
);
id!(
    /// A string in a [`Body`]: a callee, an allocator family, a hole's name.
    StrId
);
id!(
    /// An integer in a [`Body`]: a constant or a range bound. See [`Body::int`].
    IntId
);
id!(
    /// A hole operand (`?name: T`) in a [`Body`].
    HoleId
);

impl ValueId {
    /// Stands in for an unresolved name in code that is parsed only to find syntax errors.
    pub(crate) const PLACEHOLDER: ValueId = ValueId(0);
}

impl StrId {
    /// Stands in for an op's string before the parser stores it.
    pub(crate) const PLACEHOLDER: StrId = StrId(0);
}

impl IntId {
    /// Stands in for an op's integer before the parser stores it.
    pub(crate) const PLACEHOLDER: IntId = IntId(0);
}

/// Marks an absent id in a column.
const NONE: u32 = u32::MAX;
/// Marks an op that is in no region (it was unlinked).
const DETACHED: u32 = u32::MAX - 1;
/// The top bit of an [`Operand`] or [`IntId`] picks the second of two kinds.
const TAG: u32 = 1 << 31;

fn index32(n: usize) -> u32 {
    match u32::try_from(n) {
        Ok(n) if n < TAG => n,
        _ => panic!("a function body holds fewer than 2^31 entries of each kind"),
    }
}

fn opt(x: u32) -> Option<u32> {
    (x != NONE).then_some(x)
}

/// A run of entries in one of the body's pools.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
struct Span {
    start: u32,
    len: u32,
}

impl Span {
    fn range(self) -> std::ops::Range<usize> {
        self.start as usize..(self.start + self.len) as usize
    }
}

fn push_span<T>(pool: &mut Vec<T>, items: impl IntoIterator<Item = T>) -> Span {
    let start = pool.len();
    pool.extend(items);
    Span {
        start: index32(start),
        len: index32(pool.len() - start),
    }
}

/// An operand: a value, or a hole standing for a value not written yet. Packed in 32 bits.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Operand(u32);

/// What an [`Operand`] refers to.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum OperandKind {
    Value(ValueId),
    Hole(HoleId),
}

impl Operand {
    pub fn value(v: ValueId) -> Operand {
        Operand(v.0)
    }

    pub fn hole(h: HoleId) -> Operand {
        Operand(h.0 | TAG)
    }

    pub fn get(self) -> OperandKind {
        if self.0 & TAG == 0 {
            OperandKind::Value(ValueId(self.0))
        } else {
            OperandKind::Hole(HoleId(self.0 & !TAG))
        }
    }
}

impl fmt::Debug for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.get().fmt(f)
    }
}

/// An integer stored in a [`Body`]: small ones inline, others as big integers.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Int<'a> {
    Small(i64),
    Big(&'a BigInt),
}

impl Int<'_> {
    pub fn to_bigint(self) -> BigInt {
        match self {
            Int::Small(n) => BigInt::from(n),
            Int::Big(n) => n.clone(),
        }
    }
}

impl fmt::Display for Int<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Int::Small(n) => n.fmt(f),
            Int::Big(n) => n.fmt(f),
        }
    }
}

/// Where a value comes from.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ValueDef {
    Result { op: OpId, index: u32 },
    Param { region: RegionId, index: u32 },
}

/// A value to create: its name, type, and facts.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ValueSpec<'a> {
    pub name: &'a str,
    pub ty: Ty,
    pub facts: Vec<TrustedFact>,
}

/// An op's operand, result, and region lists.
#[derive(Clone, Copy, Debug)]
struct OpShape {
    results: Span,
    operands: Span,
    regions: Span,
}

/// An op's neighbors in its region (`NONE` at the ends). `prev` is `DETACHED` for an unlinked
/// op.
#[derive(Clone, Copy, Debug)]
struct Link {
    prev: u32,
    next: u32,
}

/// What only printing, diagnostics, and structural queries read.
#[derive(Clone, Copy, Debug)]
struct OpCold {
    loc: Option<Loc>,
    parent: RegionId,
}

#[derive(Clone, Copy, Debug)]
struct RegionData {
    params: Span,
    first: u32,
    last: u32,
    parent: u32,
}

#[derive(Clone, Copy, Debug)]
struct ValueInfo {
    name: Span,
    facts: Span,
    def: ValueDef,
}

/// A function's code: its entry region and everything nested in it.
#[derive(Clone, Debug)]
pub struct Body {
    // Ops, by `OpId`.
    op_kind: Vec<OpKind>,
    op_shape: Vec<OpShape>,
    op_link: Vec<Link>,
    op_cold: Vec<OpCold>,
    regions: Vec<RegionData>,
    // Values, by `ValueId`.
    value_ty: Vec<Ty>,
    value_info: Vec<ValueInfo>,
    // Pools: runs referred to by spans.
    operands: Vec<Operand>,
    region_ids: Vec<RegionId>,
    facts: Vec<TrustedFact>,
    /// All text: value names and strings, end to end.
    text: String,
    // Side tables, by id.
    strs: Vec<Span>,
    small_ints: Vec<i64>,
    big_ints: Vec<BigInt>,
    holes: Vec<(StrId, Ty)>,
    entry: RegionId,
}

impl Default for Body {
    fn default() -> Body {
        Body::new()
    }
}

impl Body {
    /// An empty body. Its entry region's parameters (the function's) are set with
    /// [`Body::set_params`].
    pub fn new() -> Body {
        let mut body = Body {
            op_kind: Vec::new(),
            op_shape: Vec::new(),
            op_link: Vec::new(),
            op_cold: Vec::new(),
            regions: Vec::new(),
            value_ty: Vec::new(),
            value_info: Vec::new(),
            operands: Vec::new(),
            region_ids: Vec::new(),
            facts: Vec::new(),
            text: String::new(),
            strs: Vec::new(),
            small_ints: Vec::new(),
            big_ints: Vec::new(),
            holes: Vec::new(),
            entry: RegionId(0),
        };
        body.entry = body.new_region(None, []);
        body
    }

    /// How many ops the body has; op ids are below this.
    pub fn num_ops(&self) -> usize {
        self.op_kind.len()
    }

    /// Release spare capacity.
    pub fn shrink_to_fit(&mut self) {
        self.op_kind.shrink_to_fit();
        self.op_shape.shrink_to_fit();
        self.op_link.shrink_to_fit();
        self.op_cold.shrink_to_fit();
        self.regions.shrink_to_fit();
        self.value_ty.shrink_to_fit();
        self.value_info.shrink_to_fit();
        self.operands.shrink_to_fit();
        self.region_ids.shrink_to_fit();
        self.facts.shrink_to_fit();
        self.text.shrink_to_fit();
        self.strs.shrink_to_fit();
        self.small_ints.shrink_to_fit();
        self.big_ints.shrink_to_fit();
        self.holes.shrink_to_fit();
    }

    /// Empty the body, keeping its arrays' capacity, so it can be reused to build another
    /// function. A builder that is reused this way and cloned once each function is done (a
    /// clone allocates exactly what is used) spends no time growing arrays and leaves no spare
    /// capacity behind.
    pub fn clear(&mut self) {
        self.op_kind.clear();
        self.op_shape.clear();
        self.op_link.clear();
        self.op_cold.clear();
        self.regions.clear();
        self.value_ty.clear();
        self.value_info.clear();
        self.operands.clear();
        self.region_ids.clear();
        self.facts.clear();
        self.text.clear();
        self.strs.clear();
        self.small_ints.clear();
        self.big_ints.clear();
        self.holes.clear();
        self.entry = self.new_region(None, []);
    }

    pub fn entry(&self) -> RegionId {
        self.entry
    }

    fn push_text(&mut self, s: &str) -> Span {
        let span = Span {
            start: index32(self.text.len()),
            len: index32(s.len()),
        };
        self.text.push_str(s);
        span
    }

    /// Store a string.
    pub fn add_str(&mut self, s: &str) -> StrId {
        let span = self.push_text(s);
        let id = StrId(index32(self.strs.len()));
        self.strs.push(span);
        id
    }

    pub fn str(&self, s: StrId) -> &str {
        &self.text[self.strs[s.index()].range()]
    }

    /// Store an integer.
    pub fn add_int(&mut self, n: BigInt) -> IntId {
        match i64::try_from(&n) {
            Ok(small) => self.add_small_int(small),
            Err(_) => {
                let id = IntId(index32(self.big_ints.len()) | TAG);
                self.big_ints.push(n);
                id
            }
        }
    }

    /// Store an integer that fits in 64 bits.
    pub fn add_small_int(&mut self, n: i64) -> IntId {
        let id = IntId(index32(self.small_ints.len()));
        self.small_ints.push(n);
        id
    }

    pub fn int(&self, n: IntId) -> Int<'_> {
        if n.0 & TAG == 0 {
            Int::Small(self.small_ints[n.index()])
        } else {
            Int::Big(&self.big_ints[(n.0 & !TAG) as usize])
        }
    }

    /// Store a hole operand `?name: ty`.
    pub fn add_hole(&mut self, name: &str, ty: Ty) -> Operand {
        let name = self.add_str(name);
        let id = HoleId(index32(self.holes.len()));
        self.holes.push((name, ty));
        Operand::hole(id)
    }

    pub fn hole_name(&self, h: HoleId) -> &str {
        self.str(self.holes[h.index()].0)
    }

    pub fn hole_ty(&self, h: HoleId) -> Ty {
        self.holes[h.index()].1
    }

    fn new_region<'s>(
        &mut self,
        parent: Option<OpId>,
        params: impl IntoIterator<Item = ValueSpec<'s>>,
    ) -> RegionId {
        let id = RegionId(index32(self.regions.len()));
        let params = self.new_values(params, |index| ValueDef::Param { region: id, index });
        self.regions.push(RegionData {
            params,
            first: NONE,
            last: NONE,
            parent: parent.map_or(NONE, |p| p.0),
        });
        id
    }

    /// Give a region without parameters its parameters (the entry region gets the function's).
    pub fn set_params<'s>(
        &mut self,
        region: RegionId,
        params: impl IntoIterator<Item = ValueSpec<'s>>,
    ) {
        assert_eq!(
            self.regions[region.index()].params.len,
            0,
            "the region already has parameters"
        );
        let span = self.new_values(params, |index| ValueDef::Param { region, index });
        self.regions[region.index()].params = span;
    }

    fn new_values<'s>(
        &mut self,
        specs: impl IntoIterator<Item = ValueSpec<'s>>,
        def: impl Fn(u32) -> ValueDef,
    ) -> Span {
        let start = self.value_ty.len();
        for (i, spec) in specs.into_iter().enumerate() {
            let facts = push_span(&mut self.facts, spec.facts);
            let name = self.push_text(spec.name);
            self.value_ty.push(spec.ty);
            self.value_info.push(ValueInfo {
                name,
                facts,
                def: def(index32(i)),
            });
        }
        Span {
            start: index32(start),
            len: index32(self.value_ty.len() - start),
        }
    }

    /// Append an op to the end of `region`. `regions` gives each of the op's regions its
    /// parameters; the regions start empty.
    pub fn append_op<'s>(
        &mut self,
        region: RegionId,
        kind: OpKind,
        operands: impl IntoIterator<Item = Operand>,
        results: impl IntoIterator<Item = ValueSpec<'s>>,
        regions: impl IntoIterator<Item = Vec<ValueSpec<'s>>>,
        loc: Option<Loc>,
    ) -> OpId {
        let id = OpId(index32(self.op_kind.len()));
        let operands = push_span(&mut self.operands, operands);
        let results = self.new_values(results, |index| ValueDef::Result { op: id, index });
        let start = self.region_ids.len();
        for params in regions {
            let r = self.new_region(Some(id), params);
            self.region_ids.push(r);
        }
        let regions = Span {
            start: index32(start),
            len: index32(self.region_ids.len() - start),
        };
        let prev = self.regions[region.index()].last;
        self.op_kind.push(kind);
        self.op_shape.push(OpShape {
            results,
            operands,
            regions,
        });
        self.op_link.push(Link { prev, next: NONE });
        self.op_cold.push(OpCold {
            loc,
            parent: region,
        });
        match opt(prev) {
            Some(p) => self.op_link[p as usize].next = id.0,
            None => self.regions[region.index()].first = id.0,
        }
        self.regions[region.index()].last = id.0;
        id
    }

    /// Remove an op from its region. Its id stays valid but no longer appears in any region.
    /// Unlinking an op that is already unlinked does nothing.
    pub fn unlink(&mut self, op: OpId) {
        let Link { prev, next } = self.op_link[op.index()];
        if prev == DETACHED {
            return;
        }
        let parent = self.op_cold[op.index()].parent.index();
        match opt(prev) {
            Some(p) => self.op_link[p as usize].next = next,
            None => self.regions[parent].first = next,
        }
        match opt(next) {
            Some(n) => self.op_link[n as usize].prev = prev,
            None => self.regions[parent].last = prev,
        }
        self.op_link[op.index()] = Link {
            prev: DETACHED,
            next: NONE,
        };
    }

    /// Whether the op is in a region (it hasn't been unlinked).
    pub fn is_linked(&self, op: OpId) -> bool {
        self.op_link[op.index()].prev != DETACHED
    }

    // Ops

    pub fn kind(&self, op: OpId) -> OpKind {
        self.op_kind[op.index()]
    }

    pub fn results(&self, op: OpId) -> impl ExactSizeIterator<Item = ValueId> + Clone + use<> {
        self.op_shape[op.index()]
            .results
            .range()
            .map(|i| ValueId(i as u32))
    }

    pub fn operands(&self, op: OpId) -> &[Operand] {
        &self.operands[self.op_shape[op.index()].operands.range()]
    }

    pub fn regions(&self, op: OpId) -> &[RegionId] {
        &self.region_ids[self.op_shape[op.index()].regions.range()]
    }

    pub fn loc(&self, op: OpId) -> Option<Loc> {
        self.op_cold[op.index()].loc
    }

    pub fn parent(&self, op: OpId) -> RegionId {
        self.op_cold[op.index()].parent
    }

    pub fn next(&self, op: OpId) -> Option<OpId> {
        opt(self.op_link[op.index()].next).map(OpId)
    }

    pub fn prev(&self, op: OpId) -> Option<OpId> {
        match self.op_link[op.index()].prev {
            DETACHED => None,
            p => opt(p).map(OpId),
        }
    }

    // Regions

    pub fn params(
        &self,
        region: RegionId,
    ) -> impl ExactSizeIterator<Item = ValueId> + Clone + use<> {
        self.regions[region.index()]
            .params
            .range()
            .map(|i| ValueId(i as u32))
    }

    /// The ops of a region, in order.
    pub fn ops(&self, region: RegionId) -> Ops<'_> {
        Ops {
            links: &self.op_link,
            cur: self.regions[region.index()].first,
        }
    }

    pub fn is_empty(&self, region: RegionId) -> bool {
        self.regions[region.index()].first == NONE
    }

    /// The op whose region this is; `None` for the entry region.
    pub fn parent_op(&self, region: RegionId) -> Option<OpId> {
        opt(self.regions[region.index()].parent).map(OpId)
    }

    // Values

    /// How many values the body has; value ids are below this.
    pub fn num_values(&self) -> usize {
        self.value_ty.len()
    }

    pub fn name(&self, value: ValueId) -> &str {
        &self.text[self.value_info[value.index()].name.range()]
    }

    pub fn ty(&self, value: ValueId) -> Ty {
        self.value_ty[value.index()]
    }

    pub fn facts(&self, value: ValueId) -> &[TrustedFact] {
        &self.facts[self.value_info[value.index()].facts.range()]
    }

    pub fn def(&self, value: ValueId) -> ValueDef {
        self.value_info[value.index()].def
    }
}

/// The ops of a region, in order.
pub struct Ops<'a> {
    links: &'a [Link],
    cur: u32,
}

impl Iterator for Ops<'_> {
    type Item = OpId;

    fn next(&mut self) -> Option<OpId> {
        let op = opt(self.cur)?;
        self.cur = self.links[op as usize].next;
        Some(OpId(op))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn val(name: &str) -> ValueSpec<'_> {
        ValueSpec {
            name,
            ty: Ty::Int(32),
            facts: vec![],
        }
    }

    #[test]
    fn ops_stay_in_order_and_unlink() {
        let mut b = Body::new();
        let r = b.entry();
        b.set_params(r, [val("x")]);
        let x = Operand::value(b.params(r).next().unwrap());
        let a = b.append_op(r, OpKind::Copy, [x], [val("a")], [], None);
        let c = b.append_op(r, OpKind::Copy, [x], [val("c")], [], None);
        let d = b.append_op(r, OpKind::Ret, [], [], [], None);
        assert_eq!(b.ops(r).collect::<Vec<_>>(), [a, c, d]);
        b.unlink(c);
        assert_eq!(b.ops(r).collect::<Vec<_>>(), [a, d]);
        b.unlink(c);
        assert_eq!(b.ops(r).collect::<Vec<_>>(), [a, d]);
        assert!(!b.is_linked(c));
        assert_eq!(b.prev(c), None);
        b.unlink(a);
        b.unlink(d);
        assert!(b.is_empty(r));
        let a_val = b.results(a).next().unwrap();
        assert_eq!(b.name(a_val), "a");
        assert_eq!(b.def(a_val), ValueDef::Result { op: a, index: 0 });
    }

    #[test]
    fn side_tables() {
        let mut b = Body::new();
        let s = b.add_str("c.malloc");
        let small = b.add_int(BigInt::from(-5));
        let big = b.add_int(BigInt::from(1) << 100u32);
        let h = b.add_hole("todo", Ty::Ptr);
        assert_eq!(b.str(s), "c.malloc");
        assert_eq!(b.int(small), Int::Small(-5));
        assert_eq!(
            b.int(big).to_string(),
            (BigInt::from(1) << 100u32).to_string()
        );
        match h.get() {
            OperandKind::Hole(h) => {
                assert_eq!((b.hole_name(h), b.hole_ty(h)), ("todo", Ty::Ptr));
            }
            OperandKind::Value(_) => panic!("expected a hole"),
        }
        assert_eq!(std::mem::size_of::<Operand>(), 4);
        assert_eq!(std::mem::size_of::<OpKind>(), 16);
    }
}
