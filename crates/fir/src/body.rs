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
//!   varies in size (names, big integers, holes, branch targets and `cf.switch` cases) lives once
//!   in a side table, and lists (operands, results, regions) are runs in shared pools.
//! * **Stable ids.** A region's ops form an index-based doubly linked list, so inserting and
//!   removing ops never moves other ops.
//! * **Use lists on demand, in columns.** Each value's uses (the operand slots that name it)
//!   form an index-based singly linked list: a head per value, and a next link per operand
//!   slot, parallel to the operand pool. A use is its slot's index ([`UseId`]); its op is found
//!   by binary search, since ops take their operand runs in id order, so no column stores it.
//!   The lists are an index that passes build ([`Body::build_uses`], one sweep over the
//!   operands); from then on every edit keeps them exact ([`Body::check_invariants`] checks
//!   them). Parsing and verifying don't need them and don't pay for them: kept up to date while
//!   parsing, they cost 8% of the parse time. Removing one use walks its value's list; values
//!   have few uses, and [`Body::replace_all_uses`] moves a whole list at once.

use std::fmt;

use num_bigint::BigInt;

use crate::ir::{Loc, OpKind, TrustedFact, Ty};
use crate::types::Types;

macro_rules! id {
    ($(#[$m:meta])* $name:ident) => {
        $(#[$m])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        pub struct $name(u32);

        impl $name {
            pub fn index(self) -> usize {
                self.0 as usize
            }

            /// The id as a 32-bit number, as the C API passes it.
            pub fn raw(self) -> u32 {
                self.0
            }

            /// The id a [`raw`](Self::raw) number stands for. Nothing checks that it exists.
            pub fn from_raw(n: u32) -> Self {
                $name(n)
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
id!(
    /// A use of a value: one operand slot of one op. See [`Body::uses`].
    UseId
);
id!(
    /// A branch target in a [`Body`]: a block label and an argument count. See [`Body::succ`].
    SuccId
);

/// `cf.switch`'s cases in a [`Body`]: a run in its case table. See [`Body::cases`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct CasesId {
    start: u32,
    len: u32,
}

impl CasesId {
    /// No cases; also what an op's cases are before the parser stores them.
    pub const EMPTY: CasesId = CasesId { start: 0, len: 0 };
}

/// A branch target (Lean's `Succ`): a block of the nearest enclosing `cf.blocks`, by label, and
/// how many of the branch's operands are its arguments. A branch's operands are its own, then
/// each target's arguments in the order the targets are written.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Succ {
    pub label: StrId,
    pub nargs: u32,
}

/// One case of `cf.switch`: its key, and where it jumps.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Case {
    pub key: IntId,
    pub succ: Succ,
}

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

impl SuccId {
    /// Stands in for an op's branch target before the parser stores it.
    pub(crate) const PLACEHOLDER: SuccId = SuccId(0);
}

/// Marks an absent id in a column.
const NONE: u32 = u32::MAX;
/// Marks an op that is in no region (it was unlinked), and an operand slot in no use list (a
/// hole, or an operand of an erased op) in `use_next`.
const DETACHED: u32 = u32::MAX - 1;
/// Marks an erased op.
const ERASED: u32 = u32::MAX - 2;
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

/// An operand: a value, or a hole standing for a value not written yet. Packed in 32 bits: a
/// value's id, or a hole's with the top bit set.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
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

    /// The packed 32 bits, as the C API passes them.
    pub fn raw(self) -> u32 {
        self.0
    }

    pub fn from_raw(n: u32) -> Operand {
        Operand(n)
    }

    pub fn get(self) -> OperandKind {
        if self.0 & TAG == 0 {
            OperandKind::Value(ValueId(self.0))
        } else {
            OperandKind::Hole(HoleId(self.0 & !TAG))
        }
    }
}

impl From<ValueId> for Operand {
    fn from(v: ValueId) -> Operand {
        Operand::value(v)
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
/// op and `ERASED` for an erased one.
#[derive(Clone, Copy, Debug)]
struct Link {
    prev: u32,
    next: u32,
}

/// What only printing, diagnostics, and structural queries read: the location, and the parent
/// region's id with `TAG` set when there is a location (`Option<Loc>` would take 4 more bytes).
#[derive(Clone, Copy, Debug)]
struct OpCold {
    loc: Loc,
    parent: u32,
}

impl OpCold {
    fn new(loc: Option<Loc>, parent: RegionId) -> OpCold {
        match loc {
            Some(loc) => OpCold {
                loc,
                parent: parent.0 | TAG,
            },
            None => OpCold {
                loc: Loc { line: 0, col: 0 },
                parent: parent.0,
            },
        }
    }

    fn loc(self) -> Option<Loc> {
        (self.parent & TAG != 0).then_some(self.loc)
    }

    fn parent(self) -> RegionId {
        RegionId(self.parent & !TAG)
    }

    fn set_parent(&mut self, parent: RegionId) {
        self.parent = parent.0 | (self.parent & TAG);
    }
}

#[derive(Clone, Copy, Debug)]
struct RegionData {
    params: Span,
    first: u32,
    last: u32,
    parent: u32,
    /// A block's label (a [`StrId`]), or `NONE`.
    label: u32,
}

#[derive(Clone, Copy, Debug)]
struct ValueInfo {
    name: Span,
    facts: Span,
    def: PackedDef,
}

/// A [`ValueDef`] in 8 bytes: the op or region id, with `TAG` set for a region, and the index.
#[derive(Clone, Copy, Debug)]
struct PackedDef(u32, u32);

impl PackedDef {
    fn pack(d: ValueDef) -> PackedDef {
        match d {
            ValueDef::Result { op, index } => PackedDef(op.0, index),
            ValueDef::Param { region, index } => PackedDef(region.0 | TAG, index),
        }
    }

    fn unpack(self) -> ValueDef {
        let PackedDef(id, index) = self;
        if id & TAG == 0 {
            ValueDef::Result {
                op: OpId(id),
                index,
            }
        } else {
            ValueDef::Param {
                region: RegionId(id & !TAG),
                index,
            }
        }
    }
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
    /// The first use of each value, or `NONE`; empty until `build_uses`.
    first_use: Vec<u32>,
    // Pools: runs referred to by spans.
    operands: Vec<Operand>,
    /// Each operand slot's next use in its value's use list (`NONE` at the end, `DETACHED` for
    /// a slot in no list), by `UseId`; empty until `build_uses`.
    use_next: Vec<u32>,
    /// Whether the use lists are built (and kept up to date).
    uses_built: bool,
    region_ids: Vec<RegionId>,
    facts: Vec<TrustedFact>,
    /// All text: value names and strings, end to end.
    text: String,
    // Side tables, by id.
    strs: Vec<Span>,
    small_ints: Vec<i64>,
    big_ints: Vec<BigInt>,
    holes: Vec<(StrId, Ty)>,
    succs: Vec<Succ>,
    cases: Vec<Case>,
    /// The struct, array, and function types the body's values and ops name.
    types: Types,
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
            first_use: Vec::new(),
            operands: Vec::new(),
            use_next: Vec::new(),
            uses_built: false,
            region_ids: Vec::new(),
            facts: Vec::new(),
            text: String::new(),
            strs: Vec::new(),
            small_ints: Vec::new(),
            big_ints: Vec::new(),
            holes: Vec::new(),
            succs: Vec::new(),
            cases: Vec::new(),
            types: Types::new(),
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
        self.first_use.shrink_to_fit();
        self.operands.shrink_to_fit();
        self.use_next.shrink_to_fit();
        self.region_ids.shrink_to_fit();
        self.facts.shrink_to_fit();
        self.text.shrink_to_fit();
        self.strs.shrink_to_fit();
        self.small_ints.shrink_to_fit();
        self.big_ints.shrink_to_fit();
        self.holes.shrink_to_fit();
        self.succs.shrink_to_fit();
        self.cases.shrink_to_fit();
        self.types.shrink_to_fit();
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
        self.first_use.clear();
        self.operands.clear();
        self.use_next.clear();
        self.uses_built = false;
        self.region_ids.clear();
        self.facts.clear();
        self.text.clear();
        self.strs.clear();
        self.small_ints.clear();
        self.big_ints.clear();
        self.holes.clear();
        self.succs.clear();
        self.cases.clear();
        self.types.clear();
        self.entry = self.new_region(None, []);
    }

    pub fn entry(&self) -> RegionId {
        self.entry
    }

    /// The table of the struct, array, and function types the body names.
    pub fn types(&self) -> &Types {
        &self.types
    }

    pub fn types_mut(&mut self) -> &mut Types {
        &mut self.types
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

    /// Store a branch target.
    pub fn add_succ(&mut self, s: Succ) -> SuccId {
        let id = SuccId(index32(self.succs.len()));
        self.succs.push(s);
        id
    }

    pub fn succ(&self, s: SuccId) -> Succ {
        self.succs[s.index()]
    }

    /// Store `cf.switch`'s cases.
    pub fn add_cases(&mut self, cases: impl IntoIterator<Item = Case>) -> CasesId {
        let span = push_span(&mut self.cases, cases);
        CasesId {
            start: span.start,
            len: span.len,
        }
    }

    pub fn cases(&self, c: CasesId) -> &[Case] {
        &self.cases[c.start as usize..(c.start + c.len) as usize]
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
            label: NONE,
        });
        id
    }

    /// Make a block of `op` (a `cf.blocks`) with this label and parameters, and nothing in it.
    /// It becomes one of `op`'s regions with [`Body::set_regions`]; this lets a parser make each
    /// block when it reaches it, after the blocks before it are filled.
    pub fn new_block<'s>(
        &mut self,
        op: OpId,
        label: StrId,
        params: impl IntoIterator<Item = ValueSpec<'s>>,
    ) -> RegionId {
        let r = self.new_region(Some(op), params);
        self.regions[r.index()].label = label.0;
        r
    }

    /// Give an op without regions these regions, made by [`Body::new_block`].
    pub fn set_regions(&mut self, op: OpId, regions: &[RegionId]) {
        assert_eq!(
            self.op_shape[op.index()].regions.len,
            0,
            "the op already has regions"
        );
        self.op_shape[op.index()].regions =
            push_span(&mut self.region_ids, regions.iter().copied());
    }

    /// Label a region, as a block of `cf.blocks` (the generic form may label any region).
    pub fn set_label(&mut self, region: RegionId, label: StrId) {
        self.regions[region.index()].label = label.0;
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
                def: PackedDef::pack(def(index32(i))),
            });
            if self.uses_built {
                self.first_use.push(NONE);
            }
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
        let id = self.create_op(region, kind, operands, results, regions, loc);
        let last = self.regions[region.index()].last;
        self.link_between(region, last, NONE, id);
        id
    }

    /// Insert an op right before `before`, in its region. Like [`Body::append_op`] otherwise.
    pub fn insert_before<'s>(
        &mut self,
        before: OpId,
        kind: OpKind,
        operands: impl IntoIterator<Item = Operand>,
        results: impl IntoIterator<Item = ValueSpec<'s>>,
        regions: impl IntoIterator<Item = Vec<ValueSpec<'s>>>,
        loc: Option<Loc>,
    ) -> OpId {
        assert!(
            self.is_linked(before),
            "insert_before: the op is in no region"
        );
        let region = self.parent(before);
        let id = self.create_op(region, kind, operands, results, regions, loc);
        let prev = self.op_link[before.index()].prev;
        self.link_between(region, prev, before.0, id);
        id
    }

    /// Insert an op right after `after`, in its region. Like [`Body::append_op`] otherwise.
    pub fn insert_after<'s>(
        &mut self,
        after: OpId,
        kind: OpKind,
        operands: impl IntoIterator<Item = Operand>,
        results: impl IntoIterator<Item = ValueSpec<'s>>,
        regions: impl IntoIterator<Item = Vec<ValueSpec<'s>>>,
        loc: Option<Loc>,
    ) -> OpId {
        assert!(
            self.is_linked(after),
            "insert_after: the op is in no region"
        );
        let region = self.parent(after);
        let id = self.create_op(region, kind, operands, results, regions, loc);
        let next = self.op_link[after.index()].next;
        self.link_between(region, after.0, next, id);
        id
    }

    /// Create an op in no region yet (but with `region` as its parent), and add its operands to
    /// their values' use lists. Ops take their operand runs in id order, which [`Body::user`]
    /// relies on.
    fn create_op<'s>(
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
        if self.uses_built {
            for u in operands.range() {
                self.use_next.push(DETACHED);
                self.link_use(u as u32);
            }
        }
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
        self.op_kind.push(kind);
        self.op_shape.push(OpShape {
            results,
            operands,
            regions,
        });
        self.op_link.push(Link {
            prev: DETACHED,
            next: NONE,
        });
        self.op_cold.push(OpCold::new(loc, region));
        id
    }

    /// Put an op that is in no region between `prev` and `next` (`NONE` at the ends) of
    /// `region`.
    fn link_between(&mut self, region: RegionId, prev: u32, next: u32, op: OpId) {
        self.op_link[op.index()] = Link { prev, next };
        self.op_cold[op.index()].set_parent(region);
        let r = &mut self.regions[region.index()];
        match opt(prev) {
            Some(p) => self.op_link[p as usize].next = op.0,
            None => r.first = op.0,
        }
        match opt(next) {
            Some(n) => self.op_link[n as usize].prev = op.0,
            None => r.last = op.0,
        }
    }

    /// Remove an op from its region. Its id stays valid but no longer appears in any region; its
    /// operands are still uses (see [`Body::erase`] to drop them). Unlinking an op that is
    /// already unlinked does nothing.
    pub fn unlink(&mut self, op: OpId) {
        let Link { prev, next } = self.op_link[op.index()];
        if prev == DETACHED || prev == ERASED {
            return;
        }
        let parent = self.op_cold[op.index()].parent().index();
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

    /// Whether the op is in a region (it hasn't been unlinked or erased).
    pub fn is_linked(&self, op: OpId) -> bool {
        !matches!(self.op_link[op.index()].prev, DETACHED | ERASED)
    }

    /// Whether the op was erased.
    pub fn is_erased(&self, op: OpId) -> bool {
        self.op_link[op.index()].prev == ERASED
    }

    /// Remove an op from its region and drop its uses, and those of every op nested in its
    /// regions, which end up empty. Its results (and the values defined inside it) must have no
    /// uses left. Ids stay valid; erasing an erased op does nothing.
    pub fn erase(&mut self, op: OpId) {
        if self.is_erased(op) {
            return;
        }
        self.unlink(op);
        let mut work = vec![op];
        let mut erased = Vec::new();
        while let Some(o) = work.pop() {
            for u in self.op_shape[o.index()].operands.range() {
                self.unlink_use(u as u32);
            }
            for i in self.op_shape[o.index()].regions.range() {
                let r = self.region_ids[i];
                while let Some(inner) = opt(self.regions[r.index()].first) {
                    self.unlink(OpId(inner));
                    work.push(OpId(inner));
                }
            }
            self.op_link[o.index()] = Link {
                prev: ERASED,
                next: NONE,
            };
            erased.push(o);
        }
        debug_assert!(
            !self.uses_built
                || erased
                    .iter()
                    .all(|&o| self.results(o).all(|v| !self.has_uses(v))),
            "erase: a value defined by the erased ops is still used"
        );
    }

    // Uses

    /// Build the use lists, if they aren't built yet. Each value's list starts in op id order.
    pub fn build_uses(&mut self) {
        if self.uses_built {
            return;
        }
        self.uses_built = true;
        self.first_use.clear();
        self.first_use.resize(self.value_ty.len(), NONE);
        self.use_next.clear();
        self.use_next.resize(self.operands.len(), DETACHED);
        // Backwards, so that putting each use at the head leaves the lists in order.
        for o in (0..self.op_shape.len()).rev() {
            if self.op_link[o].prev == ERASED {
                continue;
            }
            for u in self.op_shape[o].operands.range().rev() {
                self.link_use(u as u32);
            }
        }
    }

    /// Whether the use lists are built; see [`Body::build_uses`].
    pub fn has_use_lists(&self) -> bool {
        self.uses_built
    }

    fn need_uses(&self) {
        assert!(
            self.uses_built,
            "the use lists aren't built: call Body::build_uses"
        );
    }

    /// Add operand slot `u` to its value's use list, if it names a value.
    fn link_use(&mut self, u: u32) {
        let OperandKind::Value(v) = self.operands[u as usize].get() else {
            return;
        };
        // A body parsed only to find syntax errors has placeholder operands that may name no
        // value; they stay out of every list.
        let Some(head) = self.first_use.get_mut(v.index()) else {
            return;
        };
        self.use_next[u as usize] = std::mem::replace(head, u);
    }

    /// Take operand slot `u` out of its value's use list, if it is in one: a walk from the
    /// list's head to `u`.
    fn unlink_use(&mut self, u: u32) {
        if !self.uses_built {
            return;
        }
        let next = self.use_next[u as usize];
        if next == DETACHED {
            return;
        }
        let OperandKind::Value(v) = self.operands[u as usize].get() else {
            unreachable!("a hole in a use list")
        };
        let head = self.first_use[v.index()];
        if head == u {
            self.first_use[v.index()] = next;
        } else {
            let mut p = head;
            while self.use_next[p as usize] != u {
                p = self.use_next[p as usize];
            }
            self.use_next[p as usize] = next;
        }
        self.use_next[u as usize] = DETACHED;
    }

    /// The uses of a value, in no particular order. Needs the use lists built.
    pub fn uses(&self, value: ValueId) -> Uses<'_> {
        self.need_uses();
        Uses {
            next: &self.use_next,
            cur: self.first_use[value.index()],
        }
    }

    /// Whether a value has uses. Needs the use lists built.
    pub fn has_uses(&self, value: ValueId) -> bool {
        self.need_uses();
        self.first_use[value.index()] != NONE
    }

    /// The op a use belongs to, and which of its operands it is.
    pub fn user(&self, u: UseId) -> (OpId, usize) {
        // Operand runs are allocated in op id order, so the owner is the last op whose run
        // starts at or before `u`.
        let i = self.op_shape.partition_point(|s| s.operands.start <= u.0) - 1;
        (
            OpId(i as u32),
            (u.0 - self.op_shape[i].operands.start) as usize,
        )
    }

    /// The use that is operand `i` of `op`.
    pub fn operand_use(&self, op: OpId, i: usize) -> UseId {
        let span = self.op_shape[op.index()].operands;
        assert!(
            i < span.len as usize,
            "operand {i} of an op with {}",
            span.len
        );
        UseId(span.start + i as u32)
    }

    /// Make operand `i` of `op` refer to `new`, keeping use lists exact.
    pub fn set_operand(&mut self, op: OpId, i: usize, new: Operand) {
        assert!(!self.is_erased(op), "set_operand on an erased op");
        let u = self.operand_use(op, i).0;
        self.unlink_use(u);
        self.operands[u as usize] = new;
        if self.uses_built {
            self.link_use(u);
        }
    }

    /// Make every use of `old` a use of `new`. Needs the use lists built.
    pub fn replace_all_uses(&mut self, old: ValueId, new: ValueId) {
        self.need_uses();
        if old == new {
            return;
        }
        let first = self.first_use[old.index()];
        let mut last = NONE;
        let mut u = first;
        while let Some(x) = opt(u) {
            self.operands[x as usize] = Operand::value(new);
            last = x;
            u = self.use_next[x as usize];
        }
        let Some(last) = opt(last) else { return };
        // Put `old`'s list in front of `new`'s.
        let head = std::mem::replace(&mut self.first_use[new.index()], first);
        self.use_next[last as usize] = head;
        self.first_use[old.index()] = NONE;
    }

    /// Check the body's internal links, for tests and debugging: every region's op list is
    /// well formed and holds exactly the ops whose parent it is, ops take their operand runs in
    /// id order, and (once built) every use list holds exactly the value operands of the ops
    /// that aren't erased.
    pub fn check_invariants(&self) -> Result<(), String> {
        let n_ops = self.op_kind.len();
        for (name, len) in [
            ("op_shape", self.op_shape.len()),
            ("op_link", self.op_link.len()),
            ("op_cold", self.op_cold.len()),
        ] {
            if len != n_ops {
                return Err(format!("{name} has {len} entries for {n_ops} ops"));
            }
        }
        if self.value_info.len() != self.value_ty.len() {
            return Err("value columns differ in length".into());
        }
        let (want_values, want_uses) = if self.uses_built {
            (self.value_ty.len(), self.operands.len())
        } else {
            (0, 0)
        };
        if self.first_use.len() != want_values || self.use_next.len() != want_uses {
            return Err("the use list columns have the wrong length".into());
        }
        let mut end = 0;
        for (i, s) in self.op_shape.iter().enumerate() {
            if s.operands.start < end {
                return Err(format!("op {i}'s operands start before op {}'s end", i - 1));
            }
            end = s.operands.start + s.operands.len;
        }
        // Region lists.
        let mut listed = vec![false; n_ops];
        for (r, data) in self.regions.iter().enumerate() {
            let mut prev = NONE;
            let mut cur = data.first;
            while let Some(op) = opt(cur) {
                let o = op as usize;
                if o >= n_ops || listed[o] {
                    return Err(format!(
                        "region {r}'s list revisits or leaves the ops at {op}"
                    ));
                }
                listed[o] = true;
                let link = self.op_link[o];
                if link.prev != prev {
                    return Err(format!("op {op}'s prev link is wrong"));
                }
                if self.op_cold[o].parent().index() != r {
                    return Err(format!(
                        "op {op} is listed in region {r} but has another parent"
                    ));
                }
                prev = op;
                cur = link.next;
            }
            if data.last != prev {
                return Err(format!("region {r}'s last op is wrong"));
            }
        }
        for (o, &l) in listed.iter().enumerate() {
            if l != self.is_linked(OpId(o as u32)) {
                return Err(format!("op {o} is linked but not listed, or the reverse"));
            }
        }
        if !self.uses_built {
            return Ok(());
        }
        // Use lists.
        let mut seen = vec![false; self.operands.len()];
        for v in 0..self.first_use.len() {
            let mut cur = self.first_use[v];
            while let Some(u) = opt(cur) {
                let ui = u as usize;
                if ui >= seen.len() || seen[ui] {
                    return Err(format!(
                        "value {v}'s use list revisits or leaves the uses at {u}"
                    ));
                }
                seen[ui] = true;
                if self.operands[ui].get() != OperandKind::Value(ValueId(v as u32)) {
                    return Err(format!("use {u} is in value {v}'s list but names another"));
                }
                let (op, _) = self.user(UseId(u));
                if self.is_erased(op) {
                    return Err(format!("use {u} belongs to erased op {}", op.0));
                }
                cur = self.use_next[ui];
            }
        }
        for (o, s) in self.op_shape.iter().enumerate() {
            let erased = self.is_erased(OpId(o as u32));
            for u in s.operands.range() {
                let named = matches!(
                    self.operands[u].get(),
                    OperandKind::Value(v) if v.index() < self.first_use.len()
                );
                if seen[u] != (named && !erased) {
                    return Err(format!("use {u} of op {o} is listed wrongly"));
                }
                if !seen[u] && self.use_next[u] != DETACHED {
                    return Err(format!("use {u} of op {o} is in no list but has links"));
                }
            }
        }
        Ok(())
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
        self.op_cold[op.index()].loc()
    }

    pub fn parent(&self, op: OpId) -> RegionId {
        self.op_cold[op.index()].parent()
    }

    pub fn next(&self, op: OpId) -> Option<OpId> {
        opt(self.op_link[op.index()].next).map(OpId)
    }

    pub fn prev(&self, op: OpId) -> Option<OpId> {
        match self.op_link[op.index()].prev {
            DETACHED | ERASED => None,
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

    /// A block's label; `None` for other regions.
    pub fn label(&self, region: RegionId) -> Option<StrId> {
        opt(self.regions[region.index()].label).map(StrId)
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
        self.value_info[value.index()].def.unpack()
    }

    /// Rename a value. The old name's text stays in the body, unused, so a builder names each
    /// value once: values are made with empty names and named afterwards.
    pub fn set_name(&mut self, value: ValueId, name: &str) {
        self.value_info[value.index()].name = self.push_text(name);
    }

    /// Replace a value's facts. Like [`Body::set_name`], the old list stays in the pool.
    pub fn set_facts(&mut self, value: ValueId, facts: impl IntoIterator<Item = TrustedFact>) {
        self.value_info[value.index()].facts = push_span(&mut self.facts, facts);
    }

    /// How many regions the body has; region ids are below this.
    pub fn num_regions(&self) -> usize {
        self.regions.len()
    }

    /// How many holes the body has; hole ids are below this.
    pub fn num_holes(&self) -> usize {
        self.holes.len()
    }
}

/// The uses of a value. See [`Body::uses`].
pub struct Uses<'a> {
    next: &'a [u32],
    cur: u32,
}

impl Iterator for Uses<'_> {
    type Item = UseId;

    fn next(&mut self) -> Option<UseId> {
        let u = opt(self.cur)?;
        self.cur = self.next[u as usize];
        Some(UseId(u))
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

    fn uses_of(b: &Body, v: ValueId) -> Vec<(OpId, usize)> {
        let mut us: Vec<_> = b.uses(v).map(|u| b.user(u)).collect();
        us.sort();
        us
    }

    fn value(b: &Body, op: OpId) -> ValueId {
        b.results(op).next().unwrap()
    }

    #[test]
    fn uses_follow_edits() {
        let mut b = Body::new();
        let r = b.entry();
        b.set_params(r, [val("x"), val("y")]);
        let mut ps = b.params(r);
        let (x, y) = (ps.next().unwrap(), ps.next().unwrap());
        let (ox, oy) = (Operand::value(x), Operand::value(y));
        let add = b.append_op(r, OpKind::Copy, [ox], [val("a")], [], None);
        let ret = b.append_op(
            r,
            OpKind::Ret,
            [Operand::value(value(&b, add))],
            [],
            [],
            None,
        );
        assert!(!b.has_use_lists());
        b.check_invariants().unwrap();
        b.build_uses();
        assert_eq!(uses_of(&b, x), [(add, 0)]);
        // Insert on both sides.
        let c = b.insert_before(add, OpKind::Copy, [ox], [val("c")], [], None);
        let d = b.insert_after(add, OpKind::Copy, [oy], [val("d")], [], None);
        let e = b.insert_before(c, OpKind::Copy, [ox], [val("e")], [], None);
        assert_eq!(b.ops(r).collect::<Vec<_>>(), [e, c, add, d, ret]);
        assert_eq!(uses_of(&b, x), [(add, 0), (c, 0), (e, 0)]);
        assert_eq!(uses_of(&b, y), [(d, 0)]);
        b.check_invariants().unwrap();
        // Rewrite one operand, then all uses of a value.
        b.set_operand(c, 0, oy);
        assert_eq!(uses_of(&b, x), [(add, 0), (e, 0)]);
        assert_eq!(uses_of(&b, y), [(c, 0), (d, 0)]);
        b.replace_all_uses(x, y);
        assert!(!b.has_uses(x));
        assert_eq!(uses_of(&b, y), [(add, 0), (c, 0), (d, 0), (e, 0)]);
        assert_eq!(b.operands(e), [oy]);
        b.check_invariants().unwrap();
        // A hole is in no list; setting it back to a value relinks it.
        let h = b.add_hole("h", Ty::Int(32));
        b.set_operand(d, 0, h);
        assert_eq!(uses_of(&b, y), [(add, 0), (c, 0), (e, 0)]);
        b.set_operand(d, 0, ox);
        assert_eq!(uses_of(&b, x), [(d, 0)]);
        // Erasing drops uses.
        b.erase(e);
        b.erase(e);
        assert!(b.is_erased(e) && !b.is_linked(e));
        assert_eq!(uses_of(&b, y), [(add, 0), (c, 0)]);
        assert_eq!(b.ops(r).collect::<Vec<_>>(), [c, add, d, ret]);
        b.check_invariants().unwrap();
    }

    #[test]
    fn erase_empties_nested_regions() {
        let mut b = Body::new();
        let r = b.entry();
        b.set_params(r, [val("x")]);
        let x = b.params(r).next().unwrap();
        let ox = Operand::value(x);
        b.build_uses();
        let lp = b.append_op(
            r,
            OpKind::Loop { progress: false },
            [ox],
            [],
            [vec![val("i")]],
            None,
        );
        let body = b.regions(lp)[0];
        let i = b.params(body).next().unwrap();
        let inner = b.append_op(body, OpKind::Copy, [ox], [val("a")], [], None);
        let a = value(&b, inner);
        b.append_op(body, OpKind::Continue, [Operand::value(a)], [], [], None);
        b.append_op(
            body,
            OpKind::Copy,
            [Operand::value(i)],
            [val("unused")],
            [],
            None,
        );
        assert_eq!(uses_of(&b, x), [(lp, 0), (inner, 0)]);
        b.check_invariants().unwrap();
        b.erase(lp);
        assert!(!b.has_uses(x) && !b.has_uses(a) && !b.has_uses(i));
        assert!(b.is_empty(body) && b.is_empty(r));
        assert!(b.is_erased(inner));
        b.check_invariants().unwrap();
    }

    /// Random edits, checked after each against use lists computed from scratch.
    #[test]
    fn random_edits_keep_use_lists_exact() {
        let mut seed = 0x2545_f491_4f6c_dd1du64;
        let mut rand = move |n: usize| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed % n as u64) as usize
        };
        for _ in 0..40 {
            let mut b = Body::new();
            let r = b.entry();
            b.set_params(r, [val("p"), val("q")]);
            let mut values: Vec<ValueId> = b.params(r).collect();
            // Build the lists at the start, or after some edits.
            let build_at = rand(3) * 30;
            for step in 0..150 {
                if step == build_at {
                    b.build_uses();
                }
                let live: Vec<OpId> = (0..b.num_ops() as u32)
                    .map(OpId)
                    .filter(|&o| b.is_linked(o))
                    .collect();
                let n_operands = rand(4);
                let operands: Vec<Operand> = (0..n_operands)
                    .map(|_| {
                        if rand(10) == 0 {
                            b.add_hole("h", Ty::Int(32))
                        } else {
                            Operand::value(values[rand(values.len())])
                        }
                    })
                    .collect();
                let name = format!("v{step}");
                let spec = || vec![val(&name)];
                match rand(7) {
                    0 | 1 => {
                        // Sometimes with a region holding an op of its own.
                        let regions = if rand(4) == 0 { vec![vec![]] } else { vec![] };
                        let op = b.append_op(r, OpKind::Copy, operands, spec(), regions, None);
                        if let Some(&inner) = b.regions(op).first() {
                            let o = Operand::value(values[rand(values.len())]);
                            b.append_op(inner, OpKind::Copy, [o], [], [], None);
                        }
                        values.extend(b.results(op));
                    }
                    2 if !live.is_empty() => {
                        let at = live[rand(live.len())];
                        let op = if rand(2) == 0 {
                            b.insert_before(at, OpKind::Copy, operands, spec(), [], None)
                        } else {
                            b.insert_after(at, OpKind::Copy, operands, spec(), [], None)
                        };
                        values.extend(b.results(op));
                    }
                    3 if !live.is_empty() => {
                        let op = live[rand(live.len())];
                        let k = b.operands(op).len();
                        if k > 0 {
                            b.set_operand(
                                op,
                                rand(k),
                                operands
                                    .first()
                                    .copied()
                                    .unwrap_or(Operand::value(values[0])),
                            );
                        }
                    }
                    4 if b.has_use_lists() => {
                        let (old, new) = (values[rand(values.len())], values[rand(values.len())]);
                        b.replace_all_uses(old, new);
                    }
                    5 if !live.is_empty() && b.has_use_lists() => {
                        // Erase an op after redirecting the uses of what it defines.
                        let op = live[rand(live.len())];
                        let mut defined: Vec<ValueId> = b.results(op).collect();
                        for &rg in b.regions(op) {
                            for inner in b.ops(rg) {
                                defined.extend(b.results(inner));
                            }
                        }
                        for v in &defined {
                            b.replace_all_uses(*v, values[0]);
                        }
                        b.erase(op);
                        values.retain(|v| !defined.contains(v));
                    }
                    _ if !live.is_empty() => b.unlink(live[rand(live.len())]),
                    _ => {}
                }
                b.check_invariants().unwrap();
                if !b.has_use_lists() {
                    continue;
                }
                // Compare with use lists computed from scratch, and with lists built afresh.
                let mut fresh = b.clone();
                fresh.uses_built = false;
                fresh.first_use.clear();
                fresh.use_next.clear();
                fresh.build_uses();
                fresh.check_invariants().unwrap();
                for v in 0..b.num_values() as u32 {
                    let v = ValueId(v);
                    let mut want = Vec::new();
                    for o in 0..b.num_ops() as u32 {
                        let o = OpId(o);
                        if b.is_erased(o) {
                            continue;
                        }
                        for (i, x) in b.operands(o).iter().enumerate() {
                            if x.get() == OperandKind::Value(v) {
                                want.push((o, i));
                            }
                        }
                    }
                    assert_eq!(uses_of(&b, v), want, "value {v:?} after step {step}");
                    // Built lists are in op order.
                    let built: Vec<_> = fresh.uses(v).map(|u| fresh.user(u)).collect();
                    assert_eq!(built, want);
                }
            }
        }
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
        let label = b.add_str("loop");
        let s = b.add_succ(Succ { label, nargs: 2 });
        let key = b.add_small_int(-1);
        let cases = b.add_cases([Case {
            key,
            succ: Succ { label, nargs: 0 },
        }]);
        assert_eq!(b.succ(s), Succ { label, nargs: 2 });
        assert_eq!(b.cases(cases).len(), 1);
        assert_eq!(b.int(b.cases(cases)[0].key), Int::Small(-1));
        assert!(b.cases(CasesId::EMPTY).is_empty());
        assert_eq!(std::mem::size_of::<Operand>(), 4);
        assert_eq!(std::mem::size_of::<OpKind>(), 16);
        assert_eq!(std::mem::size_of::<Ty>(), 8);
    }

    /// A `cf.blocks` op gets its blocks after they are made, one by one, with ops nested in
    /// the earlier ones in between.
    #[test]
    fn blocks_are_attached_after_they_are_filled() {
        let mut b = Body::new();
        let r = b.entry();
        let op = b.append_op(r, OpKind::Blocks { progress: false }, [], [], [], None);
        let (l0, l1) = (b.add_str("entry"), b.add_str("next"));
        let first = b.new_block(op, l0, []);
        let dest = b.add_succ(Succ {
            label: l1,
            nargs: 1,
        });
        let inner = b.append_op(first, OpKind::Copy, [], [val("c")], [], None);
        let c = Operand::value(value(&b, inner));
        b.append_op(first, OpKind::Br { dest }, [c], [], [], None);
        let second = b.new_block(op, l1, [val("x")]);
        b.append_op(second, OpKind::Yield, [], [], [], None);
        b.set_regions(op, &[first, second]);
        assert_eq!(b.regions(op), [first, second]);
        assert_eq!(b.label(second), Some(l1));
        assert_eq!(b.label(r), None);
        assert_eq!(b.parent_op(second), Some(op));
        b.build_uses();
        b.check_invariants().unwrap();
        b.erase(op);
        assert!(b.is_erased(inner) && b.is_empty(first));
        b.check_invariants().unwrap();
    }
}
