//! A function's code, stored data-oriented: flat arrays per function, with ops, regions, and
//! values referring to each other by 32-bit index. A region's ops form an index-based doubly
//! linked list, so inserting and removing ops never moves other ops and op ids stay stable.

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

fn push_span<T: Clone>(pool: &mut Vec<T>, items: impl IntoIterator<Item = T>) -> Span {
    let start = pool.len();
    pool.extend(items);
    Span {
        start: index32(start),
        len: index32(pool.len() - start),
    }
}

fn index32(n: usize) -> u32 {
    u32::try_from(n).expect("a function body holds at most 2^32 entries of each kind")
}

/// An operand: a value, or a hole `?name: T` standing for a value not written yet.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Operand {
    Value(ValueId),
    Hole { name: String, ty: Ty },
}

/// Where a value comes from.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ValueDef {
    Result { op: OpId, index: u32 },
    Param { region: RegionId, index: u32 },
}

/// A value to create: its name, type, and facts.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ValueSpec {
    pub name: String,
    pub ty: Ty,
    pub facts: Vec<TrustedFact>,
}

#[derive(Clone, Debug)]
struct OpData {
    kind: OpKind,
    results: Span,
    operands: Span,
    regions: Span,
    loc: Option<Loc>,
    parent: RegionId,
    prev: Option<OpId>,
    next: Option<OpId>,
    /// Whether the op is in its parent region's list.
    linked: bool,
}

#[derive(Clone, Debug)]
struct RegionData {
    params: Span,
    first: Option<OpId>,
    last: Option<OpId>,
    parent: Option<OpId>,
}

#[derive(Clone, Debug)]
struct ValueData {
    name: String,
    ty: Ty,
    facts: Span,
    def: ValueDef,
}

/// A function's code: its entry region and everything nested in it.
#[derive(Clone, Debug)]
pub struct Body {
    ops: Vec<OpData>,
    regions: Vec<RegionData>,
    values: Vec<ValueData>,
    operands: Vec<Operand>,
    op_regions: Vec<RegionId>,
    facts: Vec<TrustedFact>,
    entry: RegionId,
}

impl Body {
    /// An empty body whose entry region has these parameters (the function's parameters).
    pub fn new(params: impl IntoIterator<Item = ValueSpec>) -> Body {
        let mut body = Body {
            ops: Vec::new(),
            regions: Vec::new(),
            values: Vec::new(),
            operands: Vec::new(),
            op_regions: Vec::new(),
            facts: Vec::new(),
            entry: RegionId(0),
        };
        body.entry = body.new_region(None, params);
        body
    }

    pub fn entry(&self) -> RegionId {
        self.entry
    }

    fn new_region(
        &mut self,
        parent: Option<OpId>,
        params: impl IntoIterator<Item = ValueSpec>,
    ) -> RegionId {
        let id = RegionId(index32(self.regions.len()));
        let params = self.new_values(params, |index| ValueDef::Param { region: id, index });
        self.regions.push(RegionData {
            params,
            first: None,
            last: None,
            parent,
        });
        id
    }

    fn new_values(
        &mut self,
        specs: impl IntoIterator<Item = ValueSpec>,
        def: impl Fn(u32) -> ValueDef,
    ) -> Span {
        let start = self.values.len();
        for (i, spec) in specs.into_iter().enumerate() {
            let facts = push_span(&mut self.facts, spec.facts);
            self.values.push(ValueData {
                name: spec.name,
                ty: spec.ty,
                facts,
                def: def(index32(i)),
            });
        }
        Span {
            start: index32(start),
            len: index32(self.values.len() - start),
        }
    }

    /// Append an op to the end of `region`. `regions` gives each of the op's regions its
    /// parameters; the regions start empty.
    pub fn append_op(
        &mut self,
        region: RegionId,
        kind: OpKind,
        operands: impl IntoIterator<Item = Operand>,
        results: impl IntoIterator<Item = ValueSpec>,
        regions: impl IntoIterator<Item = Vec<ValueSpec>>,
        loc: Option<Loc>,
    ) -> OpId {
        let id = OpId(index32(self.ops.len()));
        let operands = push_span(&mut self.operands, operands);
        let results = self.new_values(results, |index| ValueDef::Result { op: id, index });
        let new_regions: Vec<RegionId> = regions
            .into_iter()
            .map(|params| self.new_region(Some(id), params))
            .collect();
        let regions = push_span(&mut self.op_regions, new_regions);
        let prev = self.regions[region.index()].last;
        self.ops.push(OpData {
            kind,
            results,
            operands,
            regions,
            loc,
            parent: region,
            prev,
            next: None,
            linked: true,
        });
        match prev {
            Some(p) => self.ops[p.index()].next = Some(id),
            None => self.regions[region.index()].first = Some(id),
        }
        self.regions[region.index()].last = Some(id);
        id
    }

    /// Remove an op from its region. Its id stays valid but no longer appears in any region.
    /// Unlinking an op that is already unlinked does nothing.
    pub fn unlink(&mut self, op: OpId) {
        let OpData {
            parent,
            prev,
            next,
            linked,
            ..
        } = self.ops[op.index()];
        if !linked {
            return;
        }
        match prev {
            Some(p) => self.ops[p.index()].next = next,
            None => self.regions[parent.index()].first = next,
        }
        match next {
            Some(n) => self.ops[n.index()].prev = prev,
            None => self.regions[parent.index()].last = prev,
        }
        let data = &mut self.ops[op.index()];
        data.prev = None;
        data.next = None;
        data.linked = false;
    }

    /// Whether the op is in a region (it hasn't been unlinked).
    pub fn is_linked(&self, op: OpId) -> bool {
        self.ops[op.index()].linked
    }

    // Ops

    pub fn kind(&self, op: OpId) -> &OpKind {
        &self.ops[op.index()].kind
    }

    pub fn results(&self, op: OpId) -> impl ExactSizeIterator<Item = ValueId> + use<> {
        self.ops[op.index()]
            .results
            .range()
            .map(|i| ValueId(i as u32))
    }

    pub fn operands(&self, op: OpId) -> &[Operand] {
        &self.operands[self.ops[op.index()].operands.range()]
    }

    pub fn regions(&self, op: OpId) -> &[RegionId] {
        &self.op_regions[self.ops[op.index()].regions.range()]
    }

    pub fn loc(&self, op: OpId) -> Option<Loc> {
        self.ops[op.index()].loc
    }

    pub fn parent(&self, op: OpId) -> RegionId {
        self.ops[op.index()].parent
    }

    pub fn next(&self, op: OpId) -> Option<OpId> {
        self.ops[op.index()].next
    }

    pub fn prev(&self, op: OpId) -> Option<OpId> {
        self.ops[op.index()].prev
    }

    // Regions

    pub fn params(&self, region: RegionId) -> impl ExactSizeIterator<Item = ValueId> + use<> {
        self.regions[region.index()]
            .params
            .range()
            .map(|i| ValueId(i as u32))
    }

    /// The ops of a region, in order.
    pub fn ops(&self, region: RegionId) -> Ops<'_> {
        Ops {
            body: self,
            next: self.regions[region.index()].first,
        }
    }

    pub fn is_empty(&self, region: RegionId) -> bool {
        self.regions[region.index()].first.is_none()
    }

    /// The op whose region this is; `None` for the entry region.
    pub fn parent_op(&self, region: RegionId) -> Option<OpId> {
        self.regions[region.index()].parent
    }

    // Values

    pub fn name(&self, value: ValueId) -> &str {
        &self.values[value.index()].name
    }

    pub fn ty(&self, value: ValueId) -> Ty {
        self.values[value.index()].ty
    }

    pub fn facts(&self, value: ValueId) -> &[TrustedFact] {
        &self.facts[self.values[value.index()].facts.range()]
    }

    pub fn def(&self, value: ValueId) -> ValueDef {
        self.values[value.index()].def
    }
}

/// The ops of a region, in order.
pub struct Ops<'a> {
    body: &'a Body,
    next: Option<OpId>,
}

impl Iterator for Ops<'_> {
    type Item = OpId;

    fn next(&mut self) -> Option<OpId> {
        let op = self.next?;
        self.next = self.body.next(op);
        Some(op)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn val(name: &str) -> ValueSpec {
        ValueSpec {
            name: name.into(),
            ty: Ty::Int(32),
            facts: vec![],
        }
    }

    #[test]
    fn ops_stay_in_order_and_unlink() {
        let mut b = Body::new([val("x")]);
        let r = b.entry();
        let x = b.params(r).next().unwrap();
        let a = b.append_op(r, OpKind::Copy, [Operand::Value(x)], [val("a")], [], None);
        let c = b.append_op(r, OpKind::Copy, [Operand::Value(x)], [val("c")], [], None);
        let d = b.append_op(r, OpKind::Ret, [], [], [], None);
        assert_eq!(b.ops(r).collect::<Vec<_>>(), [a, c, d]);
        b.unlink(c);
        assert_eq!(b.ops(r).collect::<Vec<_>>(), [a, d]);
        b.unlink(c);
        assert_eq!(b.ops(r).collect::<Vec<_>>(), [a, d]);
        assert!(!b.is_linked(c));
        b.unlink(a);
        b.unlink(d);
        assert!(b.is_empty(r));
        let a_val = b.results(a).next().unwrap();
        assert_eq!(b.name(a_val), "a");
        assert_eq!(b.def(a_val), ValueDef::Result { op: a, index: 0 });
    }
}
