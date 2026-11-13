//! Promotion of stack slots to values (mem2reg). EXPERIMENTAL: no Lean theorem backs it yet.
//!
//! ```text
//! %s: ptr = mem.stack.of i64, align 8         // deleted
//! mem.store i64 %zero, %s, align 8            // deleted: %s is now %zero
//! cf.loop {                                   // cf.loop iter(%s.1 = %zero) {
//!   %v: i64 = mem.load %s, align 8            // deleted: uses read %s.1
//!   %w: i64 = int.add.nsw %v, %one
//!   mem.store i64 %w, %s, align 8             // deleted: %s is now %w
//!   cf.continue                               // cf.continue %w
//! }
//! ```
//!
//! A slot is promoted when it is a `mem.stack` or `mem.stack.of` whose pointer is used only as
//! the address of `mem.load`s and `mem.store`s, directly or through `ptr.offset`s by constants
//! (a C struct's fields, after lowering): each offset is a *field*, accessed with one type `T`
//! that comes back from memory unchanged and whose unwritten bytes read as `poison` (`iN` of
//! whole bytes, `ptr`, `f32`, `f64`; not `bN`, whose loads keep `poison` bytes as they are), and
//! no two fields' bytes overlap. Each field's loads then read the value last stored to it, or
//! `poison` before any store, since nothing else reaches its bytes; so the pass deletes the
//! loads and stores, and gives each load's uses the value it would read. Each field is its own
//! variable from then on (scalar replacement of aggregates and promotion in one step). The
//! `ptr.offset`s are left for dead code elimination.
//!
//! The allocation itself stays, unused: deleting it would renumber the allocations made after
//! it, and the semantics' events name allocations by number (`ptr #3`), so that is a separate
//! step with its own assumption ([`super::stackdce`]). Keeping it, the pass only drops accesses
//! to memory nothing else can reach.
//!
//! FIR's control flow is structured, so a value reaches a later op only through the regions'
//! own channels. For each `cf.if`, `cf.loop`, and `cf.blocks` with a store to a promoted slot
//! inside it (the slot made outside it), the slot's value is threaded through it where it is
//! *live* (some path from there reads the slot before storing to it): a result for the op if the
//! slot is live after it (and an operand for each `cf.yield`, `cf.break`, or branch that leaves
//! to it), a loop parameter if it is live at the top of the body (fed by the loop's operands and
//! each `cf.continue`), and a parameter of each block after a `cf.blocks`'s entry where it is
//! live. Slots only read inside an op need nothing: their value is visible there. Liveness is a
//! backward dataflow over the function's ops, whose edges are the structured control flow's
//! (falling through, entering regions, `cf.yield`, `cf.break`, `cf.continue`, branches); loads
//! read their slot and stores write it. Without the pruning, C's block-scoped variables (which
//! `fai-cc` makes at the function's entry) would become state of every loop and parameters of
//! every block around them, and the moves and spills that costs can outweigh the loads saved.
//!
//! Skipped: functions with an op with regions other than those three (`cf.try`, LFIR code) or a
//! call that names a handler (`func.invoke`), whose unwinding edges would need the values too;
//! slots stored in a `cf.blocks` whose entry block is a branch target (an entry block has no
//! parameters); stores of holes. A load whose result has facts becomes a `copy`, which keeps
//! them.
//!
//! **What correctness rests on** (not proved): a slot's bytes change only through its pointer,
//! and only its own loads and stores use that pointer, so no other op can read or write them;
//! an access that is out of bounds or misaligned is UB in the source, so giving it a value
//! refines it. The differential tests (`tests/mem2reg.rs`, and `tests/opt.rs` with
//! `FIR_PASSES`) check the output against the interpreter run by run.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::body::{
    Body, OpId, Operand, OperandKind, RegionId, StrId, Succ, ValueDef, ValueId, ValueSpec,
};
use crate::ir::{OpKind, SpaceCfg, Ty};

use super::{Remarks, at};

/// Whether a slot accessed only as `t` can be promoted: `t`'s values come back from memory
/// unchanged (`fwd::exact`), and unwritten bytes read as `poison` of `t`.
pub fn promotable(t: Ty) -> bool {
    match t {
        Ty::Int(w) => w % 8 == 0 && w > 0,
        Ty::Ptr | Ty::Float(_) => true,
        Ty::Byte(_) | Ty::Slice | Ty::Agg(_) | Ty::VaList => false,
    }
}

/// A field of a slot to promote: a variable from now on.
struct Slot {
    alloc: OpId,
    ty: Ty,
    /// The base of the names of the values threaded for it.
    name: String,
    /// The `poison` it reads as before any store, once made.
    poison: Option<ValueId>,
    /// The next suffix to try for a fresh name.
    next_name: usize,
}

/// What a slot holds at a point: `poison` (nothing stored yet), or a value.
#[derive(Clone, Copy)]
enum Cur {
    Undef,
    Val(ValueId),
}

struct Promoter<'b> {
    body: &'b mut Body,
    slots: Vec<Slot>,
    /// The slot each promoted pointer is, by value id.
    slot_of: Vec<Option<u32>>,
    /// What each structured op threads, by its (original) op id.
    plans: HashMap<OpId, Plan>,
    /// The enclosing loops' parameter and result slots, innermost last.
    loops: Vec<(Vec<u32>, Vec<u32>)>,
    /// The enclosing `cf.blocks`' blocks: each one's label and parameter slots.
    blocks: Vec<Vec<(Option<StrId>, Vec<u32>)>>,
    names: HashSet<String>,
}

/// What a structured op threads: the slots stored in it (`stored`), those of them live after
/// it (its new results), and, for each of its regions, those live at its start (the region's new
/// parameters: a loop's body, the blocks after a `cf.blocks`'s entry; none for the others).
#[derive(Clone, Debug, Default)]
struct Plan {
    stored: Vec<u32>,
    results: Vec<u32>,
    params: Vec<Vec<u32>>,
}

/// Promote every slot that qualifies, leaving its allocation unused (but for `ptr.offset`s).
/// Returns how many slots were promoted (slots without accesses don't count).
pub fn run(body: &mut Body, remarks: &mut Remarks, space: &SpaceCfg) -> u32 {
    body.build_uses();
    let mut ops = Vec::new();
    super::walk(body, &mut ops);
    for &op in &ops {
        let k = body.kind(op);
        let structured = matches!(k, OpKind::If | OpKind::Loop { .. } | OpKind::Blocks { .. });
        if (!structured && !body.regions(op).is_empty())
            || matches!(k, OpKind::Invoke { .. } | OpKind::InvokeIndirect { .. })
        {
            return 0;
        }
    }
    let targeted = targeted_entries(body, &ops);
    let mut slots = Vec::new();
    let mut slot_of = vec![None; body.num_values()];
    let mut threaded: Vec<Vec<u32>> = vec![Vec::new(); body.num_ops()];
    let mut promoted = Vec::new();
    for &op in &ops {
        if !matches!(
            body.kind(op),
            OpKind::MemStack { .. } | OpKind::MemStackOf { .. }
        ) {
            continue;
        }
        let ptr = body.results(op).next().expect("verified");
        // A slot without accesses has nothing to promote (and is what promotion leaves).
        let Some(fields) = fields(body, space, ptr).filter(|f| !f.is_empty()) else {
            continue;
        };
        // The structured ops between each field's stores and the slot's region.
        let home = body.parent(op);
        let mut through = Vec::new();
        for f in &fields {
            let mut ops = Vec::new();
            for &s in &f.stores {
                let mut r = body.parent(s);
                while r != home {
                    let o = body
                        .parent_op(r)
                        .expect("the slot's region encloses its uses");
                    ops.push(o);
                    r = body.parent(o);
                }
            }
            ops.sort_unstable();
            ops.dedup();
            through.push(ops);
        }
        if through.iter().flatten().any(|o| targeted.contains(o)) {
            continue;
        }
        let name = body.name(ptr);
        let name = name.strip_suffix(".addr").unwrap_or(name).to_owned();
        let whole = fields.len() == 1 && fields[0].offset == 0;
        let (mut loads, mut stores) = (0, 0);
        for (f, ops) in fields.iter().zip(through) {
            let k = slots.len() as u32;
            for o in ops {
                threaded[o.index()].push(k);
            }
            for &a in &f.addrs {
                slot_of[a.index()] = Some(k);
            }
            loads += f.loads;
            stores += f.stores.len();
            slots.push(Slot {
                alloc: op,
                ty: f.ty,
                // `%s.at8`, or `%s.atm8` for offset -8 (`-` can't be in a name).
                name: if whole {
                    name.clone()
                } else if f.offset < 0 {
                    format!("{name}.atm{}", f.offset.unsigned_abs())
                } else {
                    format!("{name}.at{}", f.offset)
                },
                poison: None,
                next_name: 1,
            });
        }
        promoted.push((op, ptr, fields.len(), loads, stores));
    }
    if slots.is_empty() {
        return 0;
    }
    let plans = plan(body, &ops, &slot_of, slots.len(), threaded);
    let names = (0..body.num_values())
        .map(|v| body.name(ValueId::from_raw(v as u32)).to_owned())
        .collect();
    let mut p = Promoter {
        body,
        slots,
        slot_of,
        plans,
        loops: Vec::new(),
        blocks: Vec::new(),
        names,
    };
    let entry = p.body.entry();
    let mut env = vec![Cur::Undef; p.slots.len()];
    p.region(entry, &mut env, &[]);
    for &(alloc, ptr, n, loads, stores) in &promoted {
        let loc = p.body.loc(alloc);
        remarks.add("mem2reg", (alloc, loc), None, || {
            let fields = if n == 1 {
                String::new()
            } else {
                format!("{n} fields, ")
            };
            format!(
                "promoted %{} {} to values ({fields}{loads} loads, {stores} stores)",
                p.body.name(ptr),
                at(loc),
            )
        });
    }
    promoted.len() as u32
}

/// The accesses of a slot at one offset, all of one type.
struct Field {
    offset: i128,
    ty: Ty,
    loads: usize,
    stores: Vec<OpId>,
    /// The pointers they access it through: the slot's, or `ptr.offset`s of it.
    addrs: Vec<ValueId>,
}

/// The fields of the slot `ptr`, by offset: every use of its pointer is the address of a load
/// or store, directly or through `ptr.offset`s by constants. `None` if some other use reaches
/// it, if one offset is accessed with two types, or if two fields' bytes overlap.
fn fields(body: &Body, space: &SpaceCfg, ptr: ValueId) -> Option<Vec<Field>> {
    let mut by_offset: BTreeMap<i128, Field> = BTreeMap::new();
    let mut work = vec![(ptr, 0i128)];
    while let Some((p, offset)) = work.pop() {
        for u in body.uses(p) {
            let (op, i) = body.user(u);
            let (t, store) = match (body.kind(op), i) {
                (OpKind::Load { .. }, 0) => (body.ty(body.results(op).next()?), false),
                (OpKind::Store { ty, .. }, 1)
                    if matches!(body.operands(op)[0].get(), OperandKind::Value(_)) =>
                {
                    (ty, true)
                }
                (OpKind::PtrOffset { .. }, 0) => {
                    let c = const_of(body, body.operands(op)[1])?;
                    work.push((body.results(op).next()?, offset.checked_add(c)?));
                    continue;
                }
                _ => return None,
            };
            if !promotable(t) {
                return None;
            }
            let f = by_offset.entry(offset).or_insert(Field {
                offset,
                ty: t,
                loads: 0,
                stores: Vec::new(),
                addrs: Vec::new(),
            });
            if f.ty != t {
                return None;
            }
            if store {
                f.stores.push(op);
            } else {
                f.loads += 1;
            }
            if !f.addrs.contains(&p) {
                f.addrs.push(p);
            }
        }
    }
    let mut end = i128::MIN;
    for f in by_offset.values() {
        if f.offset < end {
            return None;
        }
        end = f.offset + i128::from(size(space, f.ty));
    }
    Some(by_offset.into_values().collect())
}

/// The value of an `int.const` operand of at most 64 bits, signed.
fn const_of(body: &Body, o: Operand) -> Option<i128> {
    let OperandKind::Value(v) = o.get() else {
        return None;
    };
    let ValueDef::Result { op, .. } = body.def(v) else {
        return None;
    };
    let (OpKind::Const(n), Ty::Int(w @ 1..=64)) = (body.kind(op), body.ty(v)) else {
        return None;
    };
    let n = i128::try_from(body.int(n).to_bigint()).ok()? & ((1i128 << w) - 1);
    Some(if n >> (w - 1) == 1 {
        n - (1i128 << w)
    } else {
        n
    })
}

/// How many bytes a promotable type takes in memory.
fn size(space: &SpaceCfg, t: Ty) -> u32 {
    match t {
        Ty::Int(w) => w.div_ceil(8),
        Ty::Float(f) => f.width() / 8,
        Ty::Ptr => space.ptr_bits.div_ceil(8),
        _ => unreachable!("not promotable"),
    }
}

/// The `cf.blocks` ops whose entry block some branch targets.
fn targeted_entries(body: &Body, ops: &[OpId]) -> HashSet<OpId> {
    let mut out = HashSet::new();
    for &op in ops {
        let succs = targets(body, body.kind(op));
        if succs.is_empty() {
            continue;
        }
        let blocks = enclosing(body, op, |k| matches!(k, OpKind::Blocks { .. }));
        let entry = body.regions(blocks)[0];
        if succs
            .iter()
            .any(|s| same_label(body, body.label(entry), s.label))
        {
            out.insert(blocks);
        }
    }
    out
}

/// The nearest loop or `cf.blocks` (by `want`) around `op`.
fn enclosing(body: &Body, op: OpId, want: fn(OpKind) -> bool) -> OpId {
    let mut r = body.parent(op);
    loop {
        let o = body.parent_op(r).expect("verified: the op is inside one");
        if want(body.kind(o)) {
            return o;
        }
        r = body.parent(o);
    }
}

/// Liveness of the candidate slots: for each op (by its index in `ops`, program order), the
/// slots live just before it, as bits.
struct Liveness {
    words: usize,
    /// Each op's index in `ops`, by op id.
    index: Vec<u32>,
    live: Vec<u64>,
}

/// Where control goes when no op of a region is left: past the region's op, for a `cf.if`
/// region that ends without `cf.yield`. `None` is leaving the function.
const EXIT: u32 = u32::MAX;

impl Liveness {
    fn new(body: &Body, ops: &[OpId], slot_of: &[Option<u32>], nslots: usize) -> Liveness {
        let words = nslots.div_ceil(64);
        let mut index = vec![EXIT; body.num_ops()];
        for (i, &op) in ops.iter().enumerate() {
            index[op.index()] = i as u32;
        }
        let mut lv = Liveness {
            words,
            index,
            live: vec![0; ops.len() * words],
        };
        // Each op's successors, and the slot it reads (`true`) or writes.
        let slot = |o: crate::body::Operand| match o.get() {
            OperandKind::Value(v) => slot_of.get(v.index()).copied().flatten(),
            OperandKind::Hole(_) => None,
        };
        let mut succs: Vec<Vec<u32>> = Vec::with_capacity(ops.len());
        let mut access: Vec<Option<(u32, bool)>> = Vec::with_capacity(ops.len());
        for &op in ops {
            succs.push(lv.succs(body, op));
            access.push(match body.kind(op) {
                OpKind::Load { .. } => slot(body.operands(op)[0]).map(|k| (k, true)),
                OpKind::Store { .. } => slot(body.operands(op)[1]).map(|k| (k, false)),
                _ => None,
            });
        }
        // Backward to a fixed point: live before = (live after - written) + read.
        let mut changed = true;
        let mut buf = vec![0u64; words];
        while changed {
            changed = false;
            for i in (0..ops.len()).rev() {
                buf.iter_mut().for_each(|w| *w = 0);
                for &s in &succs[i] {
                    if s != EXIT {
                        let s = s as usize * words;
                        for (b, l) in buf.iter_mut().zip(&lv.live[s..s + words]) {
                            *b |= l;
                        }
                    }
                }
                if let Some((k, read)) = access[i] {
                    let (w, bit) = (k as usize / 64, 1u64 << (k % 64));
                    if read {
                        buf[w] |= bit;
                    } else {
                        buf[w] &= !bit;
                    }
                }
                let me = &mut lv.live[i * words..(i + 1) * words];
                if me != &buf[..] {
                    me.copy_from_slice(&buf);
                    changed = true;
                }
            }
        }
        lv
    }

    /// The op control reaches after `op` falls through.
    fn cont(&self, body: &Body, op: OpId) -> u32 {
        match body.next(op) {
            Some(n) => self.index[n.index()],
            None => match body.parent_op(body.parent(op)) {
                // A `cf.if` region may end without `cf.yield`.
                Some(p) if body.kind(p) == OpKind::If => self.cont(body, p),
                _ => EXIT,
            },
        }
    }

    /// The first op of region `r`, or where control goes if it is empty.
    fn start(&self, body: &Body, r: RegionId, empty: u32) -> u32 {
        body.ops(r).next().map_or(empty, |o| self.index[o.index()])
    }

    fn succs(&self, body: &Body, op: OpId) -> Vec<u32> {
        let k = body.kind(op);
        let block = |b: OpId, label: StrId| {
            let r = body
                .regions(b)
                .iter()
                .copied()
                .find(|&r| same_label(body, body.label(r), label))
                .expect("verified: the target is a block");
            self.start(body, r, EXIT)
        };
        match k {
            OpKind::If => {
                let after = self.cont(body, op);
                body.regions(op)
                    .iter()
                    .map(|&r| self.start(body, r, after))
                    .collect()
            }
            OpKind::Loop { .. } | OpKind::Blocks { .. } => {
                vec![self.start(body, body.regions(op)[0], EXIT)]
            }
            OpKind::Yield => {
                let p = body.parent_op(body.parent(op)).expect("verified");
                vec![self.cont(body, p)]
            }
            OpKind::Break => {
                let l = enclosing(body, op, |k| matches!(k, OpKind::Loop { .. }));
                vec![self.cont(body, l)]
            }
            OpKind::Continue => {
                let l = enclosing(body, op, |k| matches!(k, OpKind::Loop { .. }));
                vec![self.start(body, body.regions(l)[0], EXIT)]
            }
            OpKind::Br { .. } | OpKind::CondBr { .. } | OpKind::Switch { .. } => {
                let b = enclosing(body, op, |k| matches!(k, OpKind::Blocks { .. }));
                targets(body, k)
                    .into_iter()
                    .map(|s| block(b, s.label))
                    .collect()
            }
            _ if k.is_terminator() => Vec::new(),
            _ => vec![self.cont(body, op)],
        }
    }

    fn live(&self, at: u32, k: u32) -> bool {
        at != EXIT && self.live[at as usize * self.words + k as usize / 64] & (1 << (k % 64)) != 0
    }
}

/// Whether a block's label is `label`. Labels are strings, which a body doesn't intern: a
/// branch's label and its block's are equal as text, not necessarily as ids.
fn same_label(body: &Body, block: Option<StrId>, label: StrId) -> bool {
    block.is_some_and(|b| b == label || body.str(b) == body.str(label))
}

/// A branch's targets, in operand order.
fn targets(body: &Body, k: OpKind) -> Vec<Succ> {
    match k {
        OpKind::Br { dest } => vec![body.succ(dest)],
        OpKind::CondBr { t, f } => vec![body.succ(t), body.succ(f)],
        OpKind::Switch { dflt, cases } => std::iter::once(body.succ(dflt))
            .chain(body.cases(cases).iter().map(|c| c.succ))
            .collect(),
        _ => Vec::new(),
    }
}

/// What each structured op with a promoted slot stored in it threads, from the slots' liveness.
fn plan(
    body: &Body,
    ops: &[OpId],
    slot_of: &[Option<u32>],
    nslots: usize,
    threaded: Vec<Vec<u32>>,
) -> HashMap<OpId, Plan> {
    let lv = Liveness::new(body, ops, slot_of, nslots);
    let mut plans = HashMap::new();
    for (o, stored) in threaded.into_iter().enumerate() {
        if stored.is_empty() {
            continue;
        }
        let op = OpId::from_raw(o as u32);
        let live =
            |at: u32| -> Vec<u32> { stored.iter().copied().filter(|&k| lv.live(at, k)).collect() };
        let results = live(lv.cont(body, op));
        let params = match body.kind(op) {
            OpKind::Loop { .. } => vec![live(lv.start(body, body.regions(op)[0], EXIT))],
            OpKind::Blocks { .. } => body
                .regions(op)
                .iter()
                .enumerate()
                .map(|(i, &r)| {
                    if i == 0 {
                        Vec::new()
                    } else {
                        live(lv.start(body, r, EXIT))
                    }
                })
                .collect(),
            _ => Vec::new(),
        };
        plans.insert(
            op,
            Plan {
                stored,
                results,
                params,
            },
        );
    }
    plans
}

impl Promoter<'_> {
    /// A name for a new value of slot `k`, unused in the function.
    fn fresh(&mut self, k: u32) -> String {
        let s = &mut self.slots[k as usize];
        loop {
            let name = format!("{}.{}", s.name, s.next_name);
            s.next_name += 1;
            if self.names.insert(name.clone()) {
                return name;
            }
        }
    }

    /// Specs for new values of the slots `ks`' types.
    fn specs(&mut self, ks: &[u32]) -> Vec<(String, Ty)> {
        ks.iter()
            .map(|&k| (self.fresh(k), self.slots[k as usize].ty))
            .collect()
    }

    /// What slot `k` holds per `env`, making its `poison` if nothing was stored yet.
    fn get(&mut self, env: &mut [Cur], k: u32) -> ValueId {
        match env[k as usize] {
            Cur::Val(v) => v,
            Cur::Undef => {
                let v = match self.slots[k as usize].poison {
                    Some(v) => v,
                    None => {
                        let name = self.fresh(k);
                        let s = &self.slots[k as usize];
                        let (alloc, ty) = (s.alloc, s.ty);
                        let loc = self.body.loc(alloc);
                        let op = self.body.insert_after(
                            alloc,
                            OpKind::Poison,
                            [],
                            [spec(&name, ty)],
                            Vec::new(),
                            loc,
                        );
                        let v = self.body.results(op).next().expect("one result");
                        self.slots[k as usize].poison = Some(v);
                        v
                    }
                };
                env[k as usize] = Cur::Val(v);
                v
            }
        }
    }

    fn values(&mut self, env: &mut [Cur], ks: &[u32]) -> Vec<Operand> {
        ks.iter()
            .map(|&k| Operand::value(self.get(env, k)))
            .collect()
    }

    /// Rewrite the ops of `r` in order, `env` holding what each slot holds; a `cf.yield` here
    /// leaves to an op that threads `own`.
    fn region(&mut self, r: RegionId, env: &mut [Cur], own: &[u32]) {
        let mut cur = self.body.ops(r).next();
        while let Some(op) = cur {
            cur = self.body.next(op);
            self.op(op, env, own);
        }
    }

    fn slot(&self, o: Operand) -> Option<u32> {
        match o.get() {
            OperandKind::Value(v) => self.slot_of.get(v.index()).copied().flatten(),
            OperandKind::Hole(_) => None,
        }
    }

    fn op(&mut self, op: OpId, env: &mut [Cur], own: &[u32]) {
        let b = &*self.body;
        let kind = b.kind(op);
        match kind {
            OpKind::Load { .. } => {
                let Some(k) = self.slot(b.operands(op)[0]) else {
                    return;
                };
                let v = self.get(env, k);
                let r = self.body.results(op).next().expect("verified");
                if self.body.facts(r).is_empty() {
                    self.body.replace_all_uses(r, v);
                    self.body.erase(op);
                } else {
                    self.body.set_kind(op, OpKind::Copy);
                    self.body.set_operand(op, 0, Operand::value(v));
                }
            }
            OpKind::Store { .. } => {
                let [v, p] = *b.operands(op) else {
                    unreachable!("verified")
                };
                let Some(k) = self.slot(p) else { return };
                let OperandKind::Value(v) = v.get() else {
                    unreachable!("checked by accesses")
                };
                env[k as usize] = Cur::Val(v);
                self.body.erase(op);
            }
            OpKind::If | OpKind::Loop { .. } | OpKind::Blocks { .. } => {
                let plan = self.plans.remove(&op).unwrap_or_default();
                self.structured(op, kind, &plan, env);
            }
            OpKind::Yield => self.extend(op, kind, own.to_vec(), env),
            OpKind::Break | OpKind::Continue => {
                let (params, results) = self.loops.last().cloned().unwrap_or_default();
                let w = if kind == OpKind::Break {
                    results
                } else {
                    params
                };
                self.extend(op, kind, w, env);
            }
            OpKind::Br { .. } | OpKind::CondBr { .. } | OpKind::Switch { .. } => {
                let blocks = self.blocks.last().cloned().unwrap_or_default();
                self.branch(op, kind, &blocks, env);
            }
            _ => {}
        }
    }

    /// Rewrite a `cf.if`, `cf.loop`, or `cf.blocks` and its regions, threading the slots
    /// `plan` says.
    fn structured(&mut self, op: OpId, kind: OpKind, plan: &Plan, env: &mut [Cur]) {
        let inits = match plan.params.first() {
            Some(ks) if matches!(kind, OpKind::Loop { .. }) && !ks.is_empty() => {
                Some(self.values(env, ks))
            }
            _ => None,
        };
        let x = self.widen_results(op, &plan.results, inits);
        let regions = self.body.regions(x).to_vec();
        // Each region's parameters for its threaded slots.
        let mut params = Vec::new();
        for (i, &r) in regions.iter().enumerate() {
            let ks = plan.params.get(i).cloned().unwrap_or_default();
            let vs = if ks.is_empty() {
                Vec::new()
            } else {
                let specs = self.specs(&ks);
                self.body
                    .append_params(r, specs.iter().map(|(n, t)| spec(n, *t)))
            };
            params.push((ks, vs));
        }
        match kind {
            OpKind::Loop { .. } => self.loops.push((params[0].0.clone(), plan.results.clone())),
            OpKind::Blocks { .. } => self.blocks.push(
                regions
                    .iter()
                    .zip(&params)
                    .map(|(&r, (ks, _))| (self.body.label(r), ks.clone()))
                    .collect(),
            ),
            _ => {}
        }
        for (i, (&r, (ks, vs))) in regions.iter().zip(&params).enumerate() {
            if kind == OpKind::If && !plan.results.is_empty() {
                // A region of a `cf.if` without results may end without `cf.yield`; with
                // results it needs one, to give them.
                let last = self.body.ops(r).last();
                if !last.is_some_and(|o| self.body.kind(o).is_terminator()) {
                    let loc = self.body.loc(x);
                    self.body
                        .append_op(r, OpKind::Yield, [], [], Vec::new(), loc);
                }
            }
            let mut inner = env.to_vec();
            // A slot stored in the op holds, at the start of a region other than a
            // `cf.if`'s or a `cf.blocks`'s entry, its parameter, or (where it is dead) nothing.
            if matches!(kind, OpKind::Loop { .. })
                || (matches!(kind, OpKind::Blocks { .. }) && i > 0)
            {
                for &k in &plan.stored {
                    inner[k as usize] = Cur::Undef;
                }
            }
            for (&k, &v) in ks.iter().zip(vs) {
                inner[k as usize] = Cur::Val(v);
            }
            self.region(r, &mut inner, &plan.results);
        }
        match kind {
            OpKind::Loop { .. } => {
                self.loops.pop();
            }
            OpKind::Blocks { .. } => {
                self.blocks.pop();
            }
            _ => {}
        }
        // After it, the slots it threads hold its results; the others stored in it are dead.
        for &k in &plan.stored {
            env[k as usize] = Cur::Undef;
        }
        self.after(x, &plan.results, env);
    }

    /// Replace a structured op with one that has a result more per threaded slot (and, for a
    /// loop, these operands after its own). Returns the new op.
    fn widen_results(&mut self, op: OpId, w: &[u32], extra: Option<Vec<Operand>>) -> OpId {
        // A loop may take new state without giving new results: the slot is live at the top
        // of its body but dead after it.
        if w.is_empty() && extra.as_ref().is_none_or(Vec::is_empty) {
            return op;
        }
        let b = &*self.body;
        let old: Vec<(String, Ty, Vec<_>)> = b
            .results(op)
            .map(|v| (b.name(v).to_owned(), b.ty(v), b.facts(v).to_vec()))
            .collect();
        let operands: Vec<Operand> = b
            .operands(op)
            .iter()
            .copied()
            .chain(extra.unwrap_or_default())
            .collect();
        let kind = b.kind(op);
        let new = self.specs(w);
        let results = old
            .iter()
            .map(|(n, t, f)| ValueSpec {
                name: n,
                ty: *t,
                facts: f.clone(),
            })
            .chain(new.iter().map(|(n, t)| spec(n, *t)));
        self.body.replace_op(op, kind, operands, results)
    }

    /// After structured op `x`: the threaded slots hold its last results.
    fn after(&mut self, x: OpId, w: &[u32], env: &mut [Cur]) {
        let n = self.body.results(x).len() - w.len();
        for (&k, v) in w.iter().zip(self.body.results(x).skip(n)) {
            env[k as usize] = Cur::Val(v);
        }
    }

    /// Give a `cf.yield`, `cf.break`, or `cf.continue` the values of the slots `w` after its
    /// operands.
    fn extend(&mut self, op: OpId, kind: OpKind, w: Vec<u32>, env: &mut [Cur]) {
        if w.is_empty() {
            return;
        }
        let extra = self.values(env, &w);
        let operands: Vec<Operand> = self
            .body
            .operands(op)
            .iter()
            .copied()
            .chain(extra)
            .collect();
        self.body.replace_op(op, kind, operands, []);
    }

    /// Give each target of a branch the values of the slots it takes after its arguments;
    /// `blocks` are the enclosing `cf.blocks`' labels and slots.
    fn branch(
        &mut self,
        op: OpId,
        kind: OpKind,
        blocks: &[(Option<StrId>, Vec<u32>)],
        env: &mut [Cur],
    ) {
        let succs = targets(self.body, kind);
        let body = &*self.body;
        let slots: Vec<Vec<u32>> = succs
            .iter()
            .map(|s| {
                blocks
                    .iter()
                    .find(|(l, _)| same_label(body, *l, s.label))
                    .map_or(Vec::new(), |(_, ks)| ks.clone())
            })
            .collect();
        if slots.iter().all(Vec::is_empty) {
            return;
        }
        let old = self.body.operands(op).to_vec();
        // The branch's own operands, then each target's arguments in order.
        let own = old.len() - succs.iter().map(|s| s.nargs as usize).sum::<usize>();
        let mut operands = old[..own].to_vec();
        let mut next = own;
        let mut widened = Vec::new();
        for (s, ks) in succs.iter().zip(&slots) {
            let end = next + s.nargs as usize;
            operands.extend_from_slice(&old[next..end]);
            operands.extend(self.values(env, ks));
            widened.push(Succ {
                label: s.label,
                nargs: s.nargs + ks.len() as u32,
            });
            next = end;
        }
        let b = &mut *self.body;
        let kind = match kind {
            OpKind::Br { .. } => OpKind::Br {
                dest: b.add_succ(widened[0]),
            },
            OpKind::CondBr { .. } => OpKind::CondBr {
                t: b.add_succ(widened[0]),
                f: b.add_succ(widened[1]),
            },
            OpKind::Switch { cases, .. } => {
                let cs: Vec<_> = b
                    .cases(cases)
                    .iter()
                    .zip(&widened[1..])
                    .map(|(c, &succ)| crate::body::Case { key: c.key, succ })
                    .collect();
                OpKind::Switch {
                    dflt: b.add_succ(widened[0]),
                    cases: b.add_cases(cs),
                }
            }
            _ => unreachable!(),
        };
        b.replace_op(op, kind, operands, []);
    }
}

fn spec(name: &str, ty: Ty) -> ValueSpec<'_> {
    ValueSpec {
        name,
        ty,
        facts: Vec::new(),
    }
}
