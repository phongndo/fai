//! The validator's dataflow state ([`State`]): which input values each location holds.
//!
//! It is a map from locations (the 63 registers, the spill slots by offset, the save slots by
//! offset) to sets of values, with the operations the walk needs. The first implementation was
//! that map written out directly (a `Vec` of sets for the registers, a `BTreeMap` of sets for
//! each kind of slot), and it is kept below as the model the tests compare against
//! (`tests::Model`). This one stores the same map so that copying it is cheap, because the walk
//! copies it at every block entry, every join, and every choice point, and a function with `B`
//! blocks and `S` slots then copied `B × S` sets:
//!
//! - Locations are numbered densely (slots and saves in the order the function first uses each
//!   offset) and kept in chunks of [`CHUNK`], each behind an `Rc`. Copying a state copies the
//!   chunk pointers; a chunk is copied when a state that shares it changes it. A join or an
//!   equality takes a chunk both sides share as it is.
//! - A set of up to [`INLINE`] values is stored in place ([`Set`]), so copying a chunk allocates
//!   nothing else.
//! - Each chunk lists the values its sets may hold (a superset), so removing a value from every
//!   location skips the chunks that can't hold it.
//!
//! None of this changes what the state means, so it changes nothing the validator accepts or
//! refuses, or its messages: the model-based tests check that every operation agrees with the
//! model's, on random sequences of operations.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use fai_ir::ir::Reg;

/// An input value a location may hold.
pub(super) type Val = u32;

/// How many values a [`Set`] holds in place.
pub(super) const INLINE: usize = 5;

/// A sorted set of values, the contents of one location.
#[derive(Clone, Debug)]
pub(super) enum Set {
    Inline { len: u8, vals: [Val; INLINE] },
    Heap(Vec<Val>),
}

impl Default for Set {
    fn default() -> Set {
        Set::EMPTY
    }
}

impl PartialEq for Set {
    fn eq(&self, o: &Set) -> bool {
        self.as_slice() == o.as_slice()
    }
}

impl Eq for Set {}

impl Set {
    pub(super) const EMPTY: Set = Set::Inline {
        len: 0,
        vals: [0; INLINE],
    };

    pub(super) fn one(v: Val) -> Set {
        let mut vals = [0; INLINE];
        vals[0] = v;
        Set::Inline { len: 1, vals }
    }

    pub(super) fn as_slice(&self) -> &[Val] {
        match self {
            Set::Inline { len, vals } => &vals[..*len as usize],
            Set::Heap(v) => v,
        }
    }

    pub(super) fn is_empty(&self) -> bool {
        self.as_slice().is_empty()
    }

    pub(super) fn contains(&self, v: Val) -> bool {
        self.as_slice().binary_search(&v).is_ok()
    }

    pub(super) fn insert(&mut self, v: Val) {
        let Err(i) = self.as_slice().binary_search(&v) else {
            return;
        };
        match self {
            Set::Inline { len, vals } if (*len as usize) < INLINE => {
                let n = *len as usize;
                vals.copy_within(i..n, i + 1);
                vals[i] = v;
                *len += 1;
            }
            Set::Inline { vals, .. } => {
                let mut h = Vec::with_capacity(2 * INLINE);
                h.extend_from_slice(&vals[..i]);
                h.push(v);
                h.extend_from_slice(&vals[i..]);
                *self = Set::Heap(h);
            }
            Set::Heap(h) => h.insert(i, v),
        }
    }

    /// Remove `v`; whether it was there.
    pub(super) fn remove(&mut self, v: Val) -> bool {
        let Ok(i) = self.as_slice().binary_search(&v) else {
            return false;
        };
        match self {
            Set::Inline { len, vals } => {
                let n = *len as usize;
                vals.copy_within(i + 1..n, i);
                *len -= 1;
            }
            Set::Heap(h) => {
                h.remove(i);
            }
        }
        true
    }

    pub(super) fn intersect(&self, o: &Set) -> Set {
        let b = o.as_slice();
        let mut out = Set::EMPTY;
        for &x in self.as_slice() {
            if b.binary_search(&x).is_ok() {
                out.push_larger(x);
            }
        }
        out
    }

    /// Append `v`, larger than every value in the set.
    fn push_larger(&mut self, v: Val) {
        debug_assert!(self.as_slice().last().is_none_or(|&l| l < v));
        match self {
            Set::Inline { len, vals } if (*len as usize) < INLINE => {
                vals[*len as usize] = v;
                *len += 1;
            }
            Set::Inline { vals, .. } => {
                let mut h = Vec::with_capacity(2 * INLINE);
                h.extend_from_slice(vals);
                h.push(v);
                *self = Set::Heap(h);
            }
            Set::Heap(h) => h.push(v),
        }
    }
}

/// How many locations share one chunk.
pub(super) const CHUNK: usize = 32;

#[derive(Clone, Debug)]
struct Chunk {
    sets: [Set; CHUNK],
    /// The locations that are in the map. A register is always; a slot once it is stored to,
    /// until a join leaves it empty (the model's `BTreeMap` keys). A location not in the map
    /// holds nothing, and its set is empty.
    present: u32,
    /// Sorted; every value any of `sets` holds, and perhaps values none holds any more.
    may_hold: Vec<Val>,
}

impl Chunk {
    fn new() -> Chunk {
        Chunk {
            sets: std::array::from_fn(|_| Set::EMPTY),
            present: 0,
            may_hold: Vec::new(),
        }
    }

    fn note(&mut self, v: Val) {
        if let Err(i) = self.may_hold.binary_search(&v) {
            self.may_hold.insert(i, v);
        }
    }

    fn holds_somewhere(&self, v: Val) -> bool {
        self.may_hold.binary_search(&v).is_ok() && self.sets.iter().any(|s| s.contains(v))
    }

    /// Whether a location in the map holds nothing.
    fn has_empty(&self) -> bool {
        (0..CHUNK).any(|k| self.present & (1 << k) != 0 && self.sets[k].is_empty())
    }

    fn same(&self, o: &Chunk) -> bool {
        self.present == o.present && self.sets == o.sets
    }
}

/// A map from dense location numbers to sets, in shared chunks. Chunks past the end are
/// absent: every location in them is not in the map.
#[derive(Clone, Debug, Default)]
struct Locs {
    chunks: Vec<Rc<Chunk>>,
}

static EMPTY_SET: Set = Set::EMPTY;

impl Locs {
    fn get(&self, i: usize) -> &Set {
        self.chunks
            .get(i / CHUNK)
            .map_or(&EMPTY_SET, |c| &c.sets[i % CHUNK])
    }

    /// Location `i` holds exactly `s`, and is in the map.
    fn set(&mut self, i: usize, s: Set) {
        while self.chunks.len() <= i / CHUNK {
            self.chunks.push(Rc::new(Chunk::new()));
        }
        let c = Rc::make_mut(&mut self.chunks[i / CHUNK]);
        for &v in s.as_slice() {
            c.note(v);
        }
        c.sets[i % CHUNK] = s;
        c.present |= 1 << (i % CHUNK);
    }

    /// No location holds `v` any more.
    fn remove_everywhere(&mut self, v: Val) {
        for c in &mut self.chunks {
            if c.holds_somewhere(v) {
                let c = Rc::make_mut(c);
                for s in &mut c.sets {
                    s.remove(v);
                }
                if let Ok(i) = c.may_hold.binary_search(&v) {
                    c.may_hold.remove(i);
                }
            }
        }
    }

    /// Every location holding `v` holds `w` too; whether any does.
    fn alias(&mut self, v: Val, w: Val) -> bool {
        let mut any = false;
        for c in &mut self.chunks {
            if c.holds_somewhere(v) {
                let c = Rc::make_mut(c);
                for s in &mut c.sets {
                    if s.contains(v) {
                        s.insert(w);
                    }
                }
                c.note(w);
                any = true;
            }
        }
        any
    }

    /// The pointwise intersection, over the locations in both maps; with `keep_empty` false, a
    /// location whose intersection is empty leaves the map.
    fn join(&self, o: &Locs, keep_empty: bool) -> Locs {
        let chunks = self
            .chunks
            .iter()
            .zip(&o.chunks)
            .map(|(a, b)| {
                // A chunk both share is its own join, unless a location in it is in the map but
                // empty, which the join drops when it keeps no empty ones.
                if Rc::ptr_eq(a, b) && (keep_empty || !a.has_empty()) {
                    return a.clone();
                }
                let mut c = Chunk::new();
                let both = a.present & b.present;
                for k in 0..CHUNK {
                    if both & (1 << k) == 0 {
                        continue;
                    }
                    let s = a.sets[k].intersect(&b.sets[k]);
                    if keep_empty || !s.is_empty() {
                        for &v in s.as_slice() {
                            c.note(v);
                        }
                        c.sets[k] = s;
                        c.present |= 1 << k;
                    }
                }
                Rc::new(c)
            })
            .collect();
        Locs { chunks }
    }
}

impl PartialEq for Locs {
    fn eq(&self, o: &Locs) -> bool {
        let n = self.chunks.len().max(o.chunks.len());
        (0..n).all(|i| match (self.chunks.get(i), o.chunks.get(i)) {
            (Some(a), Some(b)) => Rc::ptr_eq(a, b) || a.same(b),
            (Some(c), None) | (None, Some(c)) => c.present == 0,
            (None, None) => true,
        })
    }
}

/// Dense numbers for one kind of slot, by offset, shared by every state of one validation.
#[derive(Clone, Debug, Default)]
pub(super) struct Offsets(Rc<RefCell<HashMap<i64, usize>>>);

impl Offsets {
    fn find(&self, off: i64) -> Option<usize> {
        self.0.borrow().get(&off).copied()
    }

    fn number(&self, off: i64) -> usize {
        let mut m = self.0.borrow_mut();
        let n = m.len();
        *m.entry(off).or_insert(n)
    }
}

/// What `x16` holds, for far spill-slot addresses.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Addr {
    Unknown,
    Const(u64),
    SpPlus(i64),
}

/// The register locations: `x0`…`x30` are 0…30, `d0`…`d31` are 31…62.
pub(super) const NREGS: usize = 63;

/// Which values each location holds: registers, spill slots (by `sp` offset), and save slots
/// (by `x29` offset); and what `x16` holds as an address.
#[derive(Clone, Debug)]
pub(super) struct State {
    regs: Locs,
    slots: Locs,
    saves: Locs,
    slot_ids: Offsets,
    save_ids: Offsets,
    x16: Addr,
}

impl PartialEq for State {
    fn eq(&self, o: &State) -> bool {
        // Both states number slots alike: they come from one validation.
        debug_assert!(Rc::ptr_eq(&self.slot_ids.0, &o.slot_ids.0));
        self.regs == o.regs && self.slots == o.slots && self.saves == o.saves && self.x16 == o.x16
    }
}

impl State {
    /// Every register holds `init(p)`; no slot holds anything. `slots` and `saves` number the
    /// offsets for this state and every state made from it.
    pub(super) fn new(init: impl Fn(u32) -> Set) -> State {
        let mut regs = Locs::default();
        for p in 0..NREGS {
            regs.set(p, init(p as u32));
        }
        State {
            regs,
            slots: Locs::default(),
            saves: Locs::default(),
            slot_ids: Offsets::default(),
            save_ids: Offsets::default(),
            x16: Addr::Unknown,
        }
    }

    pub(super) fn join(&self, o: &State) -> State {
        State {
            regs: self.regs.join(&o.regs, true),
            slots: self.slots.join(&o.slots, false),
            saves: self.saves.join(&o.saves, false),
            slot_ids: self.slot_ids.clone(),
            save_ids: self.save_ids.clone(),
            x16: if self.x16 == o.x16 {
                self.x16
            } else {
                Addr::Unknown
            },
        }
    }

    /// `v` gets a new value: no location holds the old one any more.
    pub(super) fn kill(&mut self, v: Val) {
        self.regs.remove_everywhere(v);
        self.slots.remove_everywhere(v);
        self.saves.remove_everywhere(v);
    }

    /// Every register and spill slot (not save slot) holding `v` holds `w` too; whether any
    /// does.
    pub(super) fn alias(&mut self, v: Val, w: Val) -> bool {
        let r = self.regs.alias(v, w);
        let s = self.slots.alias(v, w);
        r | s
    }

    /// Register location `p`'s set.
    pub(super) fn reg(&self, p: usize) -> &Set {
        self.regs.get(p)
    }

    /// Register location `p` now holds exactly `s`. (This doesn't touch `x16`'s address; see
    /// `Checker`'s callers.)
    pub(super) fn set_reg_loc(&mut self, p: usize, s: Set) {
        self.regs.set(p, s);
    }

    pub(super) fn slot(&self, off: i64) -> Set {
        self.slot_ids
            .find(off)
            .map_or(Set::EMPTY, |i| self.slots.get(i).clone())
    }

    pub(super) fn set_slot(&mut self, off: i64, s: Set) {
        let i = self.slot_ids.number(off);
        self.slots.set(i, s);
    }

    pub(super) fn save(&self, off: i64) -> Set {
        self.save_ids
            .find(off)
            .map_or(Set::EMPTY, |i| self.saves.get(i).clone())
    }

    pub(super) fn set_save(&mut self, off: i64, s: Set) {
        let i = self.save_ids.number(off);
        self.saves.set(i, s);
    }

    pub(super) fn x16(&self) -> Addr {
        self.x16
    }

    pub(super) fn set_x16(&mut self, a: Addr) {
        self.x16 = a;
    }
}

/// `r`'s location, if it is one of `x0`…`x30`, `d0`…`d31`.
pub(super) fn loc(r: Reg) -> Option<usize> {
    if r.is_gpr() {
        Some(r.0 as usize)
    } else if r.is_fpr() {
        Some((super::FP_BASE + r.fpr_index()) as usize)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;

    /// The state as the validator first stored it: the specification of [`State`].
    #[derive(Clone, PartialEq, Debug)]
    struct Model {
        regs: Vec<Vec<Val>>,
        slots: BTreeMap<i64, Vec<Val>>,
        saves: BTreeMap<i64, Vec<Val>>,
        x16: Addr,
    }

    fn insert(set: &mut Vec<Val>, v: Val) {
        if let Err(i) = set.binary_search(&v) {
            set.insert(i, v);
        }
    }

    fn intersect(a: &[Val], b: &[Val]) -> Vec<Val> {
        a.iter()
            .copied()
            .filter(|x| b.binary_search(x).is_ok())
            .collect()
    }

    impl Model {
        fn join(&self, o: &Model) -> Model {
            let map = |a: &BTreeMap<i64, Vec<Val>>, b: &BTreeMap<i64, Vec<Val>>| {
                a.iter()
                    .filter_map(|(k, x)| b.get(k).map(|y| (*k, intersect(x, y))))
                    .filter(|(_, s)| !s.is_empty())
                    .collect()
            };
            Model {
                regs: self
                    .regs
                    .iter()
                    .zip(&o.regs)
                    .map(|(a, b)| intersect(a, b))
                    .collect(),
                slots: map(&self.slots, &o.slots),
                saves: map(&self.saves, &o.saves),
                x16: if self.x16 == o.x16 {
                    self.x16
                } else {
                    Addr::Unknown
                },
            }
        }

        fn kill(&mut self, v: Val) {
            for s in self
                .regs
                .iter_mut()
                .chain(self.slots.values_mut())
                .chain(self.saves.values_mut())
            {
                if let Ok(i) = s.binary_search(&v) {
                    s.remove(i);
                }
            }
        }

        fn alias(&mut self, v: Val, w: Val) -> bool {
            let mut any = false;
            for s in self.regs.iter_mut().chain(self.slots.values_mut()) {
                if s.binary_search(&v).is_ok() {
                    insert(s, w);
                    any = true;
                }
            }
            any
        }
    }

    /// A small deterministic generator (xorshift).
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    fn set_of(vals: &[Val]) -> Set {
        let mut s = Set::EMPTY;
        for &v in vals {
            s.insert(v);
        }
        s
    }

    fn random_vals(rng: &mut Rng, vals: u64) -> Vec<Val> {
        let n = rng.below(9) as usize;
        let set: BTreeSet<Val> = (0..n).map(|_| rng.below(vals) as Val).collect();
        set.into_iter().collect()
    }

    /// Everything a state says, compared with the model's.
    fn agree(st: &State, m: &Model, offsets: &[i64]) {
        for p in 0..NREGS {
            assert_eq!(st.reg(p).as_slice(), &m.regs[p][..], "register {p}");
        }
        for &off in offsets {
            let want = m.slots.get(&off).cloned().unwrap_or_default();
            assert_eq!(st.slot(off).as_slice(), &want[..], "slot {off}");
            let want = m.saves.get(&off).cloned().unwrap_or_default();
            assert_eq!(st.save(off).as_slice(), &want[..], "save {off}");
        }
        assert_eq!(st.x16(), m.x16);
    }

    #[test]
    fn set_agrees_with_a_sorted_vec() {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        for _ in 0..2000 {
            let mut s = Set::EMPTY;
            let mut v: Vec<Val> = Vec::new();
            for _ in 0..rng.below(40) {
                let x = rng.below(12) as Val;
                if rng.below(3) == 0 {
                    assert_eq!(s.remove(x), v.binary_search(&x).is_ok());
                    if let Ok(i) = v.binary_search(&x) {
                        v.remove(i);
                    }
                } else {
                    s.insert(x);
                    insert(&mut v, x);
                }
                assert_eq!(s.as_slice(), &v[..]);
                assert_eq!(s.contains(x), v.binary_search(&x).is_ok());
            }
            let o = set_of(&random_vals(&mut rng, 12));
            assert_eq!(s.intersect(&o).as_slice(), &intersect(&v, o.as_slice())[..]);
        }
    }

    /// Random programs of state operations, with branches (clones), joins, and comparisons, on
    /// both the state and the model: every observation must agree.
    /// `REGCHECK_STATE_SEEDS` sets how many programs (by default 300 in release builds, 40 in
    /// development builds, which run it about ten times slower).
    #[test]
    fn state_agrees_with_the_model() {
        let seeds: u64 = std::env::var("REGCHECK_STATE_SEEDS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(if cfg!(debug_assertions) { 40 } else { 300 });
        for seed in 1..=seeds {
            let mut rng = Rng(seed.wrapping_mul(0x2545_f491_4f6c_dd1d) | 1);
            // Few values and offsets, so that sets collide, chunks fill, and joins empty slots;
            // enough offsets for several chunks.
            let vals = 2 + rng.below(40);
            let offsets: Vec<i64> = (0..(1 + rng.below(3 * CHUNK as u64)))
                .map(|k| 8 * k as i64 - 64)
                .collect();
            let init = |p: u32| {
                let mut s = Set::one(1000 + p);
                if p.is_multiple_of(7) {
                    s.insert(2000 + p);
                }
                s
            };
            let st0 = State::new(init);
            let m0 = Model {
                regs: (0..NREGS as u32)
                    .map(|p| init(p).as_slice().to_vec())
                    .collect(),
                slots: BTreeMap::new(),
                saves: BTreeMap::new(),
                x16: Addr::Unknown,
            };
            let mut pool: Vec<(State, Model)> = vec![(st0, m0)];
            for _ in 0..400 {
                let k = rng.below(pool.len() as u64) as usize;
                let off = offsets[rng.below(offsets.len() as u64) as usize];
                let v = rng.below(vals) as Val;
                let (st, m) = &mut pool[k];
                match rng.below(11) {
                    0 => {
                        st.kill(v);
                        m.kill(v);
                    }
                    1 => {
                        let w = rng.below(vals) as Val;
                        assert_eq!(st.alias(v, w), m.alias(v, w));
                    }
                    2 => {
                        let p = rng.below(NREGS as u64) as usize;
                        let s = random_vals(&mut rng, vals);
                        st.set_reg_loc(p, set_of(&s));
                        m.regs[p] = s;
                    }
                    3 => {
                        let s = random_vals(&mut rng, vals);
                        st.set_slot(off, set_of(&s));
                        m.slots.insert(off, s);
                    }
                    4 => {
                        let s = random_vals(&mut rng, vals);
                        st.set_save(off, set_of(&s));
                        m.saves.insert(off, s);
                    }
                    5 => {
                        let a = match rng.below(3) {
                            0 => Addr::Unknown,
                            1 => Addr::Const(rng.below(4)),
                            _ => Addr::SpPlus(rng.below(4) as i64),
                        };
                        st.set_x16(a);
                        m.x16 = a;
                    }
                    6 => {
                        // A slot's contents into a register, and back, as spills do.
                        let p = rng.below(NREGS as u64) as usize;
                        let s = st.slot(off);
                        st.set_reg_loc(p, s);
                        m.regs[p] = m.slots.get(&off).cloned().unwrap_or_default();
                        let s = st.reg(p).clone();
                        st.set_save(off, s);
                        m.saves.insert(off, m.regs[p].clone());
                    }
                    7 | 8 if pool.len() < 12 => {
                        let c = pool[k].clone();
                        pool.push(c);
                    }
                    9 if pool.len() > 1 => {
                        let j = rng.below(pool.len() as u64) as usize;
                        let joined = (pool[k].0.join(&pool[j].0), pool[k].1.join(&pool[j].1));
                        if rng.below(2) == 0 {
                            pool[k] = joined;
                        } else {
                            pool.push(joined);
                        }
                    }
                    _ if pool.len() > 1 => {
                        let j = rng.below(pool.len() as u64) as usize;
                        assert_eq!(
                            pool[k].0 == pool[j].0,
                            pool[k].1 == pool[j].1,
                            "seed {seed}: equality of {k} and {j}"
                        );
                    }
                    _ => {}
                }
                if pool.len() > 12 {
                    pool.swap_remove(0);
                }
                for (st, m) in &pool {
                    agree(st, m, &offsets);
                }
            }
            // Every pair compares as the model's do, including a state with itself.
            for (a, ma) in &pool {
                for (b, mb) in &pool {
                    assert_eq!(a == b, ma == mb, "seed {seed}");
                }
            }
        }
    }
}
