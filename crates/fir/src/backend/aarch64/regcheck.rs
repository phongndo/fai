//! Validation of register allocation and frame lowering on the code they produce.
//!
//! [`validate`] compares a function's code before allocation (virtual registers, the frame
//! placeholder) with its code after allocation, spilling, and frame lowering, and accepts the
//! second only if it computes what the first does under the AAPCS64 assumptions below. It is
//! given nothing from the allocator: no assignment, no list of what was inserted. It reads the
//! final instructions, so a bug in assignment, in rewriting, in spill code, or in the frame
//! lowering is caught the same way.
//!
//! **How.** A forward dataflow over the blocks of the output, which must be the input's blocks in
//! the same order with the same branches. Its state maps each location (`x0`…`x30`, each spill
//! slot `[sp, #off]`, each callee-saved save slot `[x29, #-off]`) to the set of input values it
//! is known to hold: a virtual register `v` (as last written), a physical register as the input
//! last wrote it (`x0` after a call, an argument register at entry), or a callee-saved register's
//! value at entry. At joins the sets are intersected. Within a block the output is walked in
//! step with the input: each input instruction must appear with the same opcode and immediates,
//! its virtual registers renamed to physical ones and its physical registers unchanged, and
//! every register it reads must hold the value the input reads there; or it is a `mov` between
//! two virtual registers that the output left out, and the destination then lives wherever the
//! source does. Between them, the output may only insert spill loads and stores (8-byte
//! accesses to `sp` at or above the spill area, directly or through `x16` computed as `sp` plus a
//! constant), saves and restores of callee-saved registers below `x29`, and, in place of the
//! prologue's placeholder `sub sp, sp, N`, the real frame allocation.
//!
//! **What is checked at the end.** At each `ret` every callee-saved register holds its entry
//! value; at each call the argument registers hold the input's arguments; the frame the
//! prologue allocates covers the outgoing arguments, the locals, every spill slot used, and the
//! save slots, without overlap.
//!
//! **Assumptions (trusted, not checked here).** A callee preserves `x19`–`x28`, `x29`, `sp`, and
//! memory at and above the caller's `sp`; the program's own memory accesses never reach the spill
//! and save areas (a pointer that does is out of bounds of every allocation, which is UB in the
//! source); the input code is what instruction selection meant (that is the LFIR differential
//! tests' job); and the encoding of the output is right (the native tests). The checker is not
//! proved in Lean: see `docs/assurance/README.md`.

use std::collections::BTreeMap;

use super::abi::{CallShape, FP_CALLER_SAVED};
use super::mir::{CALLER_SAVED, Inst, MFunc};
use super::regalloc::{Effects, Shapes, effects};
use crate::ir::{AluImmOp, AluOp, FSize, FUnaryOp, MemSize, MovOp, Reg, Sf};

/// An input value a location may hold.
type Val = u32;
/// The physical register at location `p` as the input last wrote it.
const PHYS: u32 = 1 << 30;
/// The callee-saved register at location `p`'s value at entry.
const ENTRY: u32 = PHYS + 128;
/// The register locations: `x0`…`x30` are 0…30, `d0`…`d31` are 31…62.
const NREGS: usize = 63;
const FP_BASE: u32 = 31;

fn phys(p: u32) -> Val {
    PHYS + p
}

/// A physical register's location.
fn loc(r: Reg) -> Option<usize> {
    if r.is_gpr() {
        Some(r.0 as usize)
    } else if r.is_fpr() {
        Some((FP_BASE + r.fpr_index()) as usize)
    } else {
        None
    }
}

/// The callee-saved registers' locations: `x19`…`x28`, and `d8`…`d15` (their low 64 bits, all
/// FIR keeps).
fn callee_saved() -> impl Iterator<Item = u32> {
    (19..=28).chain(FP_BASE + 8..=FP_BASE + 15)
}

fn reg_name(p: u32) -> String {
    if p < FP_BASE {
        format!("x{p}")
    } else {
        format!("d{}", p - FP_BASE)
    }
}

/// What `x16` holds, for far spill-slot addresses.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Addr {
    Unknown,
    Const(u64),
    SpPlus(i64),
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct State {
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

impl State {
    fn entry() -> State {
        let mut regs: Vec<Vec<Val>> = (0..NREGS as u32).map(|p| vec![phys(p)]).collect();
        for p in callee_saved() {
            insert(&mut regs[p as usize], ENTRY + p);
        }
        State {
            regs,
            slots: BTreeMap::new(),
            saves: BTreeMap::new(),
            x16: Addr::Unknown,
        }
    }

    fn join(&self, o: &State) -> State {
        let map = |a: &BTreeMap<i64, Vec<Val>>, b: &BTreeMap<i64, Vec<Val>>| {
            a.iter()
                .filter_map(|(k, x)| b.get(k).map(|y| (*k, intersect(x, y))))
                .filter(|(_, s)| !s.is_empty())
                .collect()
        };
        State {
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

    /// `v` gets a new value: no location holds the old one any more.
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

    /// Register `r` now holds exactly `set` (the old contents are gone).
    fn set_reg(&mut self, r: Reg, set: Vec<Val>) {
        if let Some(p) = loc(r) {
            self.regs[p] = set;
            if r == Reg::x(16) {
                self.x16 = Addr::Unknown;
            }
        }
    }

    fn holds(&self, r: Reg, v: Val) -> bool {
        loc(r).is_some_and(|p| self.regs[p].binary_search(&v).is_ok())
    }

    fn get(&self, r: Reg) -> Vec<Val> {
        loc(r).map_or_else(Vec::new, |p| self.regs[p].clone())
    }
}

/// The value an input register denotes.
fn val(r: Reg) -> Option<Val> {
    if r.is_virtual() {
        Some(r.virt_index())
    } else {
        loc(r).map(|p| phys(p as u32))
    }
}

fn show(v: Val) -> String {
    if v >= ENTRY {
        format!("{}'s value at entry", reg_name(v - ENTRY))
    } else if v >= PHYS {
        reg_name(v - PHYS)
    } else {
        format!("v{v}")
    }
}

/// A 64-bit move between two registers of one class: what the rewriting leaves out when both
/// get the same home.
fn as_move(i: Inst) -> Option<(Reg, Reg)> {
    match i {
        Inst::Mov { sf: Sf::X, d, n }
        | Inst::Funary {
            op: FUnaryOp::Fmov,
            fs: FSize::D,
            d,
            n,
        } if d.is_fp() == n.is_fp() => Some((d, n)),
        _ => None,
    }
}

/// The instruction with its registers blanked, to compare opcodes and immediates.
fn shape(i: Inst) -> Inst {
    i.map_regs(|_, _| Reg(0))
}

/// A frame or spill instruction the output may insert, classified.
enum Inserted {
    SlotLoad { t: Reg, off: i64 },
    SlotStore { t: Reg, off: i64 },
    SaveStore { r: Reg, off: i64 },
    SaveLoad { r: Reg, off: i64 },
    X16(Addr),
}

struct Checker<'a> {
    input: &'a MFunc,
    out: &'a MFunc,
    shapes: Shapes<'a>,
    /// Where the spill area starts: above the outgoing arguments and the locals.
    spill_base: i64,
    /// The largest spill slot end and the lowest save offset seen.
    spill_end: i64,
    save_low: i64,
    /// The frame size the output allocates in place of the placeholder, if it was found.
    frame: Option<u64>,
    /// Whether the output's frame allocation realigned `sp`.
    realigned: bool,
    /// Whether `sp` is the function's own (between the frame allocation and `mov sp, x29`):
    /// only then are `sp`-relative accesses above the locals spill slots.
    framed: bool,
    fx: Effects,
    /// Reused register lists for `step`.
    bufs: [Vec<Reg>; 4],
}

impl Checker<'_> {
    /// Whether the register at location `p` holds `v`.
    fn regs_hold(&self, st: &State, p: u32, v: Val) -> Option<()> {
        st.regs[p as usize].binary_search(&v).ok().map(|_| ())
    }

    fn err<T>(&self, b: usize, j: usize, msg: impl std::fmt::Display) -> Result<T, String> {
        Err(format!(
            "function {}: block {b}, output instruction {j} ({:?}): {msg}",
            self.out.index,
            self.out.insts.get(j)
        ))
    }

    fn classify(&self, st: &State, i: Inst) -> Option<Inserted> {
        let x16 = Reg::x(16);
        if !self.framed {
            return None;
        }
        match i {
            Inst::Ldr {
                size: MemSize::X,
                d,
                base,
                off,
            } if base == Reg::SP && off >= self.spill_base => {
                Some(Inserted::SlotLoad { t: d, off })
            }
            Inst::Str {
                size: MemSize::X,
                s,
                base,
                off,
            } if base == Reg::SP && off >= self.spill_base => {
                Some(Inserted::SlotStore { t: s, off })
            }
            Inst::Ldr {
                size: MemSize::X,
                d,
                base,
                off: 0,
            } if base == x16 => match st.x16 {
                Addr::SpPlus(o) if o >= self.spill_base => {
                    Some(Inserted::SlotLoad { t: d, off: o })
                }
                _ => None,
            },
            Inst::Str {
                size: MemSize::X,
                s,
                base,
                off: 0,
            } if base == x16 => match st.x16 {
                Addr::SpPlus(o) if o >= self.spill_base => {
                    Some(Inserted::SlotStore { t: s, off: o })
                }
                _ => None,
            },
            Inst::Str {
                size: MemSize::X,
                s,
                base,
                off,
            } if base == Reg::FP && off < 0 => Some(Inserted::SaveStore { r: s, off }),
            Inst::Ldr {
                size: MemSize::X,
                d,
                base,
                off,
            } if base == Reg::FP && off < 0 => Some(Inserted::SaveLoad { r: d, off }),
            Inst::MovWide {
                op: MovOp::Movz,
                sf: Sf::X,
                d,
                imm,
                hw,
            } if d == x16 => Some(Inserted::X16(Addr::Const(u64::from(imm) << hw))),
            Inst::MovWide {
                op: MovOp::Movk,
                sf: Sf::X,
                d,
                imm,
                hw,
            } if d == x16 => match st.x16 {
                Addr::Const(c) => {
                    let m = 0xffffu64 << hw;
                    Some(Inserted::X16(Addr::Const(
                        (c & !m) | (u64::from(imm) << hw),
                    )))
                }
                _ => None,
            },
            Inst::Alu {
                op: AluOp::Add,
                sf: Sf::X,
                d,
                n,
                m,
            } if d == x16 && n == Reg::SP && m == x16 => match st.x16 {
                Addr::Const(c) => Some(Inserted::X16(Addr::SpPlus(c as i64))),
                _ => None,
            },
            _ => None,
        }
    }

    fn apply_inserted(
        &mut self,
        st: &mut State,
        ins: Inserted,
        b: usize,
        j: usize,
    ) -> Result<(), String> {
        match ins {
            Inserted::SlotLoad { t, off } => {
                if off % 8 != 0 {
                    return self.err(b, j, "a misaligned spill slot");
                }
                self.spill_end = self.spill_end.max(off + 8);
                let s = st.slots.get(&off).cloned().unwrap_or_default();
                st.set_reg(t, s);
            }
            Inserted::SlotStore { t, off } => {
                if off % 8 != 0 {
                    return self.err(b, j, "a misaligned spill slot");
                }
                if loc(t).is_none() {
                    return self.err(
                        b,
                        j,
                        "a spill store of a register that isn't x0…x30 or d0…d31",
                    );
                }
                self.spill_end = self.spill_end.max(off + 8);
                st.slots.insert(off, st.get(t));
            }
            Inserted::SaveStore { r, off } => {
                // Aligned 8-byte slots wholly below x29 can't overlap each other or x29's own pair.
                if off % 8 != 0 || off > -8 {
                    return self.err(
                        b,
                        j,
                        "a save slot below x29 that isn't an aligned 8-byte slot",
                    );
                }
                if loc(r).is_none() {
                    return self.err(b, j, "a save of a register that isn't x0…x30 or d0…d31");
                }
                self.save_low = self.save_low.min(off);
                st.saves.insert(off, st.get(r));
            }
            Inserted::SaveLoad { r, off } => {
                if off % 8 != 0 || off > -8 {
                    return self.err(
                        b,
                        j,
                        "a save slot below x29 that isn't an aligned 8-byte slot",
                    );
                }
                self.save_low = self.save_low.min(off);
                let s = st.saves.get(&off).cloned().unwrap_or_default();
                st.set_reg(r, s);
            }
            Inserted::X16(a) => {
                st.set_reg(Reg::x(16), Vec::new());
                st.x16 = a;
            }
        }
        Ok(())
    }

    /// The output's frame allocation where the input has its placeholder: `sub sp, sp, #k`
    /// (one or two), or `x16` set to a constant and `sub sp, sp, x16`, then optionally
    /// `mov x16, sp` and `and sp, x16, #-align`. Returns how far `j` moved.
    fn frame_alloc(
        &mut self,
        st: &mut State,
        b: usize,
        mut j: usize,
        end: usize,
    ) -> Result<usize, String> {
        let x16 = Reg::x(16);
        let mut size: u64 = 0;
        let start = j;
        // What x16 holds within the sequence: a constant being built, or a snapshot of `sp`.
        let mut constant: Option<u64> = None;
        let mut holds_sp = false;
        let mut realigned = false;
        while j < end {
            match self.out.insts[j] {
                Inst::AluImm {
                    op: AluImmOp::Sub,
                    sf: Sf::X,
                    d: Reg::SP,
                    n: Reg::SP,
                    imm,
                } if imm >= 0 && !realigned => {
                    size += imm as u64;
                    holds_sp = false;
                }
                Inst::MovWide {
                    op,
                    sf: Sf::X,
                    d,
                    imm,
                    hw,
                } if d == x16 && !realigned => {
                    let bits = u64::from(imm) << hw;
                    constant = match (op, constant) {
                        (MovOp::Movz, _) => Some(bits),
                        (MovOp::Movk, Some(c)) => Some((c & !(0xffffu64 << hw)) | bits),
                        _ => {
                            return self.err(
                                b,
                                j,
                                "an unexpected x16 setup in the frame allocation",
                            );
                        }
                    };
                    holds_sp = false;
                }
                Inst::Alu {
                    op: AluOp::Sub,
                    sf: Sf::X,
                    d: Reg::SP,
                    n: Reg::SP,
                    m,
                } if m == x16 && !realigned => match constant {
                    Some(c) => {
                        size += c;
                        holds_sp = false;
                    }
                    None => return self.err(b, j, "sp lowered by an unknown amount"),
                },
                Inst::Mov {
                    sf: Sf::X,
                    d,
                    n: Reg::SP,
                } if d == x16 && !realigned => {
                    // A snapshot of the lowered `sp`, for the realignment that must follow.
                    constant = None;
                    holds_sp = true;
                }
                Inst::AluImm {
                    op: AluImmOp::And,
                    sf: Sf::X,
                    d: Reg::SP,
                    n,
                    imm,
                } if n == x16 => {
                    // Realignment: `sp` becomes the snapshot rounded down to the input's alignment,
                    // which only lowers it. Anything else in x16 would put `sp` anywhere.
                    let align = i64::from(self.input.frame.align);
                    if !holds_sp || realigned {
                        return self.err(
                            b,
                            j,
                            "sp realigned from an x16 that isn't a snapshot of sp",
                        );
                    }
                    if align <= 16 || !(align as u64).is_power_of_two() || imm != -align {
                        return self.err(
                            b,
                            j,
                            format!("sp realigned to {imm}, but the frame needs alignment {align}"),
                        );
                    }
                    realigned = true;
                    self.realigned = true;
                }
                _ => break,
            }
            j += 1;
        }
        // x16 held a constant or a snapshot of `sp`: no input value, and no spill address.
        st.set_reg(x16, Vec::new());
        self.frame = Some(size);
        Ok(j - start)
    }

    /// Check the input instruction `o` against its output `t`, and apply it to the state.
    fn step(&mut self, st: &mut State, o: Inst, t: Inst, b: usize, j: usize) -> Result<(), String> {
        if shape(o) != shape(t) {
            return self.err(
                b,
                j,
                format!("doesn't correspond to input instruction {o:?}"),
            );
        }
        let [mut od, mut ou, mut td, mut tu] = std::mem::take(&mut self.bufs);
        let r = self.step_with(st, o, t, b, j, [&mut od, &mut ou, &mut td, &mut tu]);
        self.bufs = [od, ou, td, tu];
        r
    }

    fn step_with(
        &mut self,
        st: &mut State,
        o: Inst,
        t: Inst,
        b: usize,
        j: usize,
        [od, ou, td, tu]: [&mut Vec<Reg>; 4],
    ) -> Result<(), String> {
        o.regs(od, ou);
        t.regs(td, tu);
        let (od, ou, td, tu) = (&od[..], &ou[..], &td[..], &tu[..]);
        // Physical registers of the input stay; virtual ones become physical registers of their
        // class (`vN` an `x`, `fvN` a `d`).
        for (&a, &c) in od.iter().zip(td).chain(ou.iter().zip(tu)) {
            if a.is_virtual() {
                if !(if a.is_fp() { c.is_fpr() } else { c.is_gpr() }) {
                    return self.err(b, j, format!("{a} became {c}, a register of another kind"));
                }
            } else if a != c {
                return self.err(b, j, format!("the input's {a} became {c}"));
            }
        }
        // Reads, explicit and those of calls and returns under the convention.
        effects(self.input, &self.shapes, o, &mut self.fx);
        let implicit: Vec<Reg> = self.fx.uses[ou.len()..].to_vec();
        if o == Inst::Ret {
            for p in callee_saved() {
                if self.regs_hold(st, p, ENTRY + p).is_none() {
                    return self.err(
                        b,
                        j,
                        format!(
                            "{} doesn't hold its value at entry at the return",
                            reg_name(p)
                        ),
                    );
                }
            }
        }
        for (&a, &c) in ou.iter().zip(tu).chain(implicit.iter().zip(&implicit)) {
            if let Some(v) = val(a)
                && !st.holds(c, v)
            {
                return self.err(
                    b,
                    j,
                    format!("reads {} from {c}, which holds {:?}", show(v), {
                        let s: Vec<String> = st.get(c).iter().map(|&x| show(x)).collect();
                        s
                    }),
                );
            }
        }
        // The input's own memory accesses stay out of the spill and save areas.
        match o {
            Inst::Ldr { base, off, .. } | Inst::Str { base, off, .. }
                if self.framed
                    && ((base == Reg::SP && off >= self.spill_base)
                        || (base == Reg::FP && off < 0)) =>
            {
                return self.err(b, j, "the input itself accesses the spill or save area");
            }
            _ => {}
        }
        if o == (Inst::Mov {
            sf: Sf::X,
            d: Reg::SP,
            n: Reg::FP,
        }) {
            // The epilogue: from here `sp` addresses the saved x29 and x30.
            self.framed = false;
        }
        // Writes. A move copies what its source holds.
        let copied = match (as_move(o), as_move(t)) {
            (Some(_), Some((_, n))) => st.get(n),
            _ => Vec::new(),
        };
        for (&a, &c) in od.iter().zip(td) {
            if let Some(v) = val(a) {
                st.kill(v);
                let mut s = copied.clone();
                insert(&mut s, v);
                st.set_reg(c, s);
            } else {
                st.set_reg(c, Vec::new());
            }
        }
        // After an input move `d ← n`, `d` has `n`'s value, so every other location holding `n`
        // holds `d` too, as when the move is left out. Without this, a kept move matched to the
        // output move of a later left-out one (they look alike) would lose `d`'s spill slot.
        if let Some((d, n)) = as_move(o)
            && let (Some(dv), Some(nv)) = (val(d), val(n))
            && dv != nv
            && as_move(t).is_some()
        {
            for s in st.regs.iter_mut().chain(st.slots.values_mut()) {
                if s.binary_search(&nv).is_ok() {
                    insert(s, dv);
                }
            }
        }
        // The exception pseudo-instructions address the exception slot through x16 when emitted
        // (`emit.rs`): x16 holds nothing afterwards, not even a spill address, and can't be
        // their operand.
        if matches!(
            o,
            Inst::ExnSet { .. } | Inst::ExnTake { .. } | Inst::BExn { .. }
        ) {
            if matches!(t, Inst::ExnSet { n } | Inst::ExnTake { d: n } if n == Reg::x(16)) {
                return self.err(
                    b,
                    j,
                    "an exception pseudo-instruction's operand is x16, which it clobbers",
                );
            }
            st.set_reg(Reg::x(16), Vec::new());
        }
        if o.is_call() {
            let clobbered = CALLER_SAVED
                .iter()
                .map(|&r| Reg::x(r))
                .chain(FP_CALLER_SAVED.iter().map(|&r| Reg::d(r)));
            for r in clobbered {
                let v = val(r).unwrap();
                st.kill(v);
                st.set_reg(r, vec![v]);
            }
        }
        Ok(())
    }

    /// One block from its entry state; the state at its end.
    ///
    /// An input `mov` between virtual registers may have been left out or kept, and when the
    /// next output instruction is a move too, which one it is shows only later. The walk tries
    /// "kept" first and comes back to "left out" when that fails (a choice point), within a
    /// budget proportional to the block's size; the first error found is reported.
    fn block(&mut self, b: usize, st: State) -> Result<State, String> {
        let ir = self.input.block_range(b);
        let or = self.out.block_range(b);
        let mut choices: Vec<(usize, usize, State, i64, i64, Option<u64>)> = Vec::new();
        let mut budget = 16 * (ir.len() + or.len()) + 16;
        // The error of the branch that got furthest: a wrong choice usually fails at once.
        let mut best: Option<(usize, String)> = None;
        let (mut i, mut j, mut st) = (ir.start, or.start, st);
        let mut elide_next = false;
        self.framed = b != 0;
        let framed0 = self.framed;
        loop {
            let r = self.walk(b, &mut i, &mut j, &mut st, &mut elide_next, &mut choices);
            match r {
                Ok(()) => return Ok(st),
                Err(e) => {
                    if best.as_ref().is_none_or(|(at, _)| j > *at) {
                        best = Some((j, e));
                    }
                    let Some((ci, cj, cst, se, sl, fr)) = choices.pop() else {
                        return Err(best.unwrap().1);
                    };
                    if budget == 0 {
                        return Err(best.unwrap().1);
                    }
                    budget -= 1;
                    (i, j, st) = (ci, cj, cst);
                    (self.spill_end, self.save_low, self.frame) = (se, sl, fr);
                    // Choice points are never in the prologue or the epilogue's tail.
                    self.framed = framed0 || (b == 0 && i > self.input.frame.alloc_at as usize);
                    elide_next = true;
                }
            }
        }
    }

    /// Walk the block from `i` and `j` to its end, recording choice points.
    #[allow(clippy::type_complexity)]
    fn walk(
        &mut self,
        b: usize,
        i: &mut usize,
        j: &mut usize,
        st: &mut State,
        elide_next: &mut bool,
        choices: &mut Vec<(usize, usize, State, i64, i64, Option<u64>)>,
    ) -> Result<(), String> {
        let ir = self.input.block_range(b);
        let or = self.out.block_range(b);
        loop {
            if *j < or.end
                && let Some(ins) = self.classify(st, self.out.insts[*j])
            {
                self.apply_inserted(st, ins, b, *j)?;
                *j += 1;
                continue;
            }
            if *i >= ir.end {
                if *j < or.end {
                    return self.err(b, *j, "an instruction the input doesn't have");
                }
                return Ok(());
            }
            let o = self.input.insts[*i];
            if b == 0 && *i == self.input.frame.alloc_at as usize {
                *j += self.frame_alloc(st, b, *j, or.end)?;
                self.framed = true;
                *i += 1;
                // Selection's realignment after the placeholder is part of it: the output's
                // frame allocation must have realigned in its place.
                if super::regalloc::placeholder_realign(self.input) {
                    if !self.realigned {
                        return self.err(
                            b,
                            *j,
                            "the input realigns sp, but the output's frame doesn't",
                        );
                    }
                    *i += 2;
                }
                continue;
            }
            let t = (*j < or.end).then(|| self.out.insts[*j]);
            // The rewriting leaves out a 64-bit move whose two registers got the same home, which
            // needs one of them to be virtual.
            let elidable = matches!(as_move(o), Some((d, n))
                if (d.is_virtual() || n.is_virtual()) && val(d).is_some() && val(n).is_some());
            let elide = std::mem::take(elide_next);
            match t {
                Some(t) if shape(o) == shape(t) && !elide => {
                    // Leaving `o` out instead can explain `t` only if `t` stands for a later input
                    // instruction of the same shape that every instruction in between leaves out
                    // too (left-out moves): only then is this a real choice.
                    let next_is_move = elidable && {
                        let mut k = *i + 1;
                        while k < ir.end
                            && shape(self.input.insts[k]) != shape(t)
                            && as_move(self.input.insts[k]).is_some()
                        {
                            k += 1;
                        }
                        k < ir.end && shape(self.input.insts[k]) == shape(t)
                    };
                    if elidable && next_is_move {
                        choices.push((
                            *i,
                            *j,
                            st.clone(),
                            self.spill_end,
                            self.save_low,
                            self.frame,
                        ));
                    }
                    // A move with another location might be the next input move after this
                    // one was elided. Register that alternative before rejecting this match.
                    if self.input.locs[*i] != self.out.locs[*j] {
                        return self.err(b, *j, "an instruction's source location changed");
                    }
                    self.step(st, o, t, b, *j)?;
                    *i += 1;
                    *j += 1;
                }
                _ if elidable => {
                    let Some((d, n)) = as_move(o) else {
                        unreachable!()
                    };
                    // Left out: `d` now lives wherever `n` does.
                    let (Some(dv), Some(nv)) = (val(d), val(n)) else {
                        unreachable!()
                    };
                    st.kill(dv);
                    let mut any = false;
                    for s in st.regs.iter_mut().chain(st.slots.values_mut()) {
                        if s.binary_search(&nv).is_ok() {
                            insert(s, dv);
                            any = true;
                        }
                    }
                    if !any {
                        return self.err(
                            b,
                            *j,
                            format!("a left-out move from {}, which no location holds", show(nv)),
                        );
                    }
                    *i += 1;
                }
                _ => {
                    return self.err(
                        b,
                        *j,
                        format!("input instruction {} ({o:?}) has no counterpart", *i),
                    );
                }
            }
        }
    }
}

/// A validated output, owned until it is committed to its exclusively borrowed input. The ABI
/// shapes stay borrowed too. There is no way to commit other output or choose another input.
///
/// This compiles (it isn't run: an empty function doesn't validate):
/// ```no_run
/// use fir::backend::aarch64::{abi::CallShape, mir::MFunc, regcheck};
/// let mut input = MFunc::default();
/// let (mut other, mut out, own) = (input.clone(), input.clone(), CallShape::default());
/// let mut shapes = vec![CallShape::default()];
/// let accepted = regcheck::validate(&mut input, out.clone(), &shapes, &own).unwrap();
/// accepted.apply();
/// let _ = (&mut other, &mut out, &mut shapes);
/// ```
/// Each of the following differs from it in one line, and doesn't compile (stable `rustdoc`
/// doesn't check the error codes, so the compiling twin is what shows the line is the reason).
/// The checked input can't change before committing:
/// ```compile_fail,E0506
/// use fir::backend::aarch64::{abi::CallShape, mir::MFunc, regcheck};
/// let mut input = MFunc::default();
/// let (mut other, mut out, own) = (input.clone(), input.clone(), CallShape::default());
/// let mut shapes = vec![CallShape::default()];
/// let accepted = regcheck::validate(&mut input, out.clone(), &shapes, &own).unwrap();
/// input.index = 7; accepted.apply();
/// let _ = (&mut other, &mut out, &mut shapes);
/// ```
/// The approval commits only to the input it checked:
/// ```compile_fail,E0061
/// use fir::backend::aarch64::{abi::CallShape, mir::MFunc, regcheck};
/// let mut input = MFunc::default();
/// let (mut other, mut out, own) = (input.clone(), input.clone(), CallShape::default());
/// let mut shapes = vec![CallShape::default()];
/// let accepted = regcheck::validate(&mut input, out.clone(), &shapes, &own).unwrap();
/// accepted.apply(&mut other);
/// let _ = (&mut other, &mut out, &mut shapes);
/// ```
/// The ABI context can't change before committing:
/// ```compile_fail,E0502
/// use fir::backend::aarch64::{abi::CallShape, mir::MFunc, regcheck};
/// let mut input = MFunc::default();
/// let (mut other, mut out, own) = (input.clone(), input.clone(), CallShape::default());
/// let mut shapes = vec![CallShape::default()];
/// let accepted = regcheck::validate(&mut input, out.clone(), &shapes, &own).unwrap();
/// shapes[0] = CallShape::default(); accepted.apply();
/// let _ = (&mut other, &mut out, &mut shapes);
/// ```
/// Committing consumes the approval:
/// ```compile_fail,E0382
/// use fir::backend::aarch64::{abi::CallShape, mir::MFunc, regcheck};
/// let mut input = MFunc::default();
/// let (mut other, mut out, own) = (input.clone(), input.clone(), CallShape::default());
/// let mut shapes = vec![CallShape::default()];
/// let accepted = regcheck::validate(&mut input, out.clone(), &shapes, &own).unwrap();
/// accepted.apply(); accepted.apply();
/// let _ = (&mut other, &mut out, &mut shapes);
/// ```
#[derive(Debug)]
#[must_use = "apply the validated output, or drop it to leave the input unchanged"]
pub struct Accepted<'a> {
    input: &'a mut MFunc,
    out: MFunc,
    _shapes: &'a [CallShape],
    _own: &'a CallShape,
}

impl Accepted<'_> {
    /// Commit exactly the validated output to exactly the input it was checked against.
    pub fn apply(self) {
        *self.input = self.out;
    }
}

/// Validate `out`, the code register allocation and frame lowering made from `input` (see the
/// module documentation). `shapes` gives each callee's argument and result registers; `own` is
/// the function's own. Neither code nor ABI context can change before the returned
/// approval is consumed. Refusal or dropping an approval leaves `input` untouched.
pub fn validate<'a>(
    input: &'a mut MFunc,
    out: MFunc,
    shapes: &'a [CallShape],
    own: &'a CallShape,
) -> Result<Accepted<'a>, String> {
    check(input, &out, shapes, own)?;
    Ok(Accepted {
        input,
        out,
        _shapes: shapes,
        _own: own,
    })
}

fn check(input: &MFunc, out: &MFunc, callees: &[CallShape], own: &CallShape) -> Result<(), String> {
    if input.index != out.index {
        return Err("the output belongs to a different function index".to_owned());
    }
    if input.sigs != out.sigs {
        return Err("the indirect-call signatures changed".to_owned());
    }
    let (a, b) = (input.frame, out.frame);
    if (
        a.outgoing,
        a.locals,
        a.align,
        a.alloc_at,
        a.exit,
        input.nvregs,
    ) != (
        b.outgoing, b.locals, b.align, b.alloc_at, b.exit, out.nvregs,
    ) {
        return Err("the input's frame layout or virtual-register count changed".to_owned());
    }
    if input.locs.len() != input.insts.len() || out.locs.len() != out.insts.len() {
        return Err("instruction and source-location counts differ".to_owned());
    }
    let nb = input.blocks.len();
    if nb == 0 {
        return Err("the input has no entry block".to_owned());
    }
    if out.blocks.len() != nb {
        return Err(format!(
            "function {}: {} blocks became {}",
            out.index,
            nb,
            out.blocks.len()
        ));
    }
    let fr = input.frame;
    let mut ck = Checker {
        input,
        out,
        shapes: Shapes { callees, own },
        spill_base: i64::from(fr.outgoing) + i64::from(fr.locals),
        spill_end: i64::from(fr.outgoing) + i64::from(fr.locals),
        save_low: 0,
        frame: None,
        framed: false,
        realigned: false,
        bufs: Default::default(),
        fx: Effects {
            defs: Vec::new(),
            uses: Vec::new(),
        },
    };
    let succ = |f: &MFunc, b: usize| -> Vec<u32> {
        let r = f.block_range(b);
        match r.end.checked_sub(1).map(|e| f.insts[e]) {
            Some(Inst::B { t }) => vec![t],
            Some(Inst::BCond { t, f, .. } | Inst::BExn { t, f }) => vec![t, f],
            _ => vec![],
        }
    };
    let mut at_start: Vec<Option<State>> = vec![None; nb];
    at_start[0] = Some(State::entry());
    let mut work = vec![0usize];
    let mut visits = 0usize;
    while let Some(b) = work.pop() {
        visits += 1;
        if visits > 64 * nb + 64 {
            return Err(format!(
                "function {}: the dataflow doesn't settle",
                out.index
            ));
        }
        let st = ck.block(b, at_start[b].clone().unwrap())?;
        if succ(input, b) != succ(out, b) {
            return Err(format!(
                "function {}: block {b} branches elsewhere",
                out.index
            ));
        }
        for s in succ(out, b) {
            let s = s as usize;
            let merged = match &at_start[s] {
                None => st.clone(),
                Some(old) => old.join(&st),
            };
            if at_start[s].as_ref() != Some(&merged) {
                at_start[s] = Some(merged);
                work.push(s);
            }
        }
    }
    // The frame: outgoing arguments, locals, spill slots, then saves up to x29.
    let saves = -ck.save_low;
    let need = ck.spill_end + saves;
    match ck.frame {
        Some(size) if size as i64 >= need && size % 16 == 0 => Ok(()),
        Some(size) => Err(format!(
            "function {}: the frame is {size} bytes, but the locals and spill slots end at {} and \
             the saves take {saves} (or the size isn't a multiple of 16)",
            out.index, ck.spill_end
        )),
        None if at_start[0].is_some() => Err(format!(
            "function {}: the prologue's frame allocation wasn't found",
            out.index
        )),
        None => Ok(()),
    }
}
