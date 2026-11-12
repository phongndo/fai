//! Register allocation (linear scan with spilling) and frame lowering.
//!
//! **Intervals.** Instruction `i` reads its registers at position `2i` and writes them at
//! `2i + 1`. A virtual register's interval is the hull of its reads and writes and of the
//! block boundaries where it is live (liveness is a backward dataflow over the blocks, on
//! sparse sets), so it has no holes: simple and conservative. Physical registers the code names
//! before allocation (argument and result registers around calls, the return registers, and
//! every caller-saved register a call writes) get exact segments instead; a virtual register
//! may only take a physical register none of whose segments overlap its interval, which keeps
//! values live across a call out of caller-saved registers and arguments from being clobbered
//! while the others are set up.
//!
//! **Allocation.** There are two register classes, general-purpose (`x`) and FP/SIMD (`d`), and
//! a virtual register's class is its name's (`vN` or `fvN`); each takes registers of its own
//! class. Intervals in order of their start take a free register, preferring one a move to or
//! from a physical register suggests, then caller-saved ones for intervals that cross no call.
//! With none free, the active interval of the same class that ends last and whose register
//! suits is spilled if it ends after the new one; otherwise the new one is. A spilled register
//! lives in its own 8-byte slot: each read loads it into a scratch register of its class (`x15`,
//! then `x17`; `d29`, `d30`, then `d31`) just before, each write stores it just after. `x16`
//! computes far slot addresses; `x18` (the platform register), `x29`, `x30`, and the FP scratch
//! registers are never allocated. Calls clobber AAPCS64's caller-saved registers: `x0`…`x18`,
//! `x30`, `d0`…`d7`, and `d16`…`d31` (FIR keeps only 64 bits in an FP register, so `d8`…`d15`
//! survive calls).
//!
//! **The certificate** a checker would validate is the assignment ([`Assignment`]: each
//! virtual register's physical register or spill slot) with the code before allocation. The
//! check ([`check`]) first requires every virtual register the code names to have a home it may
//! have: a register of its own class that allocation uses (never a scratch register, `x16`,
//! `x18`, `x29`, `x30`, `sp`, or `xzr`), or a slot of its own below the slot count. Then a
//! forward dataflow over the original code tracks which virtual register each physical register
//! holds (a write takes the register, a call clobbers the caller-saved ones, a write of a
//! physical register by name takes it from any virtual one), met by intersection at joins:
//! every read of a virtual register must find its physical register holding it. Spill slots
//! belong to one virtual register each, so they always do.
//! It runs on every allocation in debug builds; proving it in Lean is the trust round's.
//!
//! **Frame lowering** then fills in the prologue's frame size (the callee-saved registers the
//! allocation used, the spill slots, the locals, and the outgoing arguments), realigns `sp` when
//! a local needs more than 16 bytes, and saves and restores the callee-saved registers
//! (`x19`…`x28`, and the low 64 bits of `d8`…`d15`).

use super::abi::{CallShape, FP_CALLER_SAVED};
use super::mir::{CALLER_SAVED, Inst, MFunc};
use crate::ir::{AluImmOp, AluOp, FSize, FUnaryOp, MemSize, MovOp, Reg, Sf};

/// The general-purpose registers allocation may use, caller-saved first.
const ALLOCATABLE: [u32; 25] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
];
/// The FP registers allocation may use, caller-saved first.
const ALLOCATABLE_FP: [u32; 29] = [
    0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 8, 9, 10, 11, 12,
    13, 14, 15,
];
/// Scratch registers for spilled values, and for far slot addresses.
const SCRATCH: [u32; 2] = [15, 17];
const SCRATCH_FP: [u32; 3] = [29, 30, 31];
const ADDR: u32 = 16;

/// Physical registers by index: `x0`…`x30` are 0…30, `d0`…`d31` are 31…62.
const FP_BASE: u32 = 31;

fn phys_reg(p: u32) -> Reg {
    if p < FP_BASE {
        Reg::x(p)
    } else {
        Reg::d(p - FP_BASE)
    }
}

/// A physical register's index, if it is one allocation tracks.
fn phys(r: Reg) -> Option<u32> {
    if r.is_gpr() {
        Some(r.0)
    } else if r.is_fpr() {
        Some(FP_BASE + r.fpr_index())
    } else {
        None
    }
}

fn is_callee_saved(p: u32) -> bool {
    (19..=28).contains(&p) || (FP_BASE + 8..=FP_BASE + 15).contains(&p)
}

/// Where each virtual register lives after allocation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Home {
    Reg(Reg),
    /// A spill slot: its index (8 bytes each, from the spill area's start).
    Slot(u32),
}

/// The allocation's result, by virtual register: the certificate.
#[derive(Clone, Debug, Default)]
pub struct Assignment {
    pub homes: Vec<Home>,
    pub slots: u32,
}

/// The number of physical registers tracked (`x0`…`x30`, `d0`…`d31`).
const NPHYS: usize = 63;

/// A register's index in the liveness sets: physical registers first, then virtual ones.
fn key(r: Reg) -> Option<u32> {
    if r.is_virtual() {
        Some(NPHYS as u32 + r.virt_index())
    } else {
        phys(r)
    }
}

/// The registers each instruction reads and writes, calls included.
struct Effects {
    defs: Vec<Reg>,
    uses: Vec<Reg>,
}

/// The calls the code makes and the function's own results: what [`effects`] needs.
struct Shapes<'a> {
    callees: &'a [CallShape],
    own: &'a CallShape,
}

fn effects(f: &MFunc, sh: &Shapes<'_>, i: Inst, out: &mut Effects) {
    i.regs(&mut out.defs, &mut out.uses);
    let indirect;
    let shape = match i {
        Inst::Bl { func } => &sh.callees[func as usize],
        Inst::Blr { sig, .. } => {
            let (p, r) = &f.sigs[sig as usize];
            indirect = CallShape::of(p, r);
            &indirect
        }
        Inst::BlAlloc { .. } | Inst::BlFree { .. } => {
            out.uses.push(Reg::x(0));
            out.defs.extend(CALLER_SAVED.iter().map(|&r| Reg::x(r)));
            out.defs.extend(FP_CALLER_SAVED.iter().map(|&r| Reg::d(r)));
            return;
        }
        Inst::Ret => {
            // `ret` reads the result registers; the frame lowering keeps the rest.
            out.uses.extend_from_slice(&sh.own.rets);
            return;
        }
        _ => return,
    };
    out.uses.extend_from_slice(&shape.args);
    if shape.area {
        out.uses.push(Reg::x(8));
    }
    out.defs.extend(CALLER_SAVED.iter().map(|&r| Reg::x(r)));
    out.defs.extend(FP_CALLER_SAVED.iter().map(|&r| Reg::d(r)));
}

/// Allocate registers for `f`, rewriting it in place, then lower its frame. `shapes` gives each
/// callee's argument and result registers; `own` the function's own.
pub fn allocate(f: &mut MFunc, shapes: &[CallShape], own: &CallShape) -> Assignment {
    let sh = Shapes {
        callees: shapes,
        own,
    };
    let a = assign(f, &sh);
    if cfg!(debug_assertions)
        && let Err(e) = check(f, &sh, &a)
    {
        panic!("register allocation of function {} is wrong: {e}", f.index);
    }
    rewrite(f, &a);
    lower_frame(f);
    a
}

/// Each block's successors.
fn successors(f: &MFunc) -> Vec<Vec<u32>> {
    (0..f.blocks.len())
        .map(|b| {
            let r = f.block_range(b);
            match f.insts[r.end - 1] {
                Inst::B { t } => vec![t],
                Inst::BCond { t, f, .. } | Inst::BExn { t, f } => vec![t, f],
                _ => vec![],
            }
        })
        .collect()
}

/// Sorted-vector set union: `a ∪ b` into `out`.
fn union(a: &[u32], b: &[u32], out: &mut Vec<u32>) {
    out.clear();
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            std::cmp::Ordering::Less => {
                out.push(a[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                out.push(a[i]);
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
}

/// The blocks in postorder from the entry (unreachable ones last).
fn postorder(succ: &[Vec<u32>]) -> Vec<usize> {
    let n = succ.len();
    let mut post = Vec::with_capacity(n);
    let mut seen = vec![false; n];
    for root in 0..n {
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut stack = vec![(root, 0usize)];
        while let Some((b, k)) = stack.last_mut() {
            let b = *b;
            match succ[b].get(*k) {
                Some(&s) => {
                    *k += 1;
                    if !seen[s as usize] {
                        seen[s as usize] = true;
                        stack.push((s as usize, 0));
                    }
                }
                None => {
                    post.push(b);
                    stack.pop();
                }
            }
        }
    }
    post
}

/// Live-in and live-out sets per block (sorted keys): a backward dataflow, iterated in
/// postorder so that it settles in a few rounds.
fn liveness(f: &MFunc, sh: &Shapes<'_>) -> (Vec<Vec<u32>>, Vec<Vec<u32>>) {
    let nb = f.blocks.len();
    let succ = successors(f);
    let mut gen_: Vec<Vec<u32>> = vec![Vec::new(); nb];
    let mut kill: Vec<Vec<u32>> = vec![Vec::new(); nb];
    let mut fx = Effects {
        defs: Vec::new(),
        uses: Vec::new(),
    };
    // Per key, the last block (plus one) that wrote it, and that read it before writing it.
    let nkeys = NPHYS + f.nvregs as usize;
    let mut wrote = vec![0u32; nkeys];
    let mut read = vec![0u32; nkeys];
    for b in 0..nb {
        let stamp = b as u32 + 1;
        let (g, k) = (&mut gen_[b], &mut kill[b]);
        for i in f.block_range(b) {
            effects(f, sh, f.insts[i], &mut fx);
            for &u in &fx.uses {
                if let Some(x) = key(u)
                    && wrote[x as usize] != stamp
                    && read[x as usize] != stamp
                {
                    read[x as usize] = stamp;
                    g.push(x);
                }
            }
            for &d in &fx.defs {
                if let Some(x) = key(d)
                    && wrote[x as usize] != stamp
                {
                    wrote[x as usize] = stamp;
                    k.push(x);
                }
            }
        }
        g.sort_unstable();
        k.sort_unstable();
    }
    let order = postorder(&succ);
    let mut live_in: Vec<Vec<u32>> = gen_.clone();
    let mut live_out: Vec<Vec<u32>> = vec![Vec::new(); nb];
    let mut tmp = Vec::new();
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &order {
            let mut out: Vec<u32> = Vec::new();
            for &s in &succ[b] {
                union(&out, &live_in[s as usize], &mut tmp);
                std::mem::swap(&mut out, &mut tmp);
            }
            if out != live_out[b] {
                // live_in = gen ∪ (out − kill)
                let rest: Vec<u32> = out
                    .iter()
                    .copied()
                    .filter(|x| kill[b].binary_search(x).is_err())
                    .collect();
                union(&gen_[b], &rest, &mut tmp);
                if tmp != live_in[b] {
                    std::mem::swap(&mut live_in[b], &mut tmp);
                }
                live_out[b] = out;
                changed = true;
            }
        }
    }
    (live_in, live_out)
}

#[derive(Clone, Copy)]
struct Interval {
    vreg: u32,
    start: u32,
    end: u32,
    calls: bool,
    fp: bool,
}

fn assign(f: &MFunc, sh: &Shapes<'_>) -> Assignment {
    let nv = f.nvregs as usize;
    let (live_in, live_out) = liveness(f, sh);
    let mut start = vec![u32::MAX; nv];
    let mut end = vec![0u32; nv];
    let mut hint = vec![u32::MAX; nv];
    // Each virtual register's class.
    let mut fp = vec![false; nv];
    for &i in &f.insts {
        let mut note = |r: Reg, _| {
            if r.is_virtual() {
                fp[r.virt_index() as usize] = r.is_fp();
            }
            r
        };
        i.map_regs(&mut note);
    }
    // Physical segments: per register, (from, to) position pairs.
    let mut segs: Vec<Vec<(u32, u32)>> = vec![Vec::new(); NPHYS];
    let mut calls: Vec<u32> = Vec::new();
    let mut fx = Effects {
        defs: Vec::new(),
        uses: Vec::new(),
    };
    fn touch(v: usize, p: u32, start: &mut [u32], end: &mut [u32]) {
        start[v] = start[v].min(p);
        end[v] = end[v].max(p);
    }
    for b in 0..f.blocks.len() {
        let r = f.block_range(b);
        let (bs, be) = (2 * r.start as u32, 2 * (r.end as u32 - 1) + 1);
        // Physical registers: walk backward from the live-out set.
        let mut live_until = [u32::MAX; NPHYS];
        for &x in &live_out[b] {
            if (x as usize) < NPHYS {
                live_until[x as usize] = be;
            }
        }
        for i in r.clone().rev() {
            let inst = f.insts[i];
            effects(f, sh, inst, &mut fx);
            if inst.is_call() {
                calls.push(2 * i as u32 + 1);
            }
            let (u, d) = (2 * i as u32, 2 * i as u32 + 1);
            for &reg in &fx.defs {
                if let Some(x) = phys(reg) {
                    let x = x as usize;
                    let to = live_until[x];
                    segs[x].push((d, if to == u32::MAX { d } else { to }));
                    live_until[x] = u32::MAX;
                } else if reg.is_virtual() {
                    touch(reg.virt_index() as usize, d, &mut start, &mut end);
                }
            }
            for &reg in &fx.uses {
                if let Some(x) = phys(reg) {
                    let x = x as usize;
                    if live_until[x] == u32::MAX {
                        live_until[x] = u;
                    }
                } else if reg.is_virtual() {
                    touch(reg.virt_index() as usize, u, &mut start, &mut end);
                }
            }
            let moved = match inst {
                Inst::Mov { d, n, .. } => Some((d, n)),
                Inst::Funary {
                    op: FUnaryOp::Fmov,
                    d,
                    n,
                    ..
                } if d.is_fp() && n.is_fp() => Some((d, n)),
                _ => None,
            };
            if let Some((d, n)) = moved {
                if let (true, Some(p)) = (d.is_virtual(), phys(n)) {
                    hint[d.virt_index() as usize] = p;
                } else if let (true, Some(p)) = (n.is_virtual(), phys(d)) {
                    hint[n.virt_index() as usize] = p;
                }
            }
        }
        for (x, &to) in live_until.iter().enumerate() {
            if to != u32::MAX {
                segs[x].push((bs, to));
            }
        }
        for &x in &live_in[b] {
            if x as usize >= NPHYS {
                touch(x as usize - NPHYS, bs, &mut start, &mut end);
            }
        }
        for &x in &live_out[b] {
            if x as usize >= NPHYS {
                touch(x as usize - NPHYS, be, &mut start, &mut end);
            }
        }
    }
    calls.sort_unstable();
    for s in &mut segs {
        s.sort_unstable();
    }
    let crosses = |s: u32, e: u32| {
        let i = calls.partition_point(|&c| c < s);
        i < calls.len() && calls[i] <= e
    };
    let mut intervals: Vec<Interval> = (0..nv)
        .filter(|&v| start[v] != u32::MAX)
        .map(|v| Interval {
            vreg: v as u32,
            start: start[v],
            end: end[v],
            calls: crosses(start[v], end[v]),
            fp: fp[v],
        })
        .collect();
    intervals.sort_by_key(|i| (i.start, i.vreg));
    // Per register, the largest segment end so far, by segment start.
    let reach: Vec<Vec<u32>> = segs
        .iter()
        .map(|sg| {
            sg.iter()
                .scan(0u32, |m, &(_, b)| {
                    *m = (*m).max(b);
                    Some(*m)
                })
                .collect()
        })
        .collect();
    let fits = |r: u32, s: u32, e: u32| {
        let sg = &segs[r as usize];
        // Segments are sorted by start; one with start ≤ e and end ≥ s overlaps.
        let hi = sg.partition_point(|&(a, _)| a <= e);
        hi == 0 || reach[r as usize][hi - 1] < s
    };
    let mut homes = vec![Home::Slot(u32::MAX); nv];
    let mut slots = 0u32;
    // Active intervals with their registers, and which registers they hold.
    let mut active: Vec<(Interval, u32)> = Vec::new();
    let mut busy = [false; NPHYS];
    for cur in intervals {
        active.retain(|&(a, r)| {
            if a.end < cur.start {
                busy[r as usize] = false;
                false
            } else {
                true
            }
        });
        let ok = |r: u32| !busy[r as usize] && fits(r, cur.start, cur.end);
        // The class's registers, as physical indices.
        let base = if cur.fp { FP_BASE } else { 0 };
        let class: &[u32] = if cur.fp {
            &ALLOCATABLE_FP
        } else {
            &ALLOCATABLE
        };
        let regs = || class.iter().map(|&r| base + r);
        let h = hint[cur.vreg as usize];
        let pick = if h != u32::MAX && regs().any(|r| r == h) && ok(h) {
            Some(h)
        } else if cur.calls {
            regs().filter(|&r| is_callee_saved(r)).find(|&r| ok(r))
        } else {
            regs().find(|&r| ok(r))
        };
        match pick {
            Some(r) => {
                busy[r as usize] = true;
                homes[cur.vreg as usize] = Home::Reg(phys_reg(r));
                active.push((cur, r));
            }
            None => {
                // Steal from the active interval of the class that ends last, if its register
                // suits.
                let victim = active
                    .iter()
                    .enumerate()
                    .filter(|(_, (a, r))| {
                        a.fp == cur.fp && a.end > cur.end && fits(*r, cur.start, cur.end)
                    })
                    .max_by_key(|(_, (a, _))| a.end)
                    .map(|(i, _)| i);
                match victim {
                    Some(i) => {
                        let (v, r) = active.swap_remove(i);
                        homes[v.vreg as usize] = Home::Slot(slots);
                        slots += 1;
                        homes[cur.vreg as usize] = Home::Reg(phys_reg(r));
                        active.push((cur, r));
                    }
                    None => {
                        homes[cur.vreg as usize] = Home::Slot(slots);
                        slots += 1;
                    }
                }
            }
        }
    }
    Assignment { homes, slots }
}

/// Check that every virtual register the code names has a home it may have: a register of its
/// own class that allocation may use ([`ALLOCATABLE`], [`ALLOCATABLE_FP`]: never a scratch
/// register, `x16`, `x18`, `x29`, `x30`, `sp`, or `xzr`), or a spill slot below
/// [`Assignment::slots`] that no other virtual register has.
fn check_homes(f: &MFunc, a: &Assignment) -> Result<(), String> {
    // Each virtual register's class (`Some(true)` for FP), from the names the code uses.
    let mut class: Vec<Option<bool>> = vec![None; a.homes.len()];
    let mut bad = None;
    for &i in &f.insts {
        i.map_regs(|r, _| {
            if r.is_virtual() && bad.is_none() {
                match class.get_mut(r.virt_index() as usize) {
                    None => bad = Some(format!("{r} has no home")),
                    Some(c @ None) => *c = Some(r.is_fp()),
                    Some(Some(fp)) if *fp != r.is_fp() => {
                        bad = Some(format!(
                            "virtual register {} is named in both classes",
                            r.virt_index()
                        ))
                    }
                    Some(Some(_)) => {}
                }
            }
            r
        });
    }
    if let Some(e) = bad {
        return Err(e);
    }
    let mut slot_of: Vec<Option<usize>> = vec![None; a.slots as usize];
    for (v, (&h, c)) in a.homes.iter().zip(&class).enumerate() {
        let Some(fp) = *c else { continue };
        let name = if fp {
            Reg::fvirt(v as u32)
        } else {
            Reg::virt(v as u32)
        };
        match h {
            Home::Reg(r) => {
                let ok = if fp {
                    r.is_fpr() && ALLOCATABLE_FP.contains(&r.fpr_index())
                } else {
                    r.is_gpr() && ALLOCATABLE.contains(&r.0)
                };
                if !ok {
                    return Err(format!("{name} is assigned {r}, which it may not have"));
                }
            }
            Home::Slot(s) => match slot_of.get_mut(s as usize) {
                None => {
                    return Err(format!(
                        "{name} is assigned slot {s}, but there are {} slots",
                        a.slots
                    ));
                }
                Some(Some(w)) => {
                    return Err(format!(
                        "{name} is assigned slot {s}, which virtual register {w} has too"
                    ));
                }
                Some(o) => *o = Some(v),
            },
        }
    }
    Ok(())
}

/// Check an assignment against the code before allocation (see the module documentation).
fn check(f: &MFunc, sh: &Shapes<'_>, a: &Assignment) -> Result<(), String> {
    check_homes(f, a)?;
    const UNKNOWN: u32 = u32::MAX;
    const PHYS: u32 = u32::MAX - 1;
    let nb = f.blocks.len();
    let succ = successors(f);
    // What each physical register holds at each block's start (`None`: not reached yet).
    let mut at_start: Vec<Option<[u32; NPHYS]>> = vec![None; nb];
    at_start[0] = Some([PHYS; NPHYS]);
    let mut work = vec![0usize];
    let mut fx = Effects {
        defs: Vec::new(),
        uses: Vec::new(),
    };
    while let Some(b) = work.pop() {
        let mut st = at_start[b].unwrap();
        for i in f.block_range(b) {
            let inst = f.insts[i];
            effects(f, sh, inst, &mut fx);
            for &u in &fx.uses {
                if u.is_virtual()
                    && let Home::Reg(r) = a.homes[u.virt_index() as usize]
                    && st[phys(r).unwrap() as usize] != u.virt_index()
                {
                    return Err(format!(
                        "instruction {i} reads {u} from {r}, which holds something else"
                    ));
                }
            }
            for &d in &fx.defs {
                if d.is_virtual() {
                    if let Home::Reg(r) = a.homes[d.virt_index() as usize] {
                        st[phys(r).unwrap() as usize] = d.virt_index();
                    }
                } else if let Some(p) = phys(d) {
                    st[p as usize] = PHYS;
                }
            }
        }
        for &s in &succ[b] {
            let s = s as usize;
            let merged = match at_start[s] {
                None => st,
                Some(old) => {
                    let mut m = old;
                    for (x, y) in m.iter_mut().zip(st) {
                        if *x != y {
                            *x = UNKNOWN;
                        }
                    }
                    m
                }
            };
            if at_start[s] != Some(merged) {
                at_start[s] = Some(merged);
                work.push(s);
            }
        }
    }
    Ok(())
}

/// Rename registers and add spill code.
fn rewrite(f: &mut MFunc, a: &Assignment) {
    let spill_base = i64::from(f.frame.outgoing) + i64::from(f.frame.locals);
    f.frame.spills = (a.slots * 8).div_ceil(16) * 16;
    let (mut saved, mut saved_fp) = (0u32, 0u32);
    for h in &a.homes {
        if let Home::Reg(r) = *h {
            let p = phys(r).unwrap();
            if is_callee_saved(p) {
                if r.is_fp() {
                    saved_fp |= 1 << r.fpr_index();
                } else {
                    saved |= 1 << r.0;
                }
            }
        }
    }
    f.frame.saved = saved;
    f.frame.saved_fp = saved_fp;
    let mut out = Out::new(f);
    let mut defs = Vec::new();
    let mut uses = Vec::new();
    for b in 0..f.blocks.len() {
        out.start_block();
        for i in f.block_range(b) {
            let (inst, loc) = (f.insts[i], f.locs[i]);
            inst.regs(&mut defs, &mut uses);
            // Scratch registers for spilled reads, by class; a register both read and written
            // keeps one.
            let mut scratch: Vec<(Reg, Reg)> = Vec::new();
            let (mut ng, mut nf) = (0, 0);
            for &u in &uses {
                if u.is_virtual()
                    && let Home::Slot(s) = a.homes[u.virt_index() as usize]
                    && !scratch.iter().any(|&(v, _)| v == u)
                {
                    let t = if u.is_fp() {
                        nf += 1;
                        Reg::d(SCRATCH_FP[nf - 1])
                    } else {
                        ng += 1;
                        Reg::x(SCRATCH[ng - 1])
                    };
                    out.slot_access(true, t, spill_base + 8 * i64::from(s), loc);
                    scratch.push((u, t));
                }
            }
            let mut stores: Vec<(Reg, u32)> = Vec::new();
            let renamed = inst.map_regs(|r, is_def| {
                if !r.is_virtual() {
                    return r;
                }
                match a.homes[r.virt_index() as usize] {
                    Home::Reg(p) => p,
                    Home::Slot(s) => {
                        let first = if r.is_fp() {
                            Reg::d(SCRATCH_FP[0])
                        } else {
                            Reg::x(SCRATCH[0])
                        };
                        let t = scratch
                            .iter()
                            .find(|&&(v, _)| v == r)
                            .map_or(first, |&(_, t)| t);
                        if is_def {
                            stores.push((t, s));
                        }
                        t
                    }
                }
            });
            let same = match renamed {
                Inst::Mov { sf: Sf::X, d, n } => d == n,
                Inst::Funary {
                    op: FUnaryOp::Fmov,
                    fs: FSize::D,
                    d,
                    n,
                } => d == n,
                _ => false,
            };
            if !same {
                out.push(renamed, loc);
            }
            for (t, s) in stores {
                out.slot_access(false, t, spill_base + 8 * i64::from(s), loc);
            }
        }
    }
    out.finish(f);
}

/// A rebuilt instruction list.
struct Out {
    insts: Vec<Inst>,
    locs: Vec<Option<crate::ir::Loc>>,
    blocks: Vec<u32>,
}

impl Out {
    fn new(f: &MFunc) -> Out {
        Out {
            insts: Vec::with_capacity(f.insts.len() + f.insts.len() / 4),
            locs: Vec::with_capacity(f.insts.len() + f.insts.len() / 4),
            blocks: Vec::with_capacity(f.blocks.len()),
        }
    }

    fn start_block(&mut self) {
        self.blocks.push(self.insts.len() as u32);
    }

    fn push(&mut self, i: Inst, loc: Option<crate::ir::Loc>) {
        self.insts.push(i);
        self.locs.push(loc);
    }

    /// Put a 64-bit constant in `d`.
    fn mov_imm(&mut self, d: Reg, x: u64) {
        let mut first = true;
        for k in 0..4u8 {
            let part = (x >> (16 * k)) as u16;
            if part != 0 || (first && k == 3) {
                let op = if first { MovOp::Movz } else { MovOp::Movk };
                self.push(
                    Inst::MovWide {
                        op,
                        sf: Sf::X,
                        d,
                        imm: part,
                        hw: 16 * k,
                    },
                    None,
                );
                first = false;
            }
        }
    }

    /// Load (`load`) or store register `t` at `sp + off`, through `x16` when the offset doesn't
    /// fit the instruction.
    fn slot_access(&mut self, load: bool, t: Reg, off: i64, loc: Option<crate::ir::Loc>) {
        let (base, off) = if super::isel::is_mem_off(off, MemSize::X) {
            (Reg::SP, off)
        } else {
            let a = Reg::x(ADDR);
            self.mov_imm(a, off as u64);
            self.push(
                Inst::Alu {
                    op: AluOp::Add,
                    sf: Sf::X,
                    d: a,
                    n: Reg::SP,
                    m: a,
                },
                loc,
            );
            (a, 0)
        };
        let i = if load {
            Inst::Ldr {
                size: MemSize::X,
                d: t,
                base,
                off,
            }
        } else {
            Inst::Str {
                size: MemSize::X,
                s: t,
                base,
                off,
            }
        };
        self.push(i, loc);
    }

    fn finish(self, f: &mut MFunc) {
        f.insts = self.insts;
        f.locs = self.locs;
        f.blocks = self.blocks;
    }
}

/// Fill in the frame: its size, `sp`'s realignment, and the callee-saved registers' saves and
/// restores (at `x29 - 8`, `x29 - 16`, …: the general-purpose ones, then the FP ones' low 64
/// bits).
fn lower_frame(f: &mut MFunc) {
    let saved: Vec<Reg> = (19..=28)
        .filter(|r| f.frame.saved & (1 << r) != 0)
        .map(Reg::x)
        .chain(
            (8..=15)
                .filter(|r| f.frame.saved_fp & (1 << r) != 0)
                .map(Reg::d),
        )
        .collect();
    let csr = (8 * saved.len() as u32).div_ceil(16) * 16;
    let fr = f.frame;
    let size = u64::from(fr.outgoing + fr.locals + fr.spills + csr);
    let mut out = Out::new(f);
    let alloc_at = fr.alloc_at as usize;
    // The exit block, if a return is reachable.
    let exit_start = f
        .blocks
        .get(fr.exit as usize)
        .map_or(usize::MAX, |&s| s as usize);
    let mut b = 0;
    for i in 0..f.insts.len() {
        while b < f.blocks.len() && f.blocks[b] as usize == i {
            out.start_block();
            b += 1;
        }
        if i == exit_start {
            for (k, &r) in saved.iter().enumerate() {
                out.push(
                    Inst::Ldr {
                        size: MemSize::X,
                        d: r,
                        base: Reg::FP,
                        off: -8 * (k as i64 + 1),
                    },
                    None,
                );
            }
        }
        if i != alloc_at {
            out.push(f.insts[i], f.locs[i]);
            continue;
        }
        // `sub sp, sp, size`, then realignment, then the saves.
        let sub = |out: &mut Out, k: u64| {
            out.push(
                Inst::AluImm {
                    op: AluImmOp::Sub,
                    sf: Sf::X,
                    d: Reg::SP,
                    n: Reg::SP,
                    imm: k as i64,
                },
                None,
            )
        };
        if size < 4096 {
            if size > 0 {
                sub(&mut out, size);
            }
        } else if size < 1 << 24 {
            sub(&mut out, size & !0xfff);
            if size & 0xfff != 0 {
                sub(&mut out, size & 0xfff);
            }
        } else {
            let a = Reg::x(ADDR);
            out.mov_imm(a, size);
            out.push(
                Inst::Alu {
                    op: AluOp::Sub,
                    sf: Sf::X,
                    d: Reg::SP,
                    n: Reg::SP,
                    m: a,
                },
                None,
            );
        }
        if fr.align > 16 {
            let a = Reg::x(ADDR);
            out.push(
                Inst::Mov {
                    sf: Sf::X,
                    d: a,
                    n: Reg::SP,
                },
                None,
            );
            out.push(
                Inst::AluImm {
                    op: AluImmOp::And,
                    sf: Sf::X,
                    d: Reg::SP,
                    n: a,
                    imm: -i64::from(fr.align),
                },
                None,
            );
        }
        for (k, &r) in saved.iter().enumerate() {
            out.push(
                Inst::Str {
                    size: MemSize::X,
                    s: r,
                    base: Reg::FP,
                    off: -8 * (k as i64 + 1),
                },
                None,
            );
        }
    }
    out.finish(f);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn func(insts: Vec<Inst>, nvregs: u32) -> MFunc {
        MFunc {
            locs: vec![None; insts.len()],
            insts,
            blocks: vec![0],
            nvregs,
            ..MFunc::default()
        }
    }

    fn checks(f: &MFunc, rets: Vec<Reg>, homes: Vec<Home>, slots: u32) -> Result<(), String> {
        let own = CallShape {
            args: vec![],
            rets,
            area: false,
        };
        let sh = Shapes {
            callees: &[],
            own: &own,
        };
        check(f, &sh, &Assignment { homes, slots })
    }

    /// `fmov.imm.d fv0, 112; fneg.d fv1, fv0; fmov.d d0, fv1; ret`.
    fn fp_func() -> MFunc {
        let (v0, v1) = (Reg::fvirt(0), Reg::fvirt(1));
        func(
            vec![
                Inst::FmovImm {
                    fs: FSize::D,
                    d: v0,
                    imm: 112,
                },
                Inst::Funary {
                    op: FUnaryOp::Fneg,
                    fs: FSize::D,
                    d: v1,
                    n: v0,
                },
                Inst::Funary {
                    op: FUnaryOp::Fmov,
                    fs: FSize::D,
                    d: Reg::d(0),
                    n: v1,
                },
                Inst::Ret,
            ],
            2,
        )
    }

    /// `movz v0, 1; add v1, v0, v0; mov x0, v1; ret`.
    fn int_func() -> MFunc {
        let (v0, v1) = (Reg::virt(0), Reg::virt(1));
        func(
            vec![
                Inst::MovWide {
                    op: MovOp::Movz,
                    sf: Sf::X,
                    d: v0,
                    imm: 1,
                    hw: 0,
                },
                Inst::Alu {
                    op: AluOp::Add,
                    sf: Sf::X,
                    d: v1,
                    n: v0,
                    m: v0,
                },
                Inst::Mov {
                    sf: Sf::X,
                    d: Reg::x(0),
                    n: v1,
                },
                Inst::Ret,
            ],
            2,
        )
    }

    #[test]
    fn accepts_valid_homes() {
        let (f, d0) = (fp_func(), vec![Reg::d(0)]);
        let r = |r| Home::Reg(r);
        checks(&f, d0.clone(), vec![r(Reg::d(16)), r(Reg::d(8))], 0).unwrap();
        checks(&f, d0.clone(), vec![Home::Slot(1), Home::Slot(0)], 2).unwrap();
        let g = int_func();
        checks(&g, vec![Reg::x(0)], vec![r(Reg::x(19)), Home::Slot(0)], 1).unwrap();
        // What the allocator itself picks passes.
        let own = CallShape {
            args: vec![],
            rets: d0,
            area: false,
        };
        let sh = Shapes {
            callees: &[],
            own: &own,
        };
        check(&f, &sh, &assign(&f, &sh)).unwrap();
    }

    #[test]
    fn rejects_wrong_class() {
        // The reported case: the dataflow alone accepted it.
        let f = fp_func();
        let homes = vec![Home::Reg(Reg::x(0)), Home::Reg(Reg::x(1))];
        let e = checks(&f, vec![Reg::d(0)], homes, 0).unwrap_err();
        assert!(e.contains("fv0 is assigned x0"), "{e}");
        let g = int_func();
        let homes = vec![Home::Reg(Reg::d(0)), Home::Reg(Reg::d(1))];
        assert!(checks(&g, vec![Reg::x(0)], homes, 0).is_err());
        // A virtual register as a home.
        let homes = vec![Home::Reg(Reg::virt(0)), Home::Reg(Reg::x(1))];
        assert!(checks(&g, vec![Reg::x(0)], homes, 0).is_err());
    }

    #[test]
    fn rejects_reserved_registers() {
        let g = int_func();
        for r in [15, 16, 17, 18, 29, 30, 31, 32] {
            let homes = vec![Home::Reg(Reg(r)), Home::Reg(Reg::x(1))];
            assert!(checks(&g, vec![Reg::x(0)], homes, 0).is_err(), "x{r}");
        }
        let f = fp_func();
        for r in [29, 30, 31] {
            let homes = vec![Home::Reg(Reg::d(r)), Home::Reg(Reg::d(1))];
            assert!(checks(&f, vec![Reg::d(0)], homes, 0).is_err(), "d{r}");
        }
    }

    #[test]
    fn rejects_bad_slots() {
        let f = fp_func();
        let d0 = vec![Reg::d(0)];
        // Past the slot count.
        let e = checks(&f, d0.clone(), vec![Home::Slot(0), Home::Slot(1)], 1).unwrap_err();
        assert!(e.contains("slot 1"), "{e}");
        assert!(checks(&f, d0.clone(), vec![Home::Slot(u32::MAX), Home::Slot(0)], 1).is_err());
        // Shared.
        let e = checks(&f, d0.clone(), vec![Home::Slot(0), Home::Slot(0)], 2).unwrap_err();
        assert!(e.contains("has too"), "{e}");
        // Missing.
        assert!(checks(&f, d0, vec![Home::Slot(0)], 1).is_err());
    }
}
