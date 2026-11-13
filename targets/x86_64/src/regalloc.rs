//! Register allocation for x86-64: linear scan with spilling, as on AArch64 (see
//! `fir::backend::aarch64::regalloc`), over one register class.
//!
//! **Intervals.** Instruction `i` reads its registers at position `2i` and writes them at
//! `2i + 1`. A virtual register's interval is the hull of its reads, its writes, and the block
//! boundaries where it is live (a backward liveness dataflow over the blocks), so it has no
//! holes. Physical registers the code names (the argument and result registers of calls and of
//! the function, `rax` and `rdx` around division, `rcx` for shift amounts, and every
//! caller-saved register a call writes) instead occupy exactly the positions where they are
//! live or written; a virtual register may only take a physical register that is unoccupied
//! throughout its interval, which keeps values live across calls in callee-saved registers and
//! keeps an instruction's operands out of the registers it names.
//!
//! **Allocation.** Intervals in order of their start take a free register, preferring one that
//! a move to or from a physical register suggests, then caller-saved ones (`rax`, `rcx`, `rdx`,
//! `rsi`, `rdi`, `r8`, `r9`), then callee-saved ones (`rbx`, `r12`…`r15`). With none free, the
//! active interval that ends last and whose register suits is spilled if it ends after the new
//! one; otherwise the new one is. A spilled register lives in its own 8-byte slot: each read
//! loads it into a scratch register (`r10`, then `r11`, never allocated: no instruction names
//! more than two virtual registers) just before, each write stores it just after; loads and
//! stores are moves, so the flags an instruction reads survive them. `rsp` and `rbp` are never
//! allocated.
//!
//! **The check.** The assignment (each virtual register's register or slot) is checked on every
//! function, in every build, against the code before allocation: every virtual register must
//! have a home it may have (an allocatable register, or a slot of its own), and a forward
//! dataflow of what each physical register holds (a virtual register's value, or the value
//! written to it by name or held on entry: a write takes the register, a call writes the
//! caller-saved ones by name), met by intersection at joins, must find each read's value in its
//! register, whether the read names a virtual register or a physical one. It checks the assignment, not the rewriting, the spill code, or the frame, which
//! the native tests exercise; nothing here is proved in Lean.

use super::mir::*;

/// The registers allocation may use, caller-saved first.
const ALLOCATABLE: [u8; 12] = [0, 1, 2, 6, 7, 8, 9, 3, 12, 13, 14, 15];
/// Scratch registers for spilled values.
const SCRATCH: [Reg; 2] = [R10, R11];
const NPHYS: usize = 16;

/// Where a virtual register lives after allocation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Home {
    Reg(u8),
    /// A spill slot: its index (8 bytes each, from the spill area's start).
    Slot(u32),
    /// Named nowhere in the code.
    Unused,
}

/// The allocation's result, by virtual register: what [`check`] validates.
#[derive(Clone, Debug, Default)]
pub struct Assignment {
    pub homes: Vec<Home>,
    pub slots: u32,
}

/// The registers an instruction writes and reads, calls included: a call reads its argument
/// registers and writes every caller-saved register (its results among them); `ret` reads the
/// function's result registers.
pub fn effects(
    f: &MFunc,
    callees: &[CallShape],
    own: &CallShape,
    i: Inst,
    defs: &mut Vec<Reg>,
    uses: &mut Vec<Reg>,
) {
    i.regs(defs, uses);
    let args: &[Reg] = match i {
        Inst::Call { func } => &callees[func as usize].args,
        Inst::CallInd { sig, .. } => &f.sig_shapes[sig as usize].args,
        Inst::CallRt(rt) => rt.args(),
        Inst::Ret => {
            uses.extend_from_slice(&own.rets);
            return;
        }
        _ => return,
    };
    uses.extend_from_slice(args);
    defs.extend(CALLER_SAVED.iter().map(|&r| Reg::P(r)));
}

/// A register's index in the liveness sets: physical registers first, then virtual ones.
fn key(r: Reg) -> usize {
    match r {
        Reg::P(n) => n as usize,
        Reg::V(n) => NPHYS + n as usize,
    }
}

/// A dense bit set.
#[derive(Clone, PartialEq, Eq)]
struct Bits(Vec<u64>);

impl Bits {
    fn new(n: usize) -> Bits {
        Bits(vec![0; n.div_ceil(64)])
    }
    fn set(&mut self, i: usize) {
        self.0[i / 64] |= 1 << (i % 64);
    }
    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.0.iter().enumerate().flat_map(|(w, &x)| {
            let mut x = x;
            std::iter::from_fn(move || {
                if x == 0 {
                    return None;
                }
                let b = x.trailing_zeros() as usize;
                x &= x - 1;
                Some(w * 64 + b)
            })
        })
    }
}

fn successors(f: &MFunc) -> Vec<Vec<u32>> {
    (0..f.blocks.len())
        .map(|b| {
            let r = f.block_range(b);
            f.insts[r.end - 1].targets().collect()
        })
        .collect()
}

/// Each block's live-in and live-out registers, as sets over the registers that are live across
/// some block boundary (those a block reads before writing them, and every physical register):
/// bit `i` of a set is register key `keys[i]`. The rest live within a block, so the sets, whose
/// size is the blocks times this universe, stay small where most registers are local.
fn liveness(
    f: &MFunc,
    callees: &[CallShape],
    own: &CallShape,
) -> (Vec<Bits>, Vec<Bits>, Vec<usize>) {
    let nkeys = NPHYS + f.nvregs as usize;
    let nb = f.blocks.len();
    // Each block's upward-exposed reads, by key, deduplicated with per-key block stamps.
    let (mut defined, mut exposed) = (vec![usize::MAX; nkeys], vec![usize::MAX; nkeys]);
    let mut gen_lists: Vec<Vec<usize>> = vec![Vec::new(); nb];
    let (mut defs, mut uses) = (Vec::new(), Vec::new());
    for (b, list) in gen_lists.iter_mut().enumerate() {
        for i in f.block_range(b) {
            effects(f, callees, own, f.insts[i], &mut defs, &mut uses);
            for &u in &uses {
                let k = key(u);
                if defined[k] != b && exposed[k] != b {
                    exposed[k] = b;
                    list.push(k);
                }
            }
            for &d in &defs {
                defined[key(d)] = b;
            }
        }
    }
    // Physical registers keep their numbers as indices.
    let mut index: Vec<u32> = (0..nkeys)
        .map(|k| if k < NPHYS { k as u32 } else { u32::MAX })
        .collect();
    let mut keys: Vec<usize> = (0..NPHYS).collect();
    for &k in gen_lists.iter().flatten() {
        if index[k] == u32::MAX {
            index[k] = keys.len() as u32;
            keys.push(k);
        }
    }
    let n = keys.len();
    let mut gen_ = vec![Bits::new(n); nb];
    let mut kill = vec![Bits::new(n); nb];
    for b in 0..nb {
        for &k in &gen_lists[b] {
            gen_[b].set(index[k] as usize);
        }
        for i in f.block_range(b) {
            effects(f, callees, own, f.insts[i], &mut defs, &mut uses);
            for &d in &defs {
                let x = index[key(d)];
                if x != u32::MAX {
                    kill[b].set(x as usize);
                }
            }
        }
    }
    let succ = successors(f);
    let mut live_in = gen_.clone();
    let mut live_out = vec![Bits::new(n); nb];
    loop {
        let mut changed = false;
        for b in (0..nb).rev() {
            let mut out = Bits::new(n);
            for &s in &succ[b] {
                for (o, x) in out.0.iter_mut().zip(&live_in[s as usize].0) {
                    *o |= x;
                }
            }
            let mut inn = gen_[b].clone();
            for ((i, o), k) in inn.0.iter_mut().zip(&out.0).zip(&kill[b].0) {
                *i |= o & !k;
            }
            if inn != live_in[b] {
                live_in[b] = inn;
                changed = true;
            }
            live_out[b] = out;
        }
        if !changed {
            return (live_in, live_out, keys);
        }
    }
}

/// Range-or queries over each position's occupied physical registers.
struct Occupancy {
    levels: Vec<Vec<u16>>,
}

impl Occupancy {
    fn new(points: Vec<u16>) -> Occupancy {
        let mut levels = vec![points];
        let mut w = 1;
        while 2 * w <= levels[0].len() {
            let prev = levels.last().unwrap();
            let next = (0..prev.len() - w).map(|i| prev[i] | prev[i + w]).collect();
            levels.push(next);
            w *= 2;
        }
        Occupancy { levels }
    }

    /// The registers occupied anywhere in `lo..=hi`.
    fn range(&self, lo: usize, hi: usize) -> u16 {
        let len = hi - lo + 1;
        let k = (usize::BITS - 1 - len.leading_zeros()) as usize;
        let l = &self.levels[k];
        l[lo] | l[hi + 1 - (1 << k)]
    }
}

/// Allocate `f`'s virtual registers: the assignment, unchecked.
pub fn assign(f: &MFunc, callees: &[CallShape], own: &CallShape) -> Assignment {
    let nv = f.nvregs as usize;
    let mut homes = vec![Home::Unused; nv];
    if f.insts.is_empty() {
        return Assignment { homes, slots: 0 };
    }
    let (live_in, live_out, keys) = liveness(f, callees, own);
    let npoints = 2 * f.insts.len();
    let mut start = vec![usize::MAX; nv];
    let mut end = vec![0usize; nv];
    let mut occupied = vec![0u16; npoints];
    let mut hint: Vec<Option<u8>> = vec![None; nv];
    let touch = |v: usize, p: usize, start: &mut [usize], end: &mut [usize]| {
        start[v] = start[v].min(p);
        end[v] = end[v].max(p);
    };
    let (mut defs, mut uses) = (Vec::new(), Vec::new());
    for b in 0..f.blocks.len() {
        let r = f.block_range(b);
        let (first, last) = (2 * r.start, 2 * (r.end - 1) + 1);
        for k in live_in[b].iter().map(|i| keys[i]).filter(|&k| k >= NPHYS) {
            touch(k - NPHYS, first, &mut start, &mut end);
        }
        for k in live_out[b].iter().map(|i| keys[i]).filter(|&k| k >= NPHYS) {
            touch(k - NPHYS, last, &mut start, &mut end);
        }
        // Physical registers, backward through the block.
        let mut live: u16 = live_out[b]
            .iter()
            .take_while(|&k| k < NPHYS)
            .fold(0, |m, k| m | 1 << k);
        for i in r.rev() {
            let inst = f.insts[i];
            effects(f, callees, own, inst, &mut defs, &mut uses);
            let mut dmask = 0u16;
            for &d in &defs {
                match d {
                    Reg::P(p) => dmask |= 1 << p,
                    Reg::V(v) => touch(v as usize, 2 * i + 1, &mut start, &mut end),
                }
            }
            occupied[2 * i + 1] = live | dmask;
            live &= !dmask;
            for &u in &uses {
                match u {
                    Reg::P(p) => live |= 1 << p,
                    Reg::V(v) => touch(v as usize, 2 * i, &mut start, &mut end),
                }
            }
            occupied[2 * i] = live;
            if let Inst::Mov { d, s } = inst {
                match (d, s) {
                    (Reg::V(v), Reg::P(p)) | (Reg::P(p), Reg::V(v)) => hint[v as usize] = Some(p),
                    _ => {}
                }
            }
        }
    }
    let occ = Occupancy::new(occupied);
    let mut order: Vec<usize> = (0..nv).filter(|&v| start[v] != usize::MAX).collect();
    order.sort_by_key(|&v| (start[v], v));
    // Active intervals: (vreg, register).
    let mut active: Vec<(usize, u8)> = Vec::new();
    let mut slots = 0;
    let mut slot = |homes: &mut [Home], v: usize| {
        homes[v] = Home::Slot(slots);
        slots += 1;
    };
    for v in order {
        active.retain(|&(a, _)| end[a] >= start[v]);
        let forbidden = occ.range(start[v], end[v]);
        let taken = active.iter().fold(0u16, |m, &(_, r)| m | 1 << r);
        let ok = |r: u8| forbidden & (1 << r) == 0;
        let free = |r: u8| ok(r) && taken & (1 << r) == 0;
        let pick = hint[v]
            .filter(|&r| ALLOCATABLE.contains(&r) && free(r))
            .or_else(|| ALLOCATABLE.iter().copied().find(|&r| free(r)));
        if let Some(r) = pick {
            homes[v] = Home::Reg(r);
            active.push((v, r));
            continue;
        }
        // Spill whichever ends last: an active interval whose register suits, or this one.
        let victim = active
            .iter()
            .enumerate()
            .filter(|(_, (_, r))| ok(*r))
            .max_by_key(|(_, (a, _))| end[*a])
            .map(|(k, &(a, r))| (k, a, r));
        match victim {
            Some((k, a, r)) if end[a] > end[v] => {
                slot(&mut homes, a);
                active.swap_remove(k);
                homes[v] = Home::Reg(r);
                active.push((v, r));
            }
            _ => slot(&mut homes, v),
        }
    }
    Assignment { homes, slots }
}

/// Check that every virtual register the code names has a home it may have.
fn check_homes(f: &MFunc, a: &Assignment) -> Result<(), String> {
    if a.homes.len() != f.nvregs as usize {
        return Err(format!(
            "{} homes for {} virtual registers",
            a.homes.len(),
            f.nvregs
        ));
    }
    let mut seen = vec![false; a.slots as usize];
    let (mut defs, mut uses) = (Vec::new(), Vec::new());
    let mut named = vec![false; a.homes.len()];
    for &i in &f.insts {
        i.regs(&mut defs, &mut uses);
        for r in defs.iter().chain(&uses) {
            if let Reg::V(v) = *r {
                named[v as usize] = true;
            }
        }
    }
    for (v, &h) in a.homes.iter().enumerate() {
        match h {
            Home::Reg(r) if !ALLOCATABLE.contains(&r) => {
                return Err(format!("v{v} is in {}, which isn't allocatable", Reg::P(r)));
            }
            Home::Slot(s) if s >= a.slots => {
                return Err(format!("v{v} is in slot {s} of {}", a.slots));
            }
            Home::Slot(s) if seen[s as usize] => {
                return Err(format!("v{v} shares slot {s}"));
            }
            Home::Slot(s) => seen[s as usize] = true,
            Home::Unused if named[v] => return Err(format!("v{v} has no home")),
            _ => {}
        }
    }
    Ok(())
}

/// Validate an assignment against the code before allocation (see the module's comment).
pub fn check(
    f: &MFunc,
    callees: &[CallShape],
    own: &CallShape,
    a: &Assignment,
) -> Result<(), String> {
    check_homes(f, a)?;
    // What each physical register holds: a virtual register's value, the value last written to
    // it by name (or that it had on entry), or nothing the check knows.
    const NOTHING: u32 = u32::MAX;
    const OWN: u32 = u32::MAX - 1;
    type State = [u32; NPHYS];
    let nb = f.blocks.len();
    if nb == 0 {
        return Ok(());
    }
    let succ = successors(f);
    let mut at_entry: Vec<Option<State>> = vec![None; nb];
    at_entry[0] = Some([OWN; NPHYS]);
    let mut work = vec![0usize];
    let (mut defs, mut uses) = (Vec::new(), Vec::new());
    while let Some(b) = work.pop() {
        let mut st = at_entry[b].unwrap();
        for i in f.block_range(b) {
            let inst = f.insts[i];
            effects(f, callees, own, inst, &mut defs, &mut uses);
            for &u in &uses {
                let (r, want, what) = match u {
                    Reg::V(v) => match a.homes[v as usize] {
                        Home::Reg(r) => (r, v, format!("v{v}")),
                        _ => continue,
                    },
                    Reg::P(p) => (p, OWN, "its own value".to_owned()),
                };
                if st[r as usize] != want {
                    return Err(format!(
                        "block {b}, instruction {}: {inst:?} reads {what} from {}, which holds {}",
                        i - f.block_range(b).start,
                        Reg::P(r),
                        match st[r as usize] {
                            NOTHING => "nothing it knows".to_owned(),
                            OWN => "its own value".to_owned(),
                            w => format!("v{w}"),
                        }
                    ));
                }
            }
            for &d in &defs {
                match d {
                    Reg::P(p) => st[p as usize] = OWN,
                    Reg::V(v) => {
                        if let Home::Reg(r) = a.homes[v as usize] {
                            st[r as usize] = v;
                        }
                    }
                }
            }
        }
        for &s in &succ[b] {
            let s = s as usize;
            let next = match at_entry[s] {
                None => st,
                Some(old) => {
                    let mut m = old;
                    for (x, y) in m.iter_mut().zip(&st) {
                        if x != y {
                            *x = NOTHING;
                        }
                    }
                    m
                }
            };
            if at_entry[s] != Some(next) {
                at_entry[s] = Some(next);
                work.push(s);
            }
        }
    }
    Ok(())
}

/// Rewrite `f` by an assignment: virtual registers become their registers, spilled ones a
/// scratch register loaded before the instruction and stored after it.
fn rewrite(f: &mut MFunc, a: &Assignment) -> Result<(), String> {
    let base = f.frame.spill_base() as i32;
    let slot_off = |s: u32| base + 8 * s as i32;
    let mut insts = Vec::with_capacity(f.insts.len());
    let mut locs = Vec::with_capacity(f.locs.len());
    let mut blocks = Vec::with_capacity(f.blocks.len());
    let (mut defs, mut uses) = (Vec::new(), Vec::new());
    for b in 0..f.blocks.len() {
        blocks.push(insts.len() as u32);
        for i in f.block_range(b) {
            let inst = f.insts[i];
            let loc = f.locs[i];
            inst.regs(&mut defs, &mut uses);
            // The spilled registers it names, each with its scratch register.
            let mut spilled: Vec<(u32, u32, Reg)> = Vec::new();
            for r in uses.iter().chain(&defs) {
                if let Reg::V(v) = *r
                    && let Home::Slot(s) = a.homes[v as usize]
                    && !spilled.iter().any(|x| x.0 == v)
                {
                    let Some(&t) = SCRATCH.get(spilled.len()) else {
                        return Err(format!("{inst:?} names more than two spilled registers"));
                    };
                    spilled.push((v, s, t));
                }
            }
            for &(v, s, t) in &spilled {
                if uses.contains(&Reg::V(v)) {
                    insts.push(Inst::Load {
                        size: 8,
                        d: t,
                        base: RSP,
                        off: slot_off(s),
                    });
                    locs.push(loc);
                }
            }
            let new = inst.map_regs(|r, _| match r {
                Reg::V(v) => match a.homes[v as usize] {
                    Home::Reg(p) => Reg::P(p),
                    Home::Slot(_) => spilled.iter().find(|x| x.0 == v).unwrap().2,
                    Home::Unused => unreachable!("checked homes"),
                },
                p => p,
            });
            // A move between a register and itself does nothing.
            if !matches!(new, Inst::Mov { d, s } if d == s) {
                insts.push(new);
                locs.push(loc);
            }
            for &(v, s, t) in &spilled {
                if defs.contains(&Reg::V(v)) {
                    insts.push(Inst::Store {
                        size: 8,
                        s: t,
                        base: RSP,
                        off: slot_off(s),
                    });
                    locs.push(loc);
                }
            }
        }
    }
    f.insts = insts;
    f.locs = locs;
    f.blocks = blocks;
    Ok(())
}

/// Allocate registers for `f`, check the assignment, and rewrite `f` with it, filling in the
/// frame's spill slots and saved registers.
pub fn allocate(f: &mut MFunc, callees: &[CallShape], own: &CallShape) -> Result<(), String> {
    let a = assign(f, callees, own);
    check(f, callees, own, &a).map_err(|e| format!("register allocation is invalid: {e}"))?;
    for &h in &a.homes {
        if let Home::Reg(r) = h
            && CALLEE_SAVED.contains(&r)
        {
            f.frame.saved |= 1 << r;
        }
    }
    f.frame.spills = a.slots;
    if u64::from(f.frame.spill_base()) + 8 * u64::from(a.slots) > FRAME_LIMIT {
        return Err(format!(
            "the frame needs more than {FRAME_LIMIT} bytes (the x86-64 backend's limit)"
        ));
    }
    rewrite(f, &a)?;
    f.nvregs = 0;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn func(insts: Vec<Inst>, nvregs: u32) -> MFunc {
        let n = insts.len();
        MFunc {
            insts,
            locs: vec![None; n],
            blocks: vec![0],
            nvregs,
            ..MFunc::default()
        }
    }

    /// `v0 = rdi; v1 = 5; call f; rax = v0 + v1; ret`: both live across the call.
    fn across_call() -> MFunc {
        func(
            vec![
                Inst::Mov {
                    d: Reg::V(0),
                    s: RDI,
                },
                Inst::MovImm {
                    d: Reg::V(1),
                    imm: 5,
                },
                Inst::Call { func: 0 },
                Inst::Alu {
                    op: AluOp::Add,
                    d: Reg::V(0),
                    s: Reg::V(1),
                },
                Inst::Mov {
                    d: RAX,
                    s: Reg::V(0),
                },
                Inst::Ret,
            ],
            2,
        )
    }

    fn shapes() -> (Vec<CallShape>, CallShape) {
        let callee = CallShape {
            args: vec![],
            rets: vec![],
        };
        let own = CallShape {
            args: vec![RDI],
            rets: vec![RAX],
        };
        (vec![callee], own)
    }

    #[test]
    fn values_live_across_calls_go_to_callee_saved_registers() {
        let f = across_call();
        let (callees, own) = shapes();
        let a = assign(&f, &callees, &own);
        for h in &a.homes {
            let Home::Reg(r) = *h else {
                panic!("spilled: {:?}", a.homes)
            };
            assert!(CALLEE_SAVED.contains(&r), "{:?}", a.homes);
        }
        check(&f, &callees, &own, &a).unwrap();
    }

    #[test]
    fn the_check_refuses_clobbered_and_shared_registers() {
        let f = across_call();
        let (callees, own) = shapes();
        // In a caller-saved register, the call clobbers v0.
        let a = Assignment {
            homes: vec![Home::Reg(1), Home::Reg(3)],
            slots: 0,
        };
        assert!(check(&f, &callees, &own, &a).unwrap_err().contains("v0"));
        // Both in rbx: v1 overwrites v0.
        let a = Assignment {
            homes: vec![Home::Reg(3), Home::Reg(3)],
            slots: 0,
        };
        assert!(check(&f, &callees, &own, &a).is_err());
        // Scratch and reserved registers, and shared or missing slots, are refused.
        for homes in [
            vec![Home::Reg(10), Home::Reg(3)],
            vec![Home::Reg(4), Home::Reg(3)],
            vec![Home::Slot(0), Home::Slot(0)],
            vec![Home::Slot(1), Home::Reg(3)],
            vec![Home::Unused, Home::Reg(3)],
        ] {
            let a = Assignment { homes, slots: 1 };
            assert!(check(&f, &callees, &own, &a).is_err(), "{:?}", a.homes);
        }
        // Slots always hold their register.
        let a = Assignment {
            homes: vec![Home::Slot(0), Home::Slot(1)],
            slots: 2,
        };
        check(&f, &callees, &own, &a).unwrap();
        // A virtual register written to the argument register still to be read by name
        // overwrites the argument: `v0 = 99; rax = rdi` with v0 in rdi returns 99.
        let f = func(
            vec![
                Inst::MovImm {
                    d: Reg::V(0),
                    imm: 99,
                },
                Inst::Mov { d: RAX, s: RDI },
                Inst::Ret,
            ],
            1,
        );
        let a = Assignment {
            homes: vec![Home::Reg(7)],
            slots: 0,
        };
        let e = check(&f, &callees, &own, &a).unwrap_err();
        assert!(e.contains("reads its own value from rdi"), "{e}");
    }

    #[test]
    fn pressure_spills_and_the_rewrite_uses_scratch_registers() {
        // Twenty values live at once: more than there are registers.
        let n = 20u32;
        let mut insts: Vec<Inst> = (0..n)
            .map(|v| Inst::MovImm {
                d: Reg::V(v),
                imm: u64::from(v),
            })
            .collect();
        for v in 1..n {
            insts.push(Inst::Alu {
                op: AluOp::Add,
                d: Reg::V(0),
                s: Reg::V(v),
            });
        }
        insts.push(Inst::Mov {
            d: RAX,
            s: Reg::V(0),
        });
        insts.push(Inst::Ret);
        let mut f = func(insts, n);
        let (callees, own) = shapes();
        let a = assign(&f, &callees, &own);
        assert!(a.slots > 0);
        check(&f, &callees, &own, &a).unwrap();
        allocate(&mut f, &callees, &own).unwrap();
        let (mut defs, mut uses) = (Vec::new(), Vec::new());
        for &i in &f.insts {
            i.regs(&mut defs, &mut uses);
            assert!(defs.iter().chain(&uses).all(|r| !r.is_virtual()), "{i:?}");
        }
        assert!(
            f.insts
                .iter()
                .any(|i| matches!(i, Inst::Load { d, .. } if *d == R10))
        );
    }
}
