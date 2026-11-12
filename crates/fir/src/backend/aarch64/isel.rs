//! Instruction selection: MFIR (or HFIR made of core ops) to AArch64 LFIR over virtual
//! registers.
//!
//! Every SSA value gets a virtual register; region parameters (loop state, block arguments, the
//! results of `cf.if`, `cf.loop`, and `cf.blocks`) are virtual registers written by moves where
//! control reaches them, so the output is in machine form, not SSA. Structured control flow
//! becomes blocks and branches.
//!
//! **Integers.** An `iN` (N ≤ 64) lives in the low N bits of a register; the bits above are
//! unspecified. Ops whose result depends only on the low bits (add, sub, mul, logic, `shl`) use
//! them as they are; the others (comparisons, division, right shifts, extensions, overflow
//! checks) sign- or zero-extend their operands first. Wider integers are rejected.
//!
//! **Edge cases** follow the op's modifiers: `.wrap`, `.nsw`, `.nuw`, and `.ub` compute the
//! wrapped result (poison and UB allow any value); `.trap` branches to a trap block on overflow;
//! `.sat` selects the bound. Division by zero traps when asked to and otherwise relies on
//! `sdiv`/`udiv` giving 0 (and `msub` giving `x rem 0 = x`), which is what `.total` means; signed
//! `MIN / -1` wraps in hardware. Shifts by at least the width trap, mask the amount, or select
//! the all-shifted-out value.
//!
//! **Memory**: `mem.stack` slots are fixed frame slots (a loop iteration's slot is the previous
//! iteration's, which is dead by then); heap allocation calls the family's allocator; loads and
//! stores of odd sizes split into 4-, 2-, and 1-byte accesses; `mem.copy` copies up to 64 bytes
//! through registers and larger sizes in a loop whose direction depends on the addresses, so
//! overlap is fine. **Calls** follow AAPCS64 (see `super::abi`).

use rustc_hash::FxHashMap;

use super::mir::{Frame, Inst, MFunc};
use crate::body::{Body, OpId, OperandKind, RegionId, ValueId};
use crate::ir::*;
use crate::types::align_up;

const NONE: u32 = u32::MAX;

pub type Result<T> = std::result::Result<T, String>;

/// What `cf.yield`, `cf.break`, `cf.continue`, and jumps leave to.
enum Ctx {
    If {
        results: Vec<Reg>,
        join: u32,
    },
    Loop {
        header: u32,
        exit: u32,
        params: Vec<Reg>,
        results: Vec<Reg>,
    },
    Blocks {
        /// Each block's label, machine block, and parameters.
        labels: Vec<(String, u32, Vec<Reg>)>,
        results: Vec<Reg>,
        exit: u32,
    },
}

/// What the module tells the selection of one function.
pub struct ModuleCx<'a> {
    pub m: &'a Module,
    /// Functions, then external functions, by name: the callee indices of `bl`.
    pub funcs: FxHashMap<&'a str, u32>,
    pub globals: FxHashMap<&'a str, u32>,
}

impl<'a> ModuleCx<'a> {
    pub fn new(m: &'a Module) -> ModuleCx<'a> {
        let mut funcs = FxHashMap::default();
        for (i, f) in m.funcs.iter().enumerate() {
            funcs.insert(f.name.as_str(), i as u32);
        }
        for (i, x) in m.externs.iter().enumerate() {
            funcs.insert(x.name.as_str(), (m.funcs.len() + i) as u32);
        }
        let globals = (0..m.globals.len())
            .map(|g| (m.globals.name(g), g as u32))
            .collect();
        ModuleCx { m, funcs, globals }
    }

    /// The parameter and result types of callee `f`.
    pub fn sig(&self, f: u32) -> (Vec<Ty>, &'a [Ty]) {
        let m = self.m;
        match m.funcs.get(f as usize) {
            Some(func) => {
                let b = &func.body;
                (b.params(b.entry()).map(|v| b.ty(v)).collect(), &func.rets)
            }
            None => {
                let x = &m.externs[f as usize - m.funcs.len()];
                (x.params.clone(), &x.rets)
            }
        }
    }
}

/// Check that a module can be compiled: 64-bit pointers and addresses.
pub fn check_module(m: &Module) -> Result<()> {
    if m.space.ptr_bits != 64 || m.space.addr_bits != 64 {
        return Err(format!(
            "the AArch64 backend needs 64-bit pointers and addresses, not ptr {} addr {}",
            m.space.ptr_bits, m.space.addr_bits
        ));
    }
    if let crate::Layer::Lfir(_) = m.layer {
        return Err("the module is already LFIR".to_owned());
    }
    for x in &m.externs {
        for &t in x.params.iter().chain(&x.rets) {
            check_ty(None, t).map_err(|e| format!("extern @{}: {e}", x.name))?;
        }
    }
    Ok(())
}

fn check_ty(loc: Option<Loc>, t: Ty) -> Result<()> {
    match t {
        Ty::Int(w) | Ty::Byte(w) if w > 64 => Err(format!(
            "{}{t} is wider than 64 bits, which the AArch64 backend doesn't support yet",
            at(loc)
        )),
        _ => Ok(()),
    }
}

fn at(loc: Option<Loc>) -> String {
    match loc {
        Some(l) => format!("@{}:{}: ", l.line, l.col),
        None => String::new(),
    }
}

/// The chunks a `size`-byte access splits into: (offset, size), with sizes 8, 4, 2, 1.
fn chunks(size: u64) -> impl Iterator<Item = (u64, MemSize)> {
    let mut off = 0;
    std::iter::from_fn(move || {
        let left = size - off;
        let s = [8, 4, 2, 1].into_iter().find(|&s| s <= left)?;
        let c = (off, MemSize::of_bytes(s).unwrap());
        off += s;
        Some(c)
    })
}

/// The condition for an integer comparison, after `cmp a, b`.
fn cond_of(p: Pred) -> Cond {
    match p {
        Pred::Eq => Cond::Eq,
        Pred::Ne => Cond::Ne,
        Pred::Slt => Cond::Lt,
        Pred::Sle => Cond::Le,
        Pred::Sgt => Cond::Gt,
        Pred::Sge => Cond::Ge,
        Pred::Ult => Cond::Lo,
        Pred::Ule => Cond::Ls,
        Pred::Ugt => Cond::Hi,
        Pred::Uge => Cond::Hs,
    }
}

fn is_signed(p: Pred) -> bool {
    matches!(p, Pred::Slt | Pred::Sle | Pred::Sgt | Pred::Sge)
}

/// The instructions `movz`/`movn`/`movk` need for a 64-bit value: the first move's kind and
/// chunk, then the chunks `movk` inserts.
fn mov_plan(x: u64) -> (MovOp, u16, u8, Vec<(u16, u8)>) {
    let parts: Vec<u16> = (0..4).map(|i| (x >> (16 * i)) as u16).collect();
    let zeros = parts.iter().filter(|&&p| p == 0).count();
    let ones = parts.iter().filter(|&&p| p == 0xffff).count();
    if ones > zeros {
        let first = parts.iter().position(|&p| p != 0xffff).unwrap_or(0);
        let rest = (0..4)
            .filter(|&i| i != first && parts[i] != 0xffff)
            .map(|i| (parts[i], (16 * i) as u8))
            .collect();
        (MovOp::Movn, !parts[first], (16 * first) as u8, rest)
    } else {
        let first = parts.iter().position(|&p| p != 0).unwrap_or(0);
        let rest = (0..4)
            .filter(|&i| i != first && parts[i] != 0)
            .map(|i| (parts[i], (16 * i) as u8))
            .collect();
        (MovOp::Movz, parts[first], (16 * first) as u8, rest)
    }
}

/// Whether `x` is an immediate of `add` and `sub`: 12 bits, optionally shifted left by 12.
pub fn is_arith_imm(x: i64) -> bool {
    (0..4096).contains(&x) || (x & 0xfff == 0 && (0..4096 << 12).contains(&x))
}

/// Whether `x` (at size `sf`) is a logical (bitmask) immediate: a rotated run of ones,
/// repeated across the register in elements of 2, 4, …, 64 bits.
pub fn is_logical_imm(x: u64, sf: Sf) -> bool {
    let n = sf.bits();
    let x = if n == 32 {
        let lo = x & 0xffff_ffff;
        lo | lo << 32
    } else {
        x
    };
    if x == 0 || x == u64::MAX {
        return false;
    }
    let mut size = 64;
    while size > 2 {
        let half = size / 2;
        let mask = (1u64 << half) - 1;
        if (x & mask) != ((x >> half) & mask) {
            break;
        }
        size = half;
    }
    let mask = if size == 64 {
        u64::MAX
    } else {
        (1u64 << size) - 1
    };
    let e = x & mask;
    // A rotation of a run of ones: rotating so the run starts at bit 0 leaves `0…01…1`.
    (0..size).any(|r| {
        let rot = if r == 0 {
            e
        } else {
            ((e >> r) | (e << (size - r))) & mask
        };
        rot != 0 && rot & (rot + 1) == 0
    })
}

/// Whether `off` can address a `size`-byte access directly: a scaled unsigned 12-bit offset,
/// or an unscaled signed 9-bit one.
pub fn is_mem_off(off: i64, size: MemSize) -> bool {
    let s = i64::from(size.bytes());
    (off >= 0 && off % s == 0 && off / s < 4096) || (-256..256).contains(&off)
}

struct Sel<'a, 'c> {
    cx: &'c ModuleCx<'a>,
    body: &'a Body,
    sp: &'a SpaceCfg,
    families: &'c mut Vec<String>,
    /// Each block's instructions and locations, by creation.
    blocks: Vec<Vec<(Inst, Option<Loc>)>>,
    /// Blocks laid out after the others: the exit block and trap blocks.
    cold: Vec<bool>,
    cur: u32,
    /// Whether the current block has ended.
    done: bool,
    /// Each value's virtual register (`NONE` until defined).
    vreg: Vec<u32>,
    nv: u32,
    ctx: Vec<Ctx>,
    sigs: Vec<(Vec<Ty>, Vec<Ty>)>,
    frame: Frame,
    /// Where the locals start above `sp`, and how far they reach.
    locals_base: u64,
    locals_end: u64,
    exit: u32,
    /// The register that keeps the results area's address (`x8` on entry), if any.
    res_ptr: Option<Reg>,
    rets: &'a [Ty],
    loc: Option<Loc>,
}

/// Select one function.
pub fn select_func(cx: &ModuleCx<'_>, index: u32, families: &mut Vec<String>) -> Result<MFunc> {
    let f = &cx.m.funcs[index as usize];
    let body = &f.body;
    for &t in &f.rets {
        check_ty(None, t).map_err(|e| format!("@{}: {e}", f.name))?;
    }
    let mut s = Sel {
        cx,
        body,
        sp: &cx.m.space,
        families,
        blocks: Vec::new(),
        cold: Vec::new(),
        cur: 0,
        done: false,
        vreg: vec![NONE; body.num_values()],
        nv: 0,
        ctx: Vec::new(),
        sigs: Vec::new(),
        frame: Frame::default(),
        locals_base: 0,
        locals_end: 0,
        exit: 0,
        res_ptr: None,
        rets: &f.rets,
        loc: None,
    };
    s.func().map_err(|e| format!("@{}: {e}", f.name))?;
    Ok(s.finish(index))
}

impl Sel<'_, '_> {
    // Building blocks of code

    fn new_block(&mut self, cold: bool) -> u32 {
        self.blocks.push(Vec::new());
        self.cold.push(cold);
        (self.blocks.len() - 1) as u32
    }

    fn switch_to(&mut self, b: u32) {
        self.cur = b;
        self.done = false;
    }

    fn emit(&mut self, i: Inst) {
        debug_assert!(!self.done, "code after a terminator");
        self.blocks[self.cur as usize].push((i, self.loc));
        if i.is_terminator() {
            self.done = true;
        }
    }

    fn fresh(&mut self) -> Reg {
        self.nv += 1;
        Reg::virt(self.nv - 1)
    }

    fn val(&mut self, v: ValueId) -> Reg {
        if self.vreg[v.index()] == NONE {
            let r = self.fresh();
            self.vreg[v.index()] = r.virt_index();
        }
        Reg::virt(self.vreg[v.index()])
    }

    fn operand(&mut self, op: OpId, i: usize) -> Result<Reg> {
        match self.body.operands(op)[i].get() {
            OperandKind::Value(v) => Ok(self.val(v)),
            OperandKind::Hole(h) => Err(format!(
                "{}the hole ?{} can't be compiled",
                at(self.loc),
                self.body.hole_name(h)
            )),
        }
    }

    fn operands(&mut self, op: OpId) -> Result<Vec<Reg>> {
        (0..self.body.operands(op).len())
            .map(|i| self.operand(op, i))
            .collect()
    }

    /// The register of an op's `i`th result.
    fn result(&mut self, op: OpId, i: usize) -> Reg {
        let v = self.body.results(op).nth(i).unwrap();
        self.val(v)
    }

    fn width_of(&self, op: OpId, i: usize) -> u32 {
        match self.body.operands(op)[i].get() {
            OperandKind::Value(v) => match self.body.ty(v) {
                Ty::Int(w) | Ty::Byte(w) => w,
                _ => 64,
            },
            OperandKind::Hole(h) => match self.body.hole_ty(h) {
                Ty::Int(w) | Ty::Byte(w) => w,
                _ => 64,
            },
        }
    }

    fn mov(&mut self, d: Reg, n: Reg) {
        if d != n {
            self.emit(Inst::Mov { sf: Sf::X, d, n });
        }
    }

    /// Put a 64-bit constant in `d`.
    fn mov_imm(&mut self, d: Reg, x: u64) {
        let (op, imm, hw, rest) = mov_plan(x);
        self.emit(Inst::MovWide {
            op,
            sf: Sf::X,
            d,
            imm,
            hw,
        });
        for (imm, hw) in rest {
            self.emit(Inst::MovWide {
                op: MovOp::Movk,
                sf: Sf::X,
                d,
                imm,
                hw,
            });
        }
    }

    /// A register holding the constant.
    fn konst(&mut self, x: u64) -> Reg {
        let d = self.fresh();
        self.mov_imm(d, x);
        d
    }

    /// An `iN` constant's cheaper 64-bit form: its bits zero- or sign-extended.
    fn mov_int(&mut self, d: Reg, w: u32, bits: u64) {
        let z = bits & mask(w);
        let s = sext(w, z) as u64;
        let cost = |x: u64| mov_plan(x).3.len();
        self.mov_imm(d, if cost(s) < cost(z) { s } else { z });
    }

    /// The low `w` bits of `r`, zero-extended (`r` itself when `w` is 64).
    fn zx(&mut self, r: Reg, w: u32) -> Reg {
        if w >= 64 {
            return r;
        }
        let d = self.fresh();
        self.emit(Inst::Ext {
            signed: false,
            sf: Sf::X,
            d,
            n: r,
            width: w as u8,
        });
        d
    }

    /// The low `w` bits of `r`, sign-extended.
    fn sx(&mut self, r: Reg, w: u32) -> Reg {
        if w >= 64 {
            return r;
        }
        let d = self.fresh();
        self.emit(Inst::Ext {
            signed: true,
            sf: Sf::X,
            d,
            n: r,
            width: w as u8,
        });
        d
    }

    fn alu(&mut self, op: AluOp, d: Reg, n: Reg, m: Reg) {
        self.emit(Inst::Alu {
            op,
            sf: Sf::X,
            d,
            n,
            m,
        });
    }

    fn alu_new(&mut self, op: AluOp, n: Reg, m: Reg) -> Reg {
        let d = self.fresh();
        self.alu(op, d, n, m);
        d
    }

    /// `cmp n, #k` (or with a register for constants that don't fit).
    fn cmp_imm(&mut self, n: Reg, k: i64) {
        if is_arith_imm(k) {
            self.emit(Inst::AluImm {
                op: AluImmOp::Subs,
                sf: Sf::X,
                d: Reg::XZR,
                n,
                imm: k,
            });
        } else if is_arith_imm(k.wrapping_neg()) {
            self.emit(Inst::AluImm {
                op: AluImmOp::Adds,
                sf: Sf::X,
                d: Reg::XZR,
                n,
                imm: k.wrapping_neg(),
            });
        } else {
            let t = self.konst(k as u64);
            self.alu(AluOp::Subs, Reg::XZR, n, t);
        }
    }

    /// `d = n + k`, for any constant.
    fn add_imm(&mut self, d: Reg, n: Reg, k: i64) {
        if is_arith_imm(k) {
            self.emit(Inst::AluImm {
                op: AluImmOp::Add,
                sf: Sf::X,
                d,
                n,
                imm: k,
            });
        } else if is_arith_imm(k.wrapping_neg()) {
            self.emit(Inst::AluImm {
                op: AluImmOp::Sub,
                sf: Sf::X,
                d,
                n,
                imm: k.wrapping_neg(),
            });
        } else {
            let t = self.konst(k as u64);
            self.alu(AluOp::Add, d, n, t);
        }
    }

    /// `cset d, c`.
    fn cset(&mut self, d: Reg, c: Cond) {
        self.emit(Inst::Csel {
            op: CselOp::Csinc,
            c: c.invert(),
            sf: Sf::X,
            d,
            n: Reg::XZR,
            m: Reg::XZR,
        });
    }

    /// Branch on bit 0 of `c` (an `i1`).
    fn branch_bit(&mut self, c: Reg, t: u32, f: u32) {
        self.emit(Inst::AluImm {
            op: AluImmOp::Ands,
            sf: Sf::X,
            d: Reg::XZR,
            n: c,
            imm: 1,
        });
        self.emit(Inst::BCond { c: Cond::Ne, t, f });
    }

    /// A trap block for the current op: `aarch64.trap.R` at its location.
    fn trap_block(&mut self, r: TrapReason) -> u32 {
        let b = self.new_block(true);
        self.blocks[b as usize].push((Inst::Trap(r), self.loc));
        b
    }

    /// Trap with reason `r` if condition `c` holds (after the flags are set).
    fn trap_if(&mut self, c: Cond, r: TrapReason) {
        let t = self.trap_block(r);
        let cont = self.new_block(false);
        self.emit(Inst::BCond { c, t, f: cont });
        self.switch_to(cont);
    }

    /// Moves that act at once: `dsts[i] = srcs[i]` for all `i`, through temporaries when a
    /// destination is also a source.
    fn moves(&mut self, dsts: &[Reg], srcs: &[Reg]) {
        let clash = dsts
            .iter()
            .enumerate()
            .any(|(i, d)| srcs.iter().enumerate().any(|(j, s)| s == d && i != j));
        if clash {
            let tmps: Vec<Reg> = srcs
                .iter()
                .map(|&s| {
                    let t = self.fresh();
                    self.mov(t, s);
                    t
                })
                .collect();
            for (&d, &t) in dsts.iter().zip(&tmps) {
                self.mov(d, t);
            }
        } else {
            for (&d, &s) in dsts.iter().zip(srcs) {
                self.mov(d, s);
            }
        }
    }

    /// An address the `size`-byte access can use with an immediate offset: `(base, off)` as is
    /// if it fits, otherwise a register holding `base + off`.
    fn addr(&mut self, base: Reg, off: i64, size: MemSize) -> (Reg, i64) {
        if is_mem_off(off, size) {
            (base, off)
        } else {
            let t = self.fresh();
            self.add_imm(t, base, off);
            (t, 0)
        }
    }

    fn ldr(&mut self, size: MemSize, d: Reg, base: Reg, off: i64) {
        let (base, off) = self.addr(base, off, size);
        self.emit(Inst::Ldr { size, d, base, off });
    }

    fn str_(&mut self, size: MemSize, s: Reg, base: Reg, off: i64) {
        let (base, off) = self.addr(base, off, size);
        self.emit(Inst::Str { size, s, base, off });
    }

    /// Load `size` bytes (1 to 8) little-endian into `d`.
    fn load(&mut self, d: Reg, base: Reg, off: i64, size: u64) {
        let mut first = true;
        for (o, s) in chunks(size) {
            if first {
                self.ldr(s, d, base, off + o as i64);
                first = false;
            } else {
                let t = self.fresh();
                self.ldr(s, t, base, off + o as i64);
                let sh = self.fresh();
                self.emit(Inst::ShiftImm {
                    op: ShiftImmOp::Lsl,
                    sf: Sf::X,
                    d: sh,
                    n: t,
                    amount: (8 * o) as u8,
                });
                self.alu(AluOp::Orr, d, d, sh);
            }
        }
    }

    /// Store the low `size` bytes (1 to 8) of `v`.
    fn store(&mut self, v: Reg, base: Reg, off: i64, size: u64) {
        for (o, s) in chunks(size) {
            let part = if o == 0 {
                v
            } else {
                let t = self.fresh();
                self.emit(Inst::ShiftImm {
                    op: ShiftImmOp::Lsr,
                    sf: Sf::X,
                    d: t,
                    n: v,
                    amount: (8 * o) as u8,
                });
                t
            };
            self.str_(s, part, base, off + o as i64);
        }
    }

    /// A frame slot for a local: its offset from `sp`.
    fn local(&mut self, size: u64, align: u64) -> i64 {
        let off = align_up(u128::from(self.locals_end), align.max(1)) as u64;
        self.locals_end = off + size.max(1);
        self.frame.align = self.frame.align.max(align as u32);
        (self.locals_base + off) as i64
    }

    fn type_size(&self, t: Ty) -> u64 {
        self.body.types().size(self.sp, t) as u64
    }

    // The function

    fn func(&mut self) -> Result<()> {
        let body = self.body;
        // Outgoing arguments and local alignment, known before any local is placed.
        let mut outgoing = 0u64;
        let mut align = 16u64;
        let mut stack = vec![body.entry()];
        while let Some(r) = stack.pop() {
            for op in body.ops(r) {
                match body.kind(op) {
                    OpKind::Call { .. } | OpKind::CallIndirect(_) => {
                        let n = body.operands(op).len()
                            - usize::from(matches!(body.kind(op), OpKind::CallIndirect(_)));
                        outgoing = outgoing.max(8 * n.saturating_sub(8) as u64);
                    }
                    OpKind::MemStack { align: a, .. } => align = align.max(u64::from(a)),
                    OpKind::MemStackOf { ty, align: a } => {
                        align = align.max(u64::from(a)).max(body.types().align(self.sp, ty))
                    }
                    _ => {}
                }
                stack.extend_from_slice(body.regions(op));
            }
        }
        self.locals_base = align_up(u128::from(outgoing), align) as u64;
        self.frame.outgoing = self.locals_base as u32;
        self.frame.align = 16;
        // The prologue: save fp and lr, set fp, and make room for the rest of the frame (the
        // frame lowering fills in the size and saves the callee-saved registers).
        let entry = self.new_block(false);
        self.exit = self.new_block(true);
        self.switch_to(entry);
        let x = Reg::x;
        self.emit(Inst::AluImm {
            op: AluImmOp::Sub,
            sf: Sf::X,
            d: Reg::SP,
            n: Reg::SP,
            imm: 16,
        });
        self.emit(Inst::Str {
            size: MemSize::X,
            s: Reg::FP,
            base: Reg::SP,
            off: 0,
        });
        self.emit(Inst::Str {
            size: MemSize::X,
            s: Reg::LR,
            base: Reg::SP,
            off: 8,
        });
        self.emit(Inst::Mov {
            sf: Sf::X,
            d: Reg::FP,
            n: Reg::SP,
        });
        self.emit(Inst::AluImm {
            op: AluImmOp::Sub,
            sf: Sf::X,
            d: Reg::SP,
            n: Reg::SP,
            imm: 0,
        });
        // Parameters, from where the convention puts them.
        let params: Vec<ValueId> = body.params(body.entry()).collect();
        for (i, &p) in params.iter().enumerate() {
            check_ty(None, body.ty(p))?;
            let r = self.val(p);
            if i < 8 {
                self.mov(r, x(i as u32));
            } else {
                self.ldr(MemSize::X, r, Reg::FP, 16 + 8 * (i as i64 - 8));
            }
        }
        if self.rets.len() > 2 {
            let r = self.fresh();
            self.mov(r, x(8));
            self.res_ptr = Some(r);
        }
        self.region(body.entry())?;
        // The epilogue.
        self.switch_to(self.exit);
        self.loc = None;
        self.emit(Inst::Mov {
            sf: Sf::X,
            d: Reg::SP,
            n: Reg::FP,
        });
        self.emit(Inst::Ldr {
            size: MemSize::X,
            d: Reg::FP,
            base: Reg::SP,
            off: 0,
        });
        self.emit(Inst::Ldr {
            size: MemSize::X,
            d: Reg::LR,
            base: Reg::SP,
            off: 8,
        });
        self.emit(Inst::AluImm {
            op: AluImmOp::Add,
            sf: Sf::X,
            d: Reg::SP,
            n: Reg::SP,
            imm: 16,
        });
        self.emit(Inst::Ret);
        Ok(())
    }

    /// Lay the blocks out (hot ones in order, then the exit block and trap blocks) and flatten
    /// them.
    fn finish(self, index: u32) -> MFunc {
        let n = self.blocks.len();
        let mut order: Vec<u32> = (0..n as u32).filter(|&b| !self.cold[b as usize]).collect();
        order.push(self.exit);
        order.extend((0..n as u32).filter(|&b| self.cold[b as usize] && b != self.exit));
        let mut new_index = vec![0u32; n];
        for (i, &b) in order.iter().enumerate() {
            new_index[b as usize] = i as u32;
        }
        let mut out = MFunc {
            index,
            nvregs: self.nv,
            sigs: self.sigs,
            frame: self.frame,
            ..MFunc::default()
        };
        out.frame.locals = (align_up(u128::from(self.locals_end), 16) as u64) as u32;
        out.frame.exit = new_index[self.exit as usize];
        for &b in &order {
            out.blocks.push(out.insts.len() as u32);
            let code = &self.blocks[b as usize];
            for &(i, loc) in code {
                let i = match i {
                    Inst::B { t } => Inst::B {
                        t: new_index[t as usize],
                    },
                    Inst::BCond { c, t, f } => Inst::BCond {
                        c,
                        t: new_index[t as usize],
                        f: new_index[f as usize],
                    },
                    i => i,
                };
                out.insts.push(i);
                out.locs.push(loc);
            }
            // A block that nothing reaches may lack a terminator; it loops on itself.
            if !code.last().is_some_and(|(i, _)| i.is_terminator()) {
                out.insts.push(Inst::B {
                    t: new_index[b as usize],
                });
                out.locs.push(None);
            }
        }
        // The prologue's `sub sp, sp, N` is its fifth instruction.
        out.frame.alloc_at = 4;
        out
    }

    // Regions and ops

    fn region(&mut self, r: RegionId) -> Result<()> {
        for op in self.body.ops(r) {
            self.op(op)?;
        }
        if !self.done {
            // Falling off the end of a `cf.if` region yields nothing.
            self.yield_(&[]);
        }
        Ok(())
    }

    fn yield_(&mut self, vals: &[Reg]) {
        match self.ctx.last() {
            Some(Ctx::If { results, join }) => {
                let (results, join) = (results.clone(), *join);
                self.moves(&results, vals);
                self.emit(Inst::B { t: join });
            }
            Some(Ctx::Blocks { results, exit, .. }) => {
                let (results, exit) = (results.clone(), *exit);
                self.moves(&results, vals);
                self.emit(Inst::B { t: exit });
            }
            _ => self.emit(Inst::B { t: self.cur }),
        }
    }

    fn nearest_loop(&self) -> Option<(u32, u32, Vec<Reg>, Vec<Reg>)> {
        self.ctx.iter().rev().find_map(|c| match c {
            Ctx::Loop {
                header,
                exit,
                params,
                results,
            } => Some((*header, *exit, params.clone(), results.clone())),
            _ => None,
        })
    }

    /// The machine block and parameters of block `label` of the nearest `cf.blocks`.
    fn target(&self, label: &str) -> (u32, Vec<Reg>) {
        self.ctx
            .iter()
            .rev()
            .find_map(|c| match c {
                Ctx::Blocks { labels, .. } => labels
                    .iter()
                    .find(|(l, _, _)| l == label)
                    .map(|(_, b, ps)| (*b, ps.clone())),
                _ => None,
            })
            .expect("verified jumps name blocks")
    }

    /// Jump to a block with arguments: moves into its parameters, then a branch.
    fn jump(&mut self, label: &str, args: &[Reg]) {
        let (b, ps) = self.target(label);
        self.moves(&ps, args);
        self.emit(Inst::B { t: b });
    }

    /// A block that jumps to `label` with `args`, or the target itself when there are none.
    fn edge(&mut self, label: &str, args: &[Reg]) -> u32 {
        let (b, ps) = self.target(label);
        if ps.is_empty() {
            return b;
        }
        let e = self.new_block(false);
        let back = (self.cur, self.done);
        self.switch_to(e);
        self.jump(label, args);
        (self.cur, self.done) = back;
        e
    }

    fn op(&mut self, op: OpId) -> Result<()> {
        let body = self.body;
        let kind = body.kind(op);
        self.loc = body.loc(op);
        for v in body.results(op) {
            check_ty(self.loc, body.ty(v))?;
        }
        match kind {
            OpKind::Const(n) => {
                let w = body.ty(body.results(op).next().unwrap()).width_bits();
                let bits = int_low_bits(body.int(n));
                let d = self.result(op, 0);
                self.mov_int(d, w, bits);
            }
            OpKind::Poison | OpKind::PtrNull => {
                let d = self.result(op, 0);
                self.mov_imm(d, 0);
            }
            OpKind::Freeze
            | OpKind::Copy
            | OpKind::Trunc(_)
            | OpKind::PtrAddr
            | OpKind::PtrExpose
            | OpKind::PtrFromExposed => {
                // The same register: `freeze` has a value already, and the others change no
                // bits that matter.
                let a = self.operand(op, 0)?;
                let v = body.results(op).next().unwrap();
                self.vreg[v.index()] = a.virt_index();
            }
            OpKind::PtrWithAddr => {
                let a = self.operand(op, 1)?;
                let v = body.results(op).next().unwrap();
                self.vreg[v.index()] = a.virt_index();
            }
            OpKind::Select => {
                let (c, a, b) = (
                    self.operand(op, 0)?,
                    self.operand(op, 1)?,
                    self.operand(op, 2)?,
                );
                let d = self.result(op, 0);
                self.emit(Inst::AluImm {
                    op: AluImmOp::Ands,
                    sf: Sf::X,
                    d: Reg::XZR,
                    n: c,
                    imm: 1,
                });
                self.emit(Inst::Csel {
                    op: CselOp::Csel,
                    c: Cond::Ne,
                    sf: Sf::X,
                    d,
                    n: a,
                    m: b,
                });
            }
            OpKind::Arith(aop, ovf) => {
                let w = self.width_of(op, 0);
                let (a, b) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let d = self.result(op, 0);
                self.arith(aop, ovf, w, d, a, b);
            }
            OpKind::Bit(bop) => {
                let (a, b) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let d = self.result(op, 0);
                let o = match bop {
                    BitOp::And => AluOp::And,
                    BitOp::Or => AluOp::Orr,
                    BitOp::Xor => AluOp::Eor,
                };
                self.alu(o, d, a, b);
            }
            OpKind::Div(dop, zero, ovf) => {
                let w = self.width_of(op, 0);
                let (a, b) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let d = self.result(op, 0);
                self.div(dop, zero, ovf, w, d, a, b);
            }
            OpKind::Shift(sop, edge) => {
                let w = self.width_of(op, 0);
                let (a, b) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let d = self.result(op, 0);
                self.shift(sop, edge, w, d, a, b);
            }
            OpKind::Cmp(p) => {
                let w = self.width_of(op, 0);
                let (a, b) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let d = self.result(op, 0);
                let (a, b) = if is_signed(p) {
                    (self.sx(a, w), self.sx(b, w))
                } else {
                    (self.zx(a, w), self.zx(b, w))
                };
                self.alu(AluOp::Subs, Reg::XZR, a, b);
                self.cset(d, cond_of(p));
            }
            OpKind::PtrCmp(p) => {
                let (a, b) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let d = self.result(op, 0);
                self.alu(AluOp::Subs, Reg::XZR, a, b);
                self.cset(d, cond_of(p));
            }
            OpKind::Zext | OpKind::Sext => {
                let w = self.width_of(op, 0);
                let a = self.operand(op, 0)?;
                let d = self.result(op, 0);
                self.emit(Inst::Ext {
                    signed: kind == OpKind::Sext,
                    sf: Sf::X,
                    d,
                    n: a,
                    width: w as u8,
                });
            }
            OpKind::MemStack { size, align } => {
                let off = self.local(size, u64::from(align));
                let d = self.result(op, 0);
                self.add_imm(d, Reg::SP, off);
            }
            OpKind::MemStackOf { ty, align } => {
                let size = self.type_size(ty);
                let a = u64::from(align).max(body.types().align(self.sp, ty));
                let off = self.local(size, a);
                let d = self.result(op, 0);
                self.add_imm(d, Reg::SP, off);
            }
            OpKind::MemAlloc {
                fail,
                family,
                align,
            } => {
                let n = self.operand(op, 0)?;
                let d = self.result(op, 0);
                let family = self.family(body.str(family));
                self.mov(Reg::x(0), n);
                self.emit(Inst::BlAlloc { family, align });
                self.mov(d, Reg::x(0));
                if fail == AllocFail::Trap {
                    self.cmp_imm(d, 0);
                    self.trap_if(Cond::Eq, TrapReason::Oom);
                }
            }
            OpKind::MemFree { family } => {
                let p = self.operand(op, 0)?;
                let family = self.family(body.str(family));
                self.mov(Reg::x(0), p);
                self.emit(Inst::BlFree { family });
            }
            OpKind::Load { .. } => {
                let p = self.operand(op, 0)?;
                let v = body.results(op).next().unwrap();
                let size = self.type_size(body.ty(v));
                let d = self.val(v);
                self.load(d, p, 0, size);
            }
            OpKind::Store { ty, .. } => {
                let (v, p) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let size = self.type_size(ty);
                self.store(v, p, 0, size);
            }
            OpKind::MemCopy { ty, .. } => {
                let (d, s) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let size = self.type_size(ty);
                self.copy(d, s, size);
            }
            OpKind::PtrOffset { .. } => {
                let (p, n) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let d = self.result(op, 0);
                self.alu(AluOp::Add, d, p, n);
            }
            OpKind::PtrField { ty, index, .. } => {
                let p = self.operand(op, 0)?;
                let d = self.result(op, 0);
                let off = body.types().field_offset(self.sp, ty, index).unwrap_or(0) as i64;
                self.add_imm(d, p, off);
            }
            OpKind::PtrIndex { ty, .. } => {
                let (p, i) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let d = self.result(op, 0);
                let stride = body.types().stride(self.sp, ty) as u64;
                let t = if stride.is_power_of_two() {
                    let t = self.fresh();
                    self.emit(Inst::ShiftImm {
                        op: ShiftImmOp::Lsl,
                        sf: Sf::X,
                        d: t,
                        n: i,
                        amount: stride.trailing_zeros() as u8,
                    });
                    t
                } else {
                    let s = self.konst(stride);
                    self.alu_new(AluOp::Mul, i, s)
                };
                self.alu(AluOp::Add, d, p, t);
            }
            OpKind::TySize(ty) | OpKind::TyAlign(ty) => {
                let (s, a) = body.types().dims(self.sp, ty);
                let x = if matches!(kind, OpKind::TySize(_)) {
                    s as u64
                } else {
                    a
                };
                let d = self.result(op, 0);
                self.mov_imm(d, x);
            }
            OpKind::TyOffset { ty, index } => {
                let off = body.types().field_offset(self.sp, ty, index).unwrap_or(0) as u64;
                let d = self.result(op, 0);
                self.mov_imm(d, off);
            }
            OpKind::MemGlobal { global } => {
                let g = self.cx.globals[body.str(global)];
                let d = self.result(op, 0);
                self.emit(Inst::Adrl { d, global: g });
            }
            OpKind::FuncAddr { callee } => {
                let func = self.cx.funcs[body.str(callee)];
                let d = self.result(op, 0);
                self.emit(Inst::AdrlFunc { d, func });
            }
            OpKind::Call { callee } => {
                let func = self.cx.funcs[body.str(callee)];
                let args = self.operands(op)?;
                let (ps, rs) = self.cx.sig(func);
                self.call(op, &args, ps.len(), rs.len(), |s| {
                    s.emit(Inst::Bl { func });
                });
            }
            OpKind::CallIndirect(sig) => {
                let args = self.operands(op)?;
                let Some(Shape::Func(ps, rs)) = body.types().shape_of(sig) else {
                    return Err(format!("{}not a function type", at(self.loc)));
                };
                let (ps, rs) = (ps.to_vec(), rs.to_vec());
                let (np, nr) = (ps.len(), rs.len());
                self.sigs.push((ps, rs));
                let sig = (self.sigs.len() - 1) as u32;
                let target = args[0];
                self.call(op, &args[1..], np, nr, |s| {
                    s.emit(Inst::Blr { n: target, sig });
                });
            }
            OpKind::If => {
                let c = self.operand(op, 0)?;
                let &[thn, els] = body.regions(op) else {
                    return Err("malformed cf.if".to_owned());
                };
                let results: Vec<Reg> = (0..body.results(op).len())
                    .map(|i| self.result(op, i))
                    .collect();
                let (t, e, join) = (
                    self.new_block(false),
                    self.new_block(false),
                    self.new_block(false),
                );
                self.branch_bit(c, t, e);
                self.ctx.push(Ctx::If { results, join });
                self.switch_to(t);
                self.region(thn)?;
                self.switch_to(e);
                self.region(els)?;
                self.ctx.pop();
                self.switch_to(join);
            }
            OpKind::Loop { .. } => {
                let inits = self.operands(op)?;
                let r = body.regions(op)[0];
                let params: Vec<Reg> = body.params(r).map(|v| self.val(v)).collect();
                let results: Vec<Reg> = (0..body.results(op).len())
                    .map(|i| self.result(op, i))
                    .collect();
                self.moves(&params, &inits);
                let (header, exit) = (self.new_block(false), self.new_block(false));
                self.emit(Inst::B { t: header });
                self.ctx.push(Ctx::Loop {
                    header,
                    exit,
                    params,
                    results,
                });
                self.switch_to(header);
                self.region(r)?;
                self.ctx.pop();
                self.switch_to(exit);
            }
            OpKind::Blocks { .. } => {
                let results: Vec<Reg> = (0..body.results(op).len())
                    .map(|i| self.result(op, i))
                    .collect();
                let mut labels = Vec::new();
                for &r in body.regions(op) {
                    let l = body.label(r).map_or("", |l| body.str(l)).to_owned();
                    let b = self.new_block(false);
                    let ps = body.params(r).map(|v| self.val(v)).collect();
                    labels.push((l, b, ps));
                }
                let exit = self.new_block(false);
                self.emit(Inst::B { t: labels[0].1 });
                let blocks: Vec<u32> = labels.iter().map(|l| l.1).collect();
                self.ctx.push(Ctx::Blocks {
                    labels,
                    results,
                    exit,
                });
                for (&r, &b) in body.regions(op).iter().zip(&blocks) {
                    self.switch_to(b);
                    self.region(r)?;
                }
                self.ctx.pop();
                self.switch_to(exit);
            }
            OpKind::Yield => {
                let vals = self.operands(op)?;
                self.yield_(&vals);
            }
            OpKind::Break => {
                let vals = self.operands(op)?;
                let (_, exit, _, results) = self.nearest_loop().expect("verified");
                self.moves(&results, &vals);
                self.emit(Inst::B { t: exit });
            }
            OpKind::Continue => {
                let vals = self.operands(op)?;
                let (header, _, params, _) = self.nearest_loop().expect("verified");
                self.moves(&params, &vals);
                self.emit(Inst::B { t: header });
            }
            OpKind::Ret => {
                let vals = self.operands(op)?;
                match self.res_ptr {
                    None => {
                        let dsts: Vec<Reg> = (0..vals.len() as u32).map(Reg::x).collect();
                        self.moves(&dsts, &vals);
                    }
                    Some(area) => {
                        for (i, &v) in vals.iter().enumerate() {
                            self.str_(MemSize::X, v, area, 8 * i as i64);
                        }
                    }
                }
                self.emit(Inst::B { t: self.exit });
            }
            OpKind::Br { dest } => {
                let s = body.succ(dest);
                let args = self.operands(op)?;
                self.jump(body.str(s.label), &args);
            }
            OpKind::CondBr { t, f } => {
                let (t, f) = (body.succ(t), body.succ(f));
                let all = self.operands(op)?;
                let c = all[0];
                let (ta, fa) = all[1..].split_at(t.nargs as usize);
                let tb = self.edge(body.str(t.label), ta);
                let fb = self.edge(body.str(f.label), fa);
                self.branch_bit(c, tb, fb);
            }
            OpKind::Switch { dflt, cases } => {
                let w = self.width_of(op, 0);
                let all = self.operands(op)?;
                let v = self.zx(all[0], w);
                let d = body.succ(dflt);
                let mut rest = &all[1..];
                let (da, r) = rest.split_at(d.nargs as usize);
                rest = r;
                let dblock = self.edge(body.str(d.label), da);
                let mut targets: Vec<(u64, u32)> = Vec::new();
                for c in body.cases(cases) {
                    let (args, r) = rest.split_at(c.succ.nargs as usize);
                    rest = r;
                    let b = self.edge(body.str(c.succ.label), args);
                    let k = int_low_bits(body.int(c.key)) & mask(w);
                    targets.push((k, b));
                }
                targets.sort_by_key(|t| t.0);
                self.switch_tree(v, &targets, dblock);
            }
            k => {
                return Err(format!(
                    "{}{} is not supported by the AArch64 backend",
                    at(self.loc),
                    k.mnemonic()
                ));
            }
        }
        Ok(())
    }

    fn family(&mut self, name: &str) -> u32 {
        match self.families.iter().position(|f| f == name) {
            Some(i) => i as u32,
            None => {
                self.families.push(name.to_owned());
                (self.families.len() - 1) as u32
            }
        }
    }

    /// A call: arguments where the convention puts them, the call, then the results.
    fn call(
        &mut self,
        op: OpId,
        args: &[Reg],
        _nparams: usize,
        nrets: usize,
        emit: impl FnOnce(&mut Self),
    ) {
        for (i, &a) in args.iter().enumerate().skip(8) {
            self.str_(MemSize::X, a, Reg::SP, 8 * (i as i64 - 8));
        }
        let area = (nrets > 2).then(|| self.local(8 * nrets as u64, 8));
        if let Some(off) = area {
            self.add_imm(Reg::x(8), Reg::SP, off);
        }
        let regs: Vec<Reg> = (0..args.len().min(8) as u32).map(Reg::x).collect();
        self.moves(&regs, &args[..regs.len()]);
        emit(self);
        let results: Vec<Reg> = (0..nrets).map(|i| self.result(op, i)).collect();
        match area {
            None => {
                for (i, &r) in results.iter().enumerate() {
                    self.mov(r, Reg::x(i as u32));
                }
            }
            Some(off) => {
                for (i, &r) in results.iter().enumerate() {
                    self.ldr(MemSize::X, r, Reg::SP, off + 8 * i as i64);
                }
            }
        }
    }

    /// Compare `v` (zero-extended) against sorted keys, branching to each case or the default.
    fn switch_tree(&mut self, v: Reg, targets: &[(u64, u32)], dflt: u32) {
        if targets.len() <= 3 {
            for &(k, b) in targets {
                self.cmp_imm(v, k as i64);
                let next = self.new_block(false);
                self.emit(Inst::BCond {
                    c: Cond::Eq,
                    t: b,
                    f: next,
                });
                self.switch_to(next);
            }
            self.emit(Inst::B { t: dflt });
            return;
        }
        let mid = targets.len() / 2;
        let (k, b) = targets[mid];
        self.cmp_imm(v, k as i64);
        let ne = self.new_block(false);
        self.emit(Inst::BCond {
            c: Cond::Eq,
            t: b,
            f: ne,
        });
        self.switch_to(ne);
        let (lo, hi) = (self.new_block(false), self.new_block(false));
        self.emit(Inst::BCond {
            c: Cond::Lo,
            t: lo,
            f: hi,
        });
        self.switch_to(lo);
        self.switch_tree(v, &targets[..mid], dflt);
        self.switch_to(hi);
        self.switch_tree(v, &targets[mid + 1..], dflt);
    }

    /// `mem.copy` of `size` bytes from `s` to `d`; overlap is allowed.
    fn copy(&mut self, d: Reg, s: Reg, size: u64) {
        if size == 0 {
            return;
        }
        if size <= 64 {
            // Read everything, then write it: overlap can't matter.
            let parts: Vec<(u64, MemSize, Reg)> = chunks(size)
                .map(|(o, sz)| {
                    let t = self.fresh();
                    self.ldr(sz, t, s, o as i64);
                    (o, sz, t)
                })
                .collect();
            for (o, sz, t) in parts {
                self.str_(sz, t, d, o as i64);
            }
            return;
        }
        // Copy forward when the destination is below the source, backward otherwise, in 8-byte
        // words with a byte-wise tail, so no byte is overwritten before it is read.
        let words = size / 8;
        let tail = size % 8;
        let (fwd, bwd, done) = (
            self.new_block(false),
            self.new_block(false),
            self.new_block(false),
        );
        self.alu(AluOp::Subs, Reg::XZR, d, s);
        self.emit(Inst::BCond {
            c: Cond::Ls,
            t: fwd,
            f: bwd,
        });
        // Forward: i from 0 up, then the tail.
        self.switch_to(fwd);
        let i = self.fresh();
        self.mov_imm(i, 0);
        let (head, body) = (self.new_block(false), self.new_block(false));
        self.emit(Inst::B { t: head });
        self.switch_to(head);
        self.cmp_imm(i, (8 * words) as i64);
        let ftail = self.new_block(false);
        self.emit(Inst::BCond {
            c: Cond::Lo,
            t: body,
            f: ftail,
        });
        self.switch_to(body);
        let (sa, da, t) = (
            self.alu_new(AluOp::Add, s, i),
            self.alu_new(AluOp::Add, d, i),
            self.fresh(),
        );
        self.emit(Inst::Ldr {
            size: MemSize::X,
            d: t,
            base: sa,
            off: 0,
        });
        self.emit(Inst::Str {
            size: MemSize::X,
            s: t,
            base: da,
            off: 0,
        });
        self.add_imm(i, i, 8);
        self.emit(Inst::B { t: head });
        self.switch_to(ftail);
        for k in 0..tail {
            let o = (8 * words + k) as i64;
            let t = self.fresh();
            self.ldr(MemSize::B, t, s, o);
            self.str_(MemSize::B, t, d, o);
        }
        self.emit(Inst::B { t: done });
        // Backward: the tail from the top, then words with i from the top down.
        self.switch_to(bwd);
        for k in (0..tail).rev() {
            let o = (8 * words + k) as i64;
            let t = self.fresh();
            self.ldr(MemSize::B, t, s, o);
            self.str_(MemSize::B, t, d, o);
        }
        let j = self.fresh();
        self.mov_imm(j, 8 * words);
        let (bhead, bbody) = (self.new_block(false), self.new_block(false));
        self.emit(Inst::B { t: bhead });
        self.switch_to(bhead);
        self.cmp_imm(j, 0);
        self.emit(Inst::BCond {
            c: Cond::Ne,
            t: bbody,
            f: done,
        });
        self.switch_to(bbody);
        self.add_imm(j, j, -8);
        let (sa, da, t) = (
            self.alu_new(AluOp::Add, s, j),
            self.alu_new(AluOp::Add, d, j),
            self.fresh(),
        );
        self.emit(Inst::Ldr {
            size: MemSize::X,
            d: t,
            base: sa,
            off: 0,
        });
        self.emit(Inst::Str {
            size: MemSize::X,
            s: t,
            base: da,
            off: 0,
        });
        self.emit(Inst::B { t: bhead });
        self.switch_to(done);
    }

    /// `int.add`, `int.sub`, `int.mul` with an overflow modifier.
    fn arith(&mut self, aop: ArithOp, ovf: Ovf, w: u32, d: Reg, a: Reg, b: Reg) {
        let op = match aop {
            ArithOp::Add => AluOp::Add,
            ArithOp::Sub => AluOp::Sub,
            ArithOp::Mul => AluOp::Mul,
        };
        match ovf {
            Ovf::Wrap | Ovf::Nsw | Ovf::Nuw | Ovf::NswNuw | Ovf::Ub(_) => self.alu(op, d, a, b),
            Ovf::Trap(signed) => {
                let (r, c) = self.overflow(aop, signed, w, a, b);
                self.trap_if(c, TrapReason::Overflow);
                self.mov(d, r);
            }
            Ovf::Sat(signed) => {
                let bound = self.sat_bound(aop, signed, w, a, b);
                let (r, c) = self.overflow(aop, signed, w, a, b);
                self.emit(Inst::Csel {
                    op: CselOp::Csel,
                    c,
                    sf: Sf::X,
                    d,
                    n: bound,
                    m: r,
                });
            }
        }
    }

    /// The bound a saturating op gives on overflow (computed without touching the flags).
    fn sat_bound(&mut self, aop: ArithOp, signed: bool, w: u32, a: Reg, b: Reg) -> Reg {
        if !signed {
            return match aop {
                ArithOp::Sub => self.konst(0),
                _ => self.konst(mask(w)),
            };
        }
        // MAX if the result should be positive, MIN if negative: sign ^ MAX.
        let max = self.konst(mask(w) >> 1);
        let sa = self.sx(a, w);
        let neg = match aop {
            ArithOp::Mul => {
                let sb = self.sx(b, w);
                self.alu_new(AluOp::Eor, sa, sb)
            }
            _ => sa,
        };
        let sign = self.fresh();
        self.emit(Inst::ShiftImm {
            op: ShiftImmOp::Asr,
            sf: Sf::X,
            d: sign,
            n: neg,
            amount: 63,
        });
        self.alu_new(AluOp::Eor, sign, max)
    }

    /// The wrapped result of `a op b`, and a condition that holds after it exactly when the
    /// op overflows (signed or unsigned) at width `w`.
    fn overflow(&mut self, aop: ArithOp, signed: bool, w: u32, a: Reg, b: Reg) -> (Reg, Cond) {
        let r = self.fresh();
        match aop {
            ArithOp::Add | ArithOp::Sub if w == 64 || w == 32 => {
                let sf = if w == 64 { Sf::X } else { Sf::W };
                let sub = aop == ArithOp::Sub;
                self.emit(Inst::Alu {
                    op: if sub { AluOp::Subs } else { AluOp::Adds },
                    sf,
                    d: r,
                    n: a,
                    m: b,
                });
                let c = match (signed, sub) {
                    (true, _) => Cond::Vs,
                    (false, false) => Cond::Hs,
                    (false, true) => Cond::Lo,
                };
                (r, c)
            }
            ArithOp::Add | ArithOp::Sub => {
                // The exact result fits in 64 bits; it overflows if it doesn't fit in w.
                let (ax, bx) = if signed {
                    (self.sx(a, w), self.sx(b, w))
                } else {
                    (self.zx(a, w), self.zx(b, w))
                };
                let op = if aop == ArithOp::Add {
                    AluOp::Add
                } else {
                    AluOp::Sub
                };
                self.alu(op, r, ax, bx);
                let t = if signed { self.sx(r, w) } else { self.zx(r, w) };
                self.alu(AluOp::Subs, Reg::XZR, t, r);
                (r, Cond::Ne)
            }
            ArithOp::Mul => {
                let (ax, bx) = if signed {
                    (self.sx(a, w), self.sx(b, w))
                } else {
                    (self.zx(a, w), self.zx(b, w))
                };
                self.alu(AluOp::Mul, r, ax, bx);
                // The high half must be the sign (or zero) of the low half, which must fit in w.
                let mut bad: Option<Reg> = None;
                if w > 32 {
                    let hi = self.alu_new(if signed { AluOp::Smulh } else { AluOp::Umulh }, ax, bx);
                    let ext = if signed {
                        let t = self.fresh();
                        self.emit(Inst::ShiftImm {
                            op: ShiftImmOp::Asr,
                            sf: Sf::X,
                            d: t,
                            n: r,
                            amount: 63,
                        });
                        t
                    } else {
                        Reg::XZR
                    };
                    self.alu(AluOp::Subs, Reg::XZR, hi, ext);
                    let f = self.fresh();
                    self.cset(f, Cond::Ne);
                    bad = Some(f);
                }
                if w < 64 {
                    let t = if signed { self.sx(r, w) } else { self.zx(r, w) };
                    self.alu(AluOp::Subs, Reg::XZR, t, r);
                    let f = self.fresh();
                    self.cset(f, Cond::Ne);
                    bad = Some(match bad {
                        Some(g) => self.alu_new(AluOp::Orr, g, f),
                        None => f,
                    });
                }
                let bad = bad.expect("some check applies");
                self.cmp_imm(bad, 0);
                (r, Cond::Ne)
            }
        }
    }

    /// Division and remainder with their edge cases.
    #[allow(clippy::too_many_arguments)]
    fn div(&mut self, dop: DivOp, zero: Edge, ovf: Edge, w: u32, d: Reg, a: Reg, b: Reg) {
        let signed = dop.signed();
        let (ax, bx) = if signed {
            (self.sx(a, w), self.sx(b, w))
        } else {
            (self.zx(a, w), self.zx(b, w))
        };
        if zero == Edge::Trap {
            self.cmp_imm(bx, 0);
            self.trap_if(Cond::Eq, TrapReason::Div0);
        }
        if signed && ovf == Edge::Trap {
            // MIN / -1: b is -1, then a is MIN.
            self.cmp_imm(bx, -1);
            let (check, cont) = (self.new_block(false), self.new_block(false));
            self.emit(Inst::BCond {
                c: Cond::Eq,
                t: check,
                f: cont,
            });
            self.switch_to(check);
            let min = self.konst((-1i64 << (w - 1)) as u64);
            self.alu(AluOp::Subs, Reg::XZR, ax, min);
            let t = self.trap_block(TrapReason::Overflow);
            self.emit(Inst::BCond {
                c: Cond::Eq,
                t,
                f: cont,
            });
            self.switch_to(cont);
        }
        let q = self.alu_new(if signed { AluOp::Sdiv } else { AluOp::Udiv }, ax, bx);
        match dop {
            DivOp::DivS | DivOp::DivU => self.mov(d, q),
            DivOp::RemS | DivOp::RemU => {
                let p = self.alu_new(AluOp::Mul, q, bx);
                self.alu(AluOp::Sub, d, ax, p);
            }
        }
    }

    /// Shifts with their edge case for amounts of at least the width.
    fn shift(&mut self, sop: ShiftOp, edge: ShiftEdge, w: u32, d: Reg, a: Reg, b: Reg) {
        let amt = self.zx(b, w);
        let amt = match edge {
            ShiftEdge::Trap => {
                self.cmp_imm(amt, i64::from(w));
                self.trap_if(Cond::Hs, TrapReason::Shift);
                amt
            }
            ShiftEdge::Mask if w.is_power_of_two() => {
                let t = self.fresh();
                self.emit(Inst::AluImm {
                    op: AluImmOp::And,
                    sf: Sf::X,
                    d: t,
                    n: amt,
                    imm: i64::from(w - 1),
                });
                t
            }
            ShiftEdge::Mask => {
                let n = self.konst(u64::from(w));
                let q = self.alu_new(AluOp::Udiv, amt, n);
                let p = self.alu_new(AluOp::Mul, q, n);
                self.alu_new(AluOp::Sub, amt, p)
            }
            ShiftEdge::Total if sop == ShiftOp::ShrS => {
                // Shifting by w - 1 or more leaves only the sign.
                let top = self.konst(u64::from(w - 1));
                self.cmp_imm(amt, i64::from(w - 1));
                let t = self.fresh();
                self.emit(Inst::Csel {
                    op: CselOp::Csel,
                    c: Cond::Hi,
                    sf: Sf::X,
                    d: t,
                    n: top,
                    m: amt,
                });
                t
            }
            ShiftEdge::Ub | ShiftEdge::Total => amt,
        };
        let r = match sop {
            ShiftOp::Shl => self.alu_new(AluOp::Lsl, a, amt),
            ShiftOp::ShrU => {
                let x = self.zx(a, w);
                self.alu_new(AluOp::Lsr, x, amt)
            }
            ShiftOp::ShrS => {
                let x = self.sx(a, w);
                self.alu_new(AluOp::Asr, x, amt)
            }
        };
        if edge == ShiftEdge::Total && sop != ShiftOp::ShrS {
            // Shifting by w or more shifts everything out.
            self.cmp_imm(amt, i64::from(w));
            self.emit(Inst::Csel {
                op: CselOp::Csel,
                c: Cond::Lo,
                sf: Sf::X,
                d,
                n: r,
                m: Reg::XZR,
            });
        } else {
            self.mov(d, r);
        }
    }
}

fn mask(w: u32) -> u64 {
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
}

fn sext(w: u32, x: u64) -> i64 {
    if w >= 64 || w == 0 {
        x as i64
    } else {
        ((x << (64 - w)) as i64) >> (64 - w)
    }
}

/// An integer's low 64 bits (two's complement).
fn int_low_bits(n: crate::body::Int<'_>) -> u64 {
    match n {
        crate::body::Int::Small(n) => n as u64,
        crate::body::Int::Big(n) => {
            let m = num_bigint::BigInt::from(1) << 64;
            let r = ((n % &m) + &m) % &m;
            u64::try_from(r).unwrap_or(0)
        }
    }
}

trait WidthBits {
    fn width_bits(self) -> u32;
}

impl WidthBits for Ty {
    fn width_bits(self) -> u32 {
        match self {
            Ty::Int(w) | Ty::Byte(w) => w,
            _ => 64,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn logical_immediates() {
        for x in [
            1u64,
            0xff,
            0xf0f0_f0f0_f0f0_f0f0,
            0x5555_5555_5555_5555,
            !0xf,
            1 << 63,
        ] {
            assert!(is_logical_imm(x, Sf::X), "{x:#x}");
        }
        for x in [0u64, u64::MAX, 0x1234, 5] {
            assert!(!is_logical_imm(x, Sf::X), "{x:#x}");
        }
        assert!(is_logical_imm(0xffff_0000, Sf::W));
    }

    #[test]
    fn chunks_cover_sizes() {
        for size in 1..20 {
            let cs: Vec<_> = chunks(size).collect();
            assert_eq!(cs.iter().map(|c| u64::from(c.1.bytes())).sum::<u64>(), size);
        }
    }
}
