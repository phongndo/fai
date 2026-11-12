//! The AArch64 LFIR machine, mirroring `spec/Fir/AArch64Machine.lean` (and the instruction
//! semantics of `spec/Fir/AArch64.lean`): how `fir run` runs a module in `layer lfir aarch64`.
//!
//! It is a register machine over the interpreter's memory, allocations, and events (this module
//! is a child of `interp`, so it uses the [`Machine`]'s private parts): registers `x0`…`x30` and
//! `sp` hold words (64 bits, or a pointer with its provenance), NZCV holds the flags, and each
//! call has a frame with its own virtual registers. Memory is flat: an integer address reaches
//! whichever live allocation holds those bytes. Calls follow AAPCS64; external calls are events,
//! answered with zeros, and leave the caller-saved registers zero (the oracle's choice).

use super::*;
use crate::body::StrId;
use crate::decl::Imm;

/// The machine stack's size (Lean's `stackSize`).
const STACK: u64 = 1 << 20;

/// What a register holds (Lean's `Word`). A pointer is an index into the machine's `ptrs`.
#[derive(Clone, Copy, Debug)]
enum Word {
    Bits(u64),
    Ptr(u32),
}

/// A running function (Lean's `LFrame`).
struct LFrame {
    func: u32,
    /// The function's `aarch64.code` op, whose regions are its blocks.
    code: OpId,
    next: Option<OpId>,
    /// Where its virtual registers start in `vregs`.
    vbase: u32,
    /// `x19`…`x29` and `sp` on entry.
    saved: [Word; 12],
}

struct Lfir<'m> {
    m: Machine<'m>,
    x: [Word; 31],
    sp: Word,
    nzcv: u8,
    frames: Vec<LFrame>,
    vregs: Vec<Option<Word>>,
    /// How many virtual registers each function names, once computed.
    nvregs: FxHashMap<u32, u32>,
    res_area: Word,
    hung: bool,
    /// The pending exception, if any (Lean's `LMachine.exn`).
    exn: Option<Word>,
}

/// Run function `f` of an LFIR module with `args`, and describe the outcome as `fir-ref run`
/// does (Lean's `AArch64.run`).
pub(super) fn run(m: Machine<'_>, f: u32, args: &[Value], fuel: u64) -> String {
    let mut l = Lfir {
        m,
        x: [Word::Bits(0); 31],
        sp: Word::Bits(0),
        nzcv: 0,
        frames: Vec::new(),
        vregs: Vec::new(),
        nvregs: FxHashMap::default(),
        res_area: Word::Bits(0),
        hung: false,
        exn: None,
    };
    match l.start(f, args) {
        Err(h) => h.render(),
        Ok(()) => l.drive(fuel),
    }
}

fn mask(n: u32) -> u64 {
    if n >= 64 { u64::MAX } else { (1u64 << n) - 1 }
}

/// `x`'s low `n` bits, sign-extended to 64.
fn sext(n: u32, x: u64) -> i64 {
    if n >= 64 {
        x as i64
    } else {
        ((x << (64 - n)) as i64) >> (64 - n)
    }
}

/// ASL's `AddWithCarry` on `n`-bit operands: the result and NZCV.
fn add_with_carry(n: u32, x: u64, y: u64, carry: bool) -> (u64, u8) {
    let (x, y) = (x & mask(n), y & mask(n));
    let c = u128::from(carry);
    let usum = u128::from(x) + u128::from(y) + c;
    let ssum = i128::from(sext(n, x)) + i128::from(sext(n, y)) + c as i128;
    let r = (usum as u64) & mask(n);
    let flags = nzcv(
        r >> (n - 1) & 1 == 1,
        r == 0,
        u128::from(r) != usum,
        i128::from(sext(n, r)) != ssum,
    );
    (r, flags)
}

fn nzcv(n: bool, z: bool, c: bool, v: bool) -> u8 {
    (u8::from(n) << 3) | (u8::from(z) << 2) | (u8::from(c) << 1) | u8::from(v)
}

/// Three-register data processing at size `sf` (Lean's `AArch64.alu`).
fn alu(op: AluOp, sf: Sf, x: u64, y: u64) -> (u64, Option<u8>) {
    let n = sf.bits();
    let (x, y) = (x & mask(n), y & mask(n));
    let r = match op {
        AluOp::Add => x.wrapping_add(y),
        AluOp::Adds => {
            let (r, f) = add_with_carry(n, x, y, false);
            return (r, Some(f));
        }
        AluOp::Sub => x.wrapping_sub(y),
        AluOp::Subs => {
            let (r, f) = add_with_carry(n, x, !y & mask(n), true);
            return (r, Some(f));
        }
        AluOp::And => x & y,
        AluOp::Ands => {
            let r = x & y;
            return (r, Some(nzcv(r >> (n - 1) & 1 == 1, r == 0, false, false)));
        }
        AluOp::Orr => x | y,
        AluOp::Eor => x ^ y,
        AluOp::Bic => x & !y,
        AluOp::Lsl => x << (y % u64::from(n)),
        AluOp::Lsr => x >> (y % u64::from(n)),
        AluOp::Asr => (sext(n, x) >> (y % u64::from(n))) as u64,
        AluOp::Mul => x.wrapping_mul(y),
        AluOp::Sdiv => {
            if y == 0 {
                0
            } else {
                sext(n, x).wrapping_div(sext(n, y)) as u64
            }
        }
        AluOp::Udiv => x.checked_div(y).unwrap_or(0),
        AluOp::Smulh => ((i128::from(sext(n, x)) * i128::from(sext(n, y))) >> n) as u64,
        AluOp::Umulh => ((u128::from(x) * u128::from(y)) >> n) as u64,
    };
    (r & mask(n), None)
}

fn alu_of_imm(op: AluImmOp) -> AluOp {
    match op {
        AluImmOp::Add => AluOp::Add,
        AluImmOp::Adds => AluOp::Adds,
        AluImmOp::Sub => AluOp::Sub,
        AluImmOp::Subs => AluOp::Subs,
        AluImmOp::And => AluOp::And,
        AluImmOp::Ands => AluOp::Ands,
        AluImmOp::Orr => AluOp::Orr,
        AluImmOp::Eor => AluOp::Eor,
    }
}

/// An integer immediate as 64 bits (Lean's `BitVec.ofInt 64`).
fn int_bits(n: Int<'_>) -> u64 {
    match n {
        Int::Small(n) => n as u64,
        Int::Big(n) => {
            let m = BigInt::from(1) << 64;
            let r = ((n % &m) + &m) % &m;
            u64::try_from(r).unwrap_or(0)
        }
    }
}

/// An integer immediate as an offset.
fn int_offset(n: Int<'_>) -> i128 {
    match n {
        Int::Small(n) => i128::from(n),
        Int::Big(n) => i128::try_from(n).unwrap_or(0),
    }
}

/// The callee-saved registers: `x19`…`x29`, then `sp` (Lean's `calleeSaved`).
fn callee_saved(i: usize) -> Reg {
    if i < 11 {
        Reg::x(19 + i as u32)
    } else {
        Reg::SP
    }
}

impl<'m> Lfir<'m> {
    fn body(&self) -> &'m Body {
        self.m.body()
    }

    // Registers

    fn read(&self, loc: Option<Loc>, r: Reg) -> R<Word> {
        match r {
            Reg::XZR => Ok(Word::Bits(0)),
            Reg::SP => Ok(self.sp),
            r if r.is_gpr() => Ok(self.x[r.0 as usize]),
            r => {
                let Some(f) = self.frames.last() else {
                    return stuck(loc, "no running function");
                };
                let i = (f.vbase + r.virt_index()) as usize;
                match self.vregs.get(i).copied().flatten() {
                    Some(w) => Ok(w),
                    None => stuck(loc, format!("{r} is read before it is written")),
                }
            }
        }
    }

    fn write(&mut self, r: Reg, w: Word) {
        match r {
            Reg::XZR => {}
            Reg::SP => self.sp = w,
            r if r.is_gpr() => self.x[r.0 as usize] = w,
            r => {
                if let Some(f) = self.frames.last() {
                    let i = (f.vbase + r.virt_index()) as usize;
                    if i >= self.vregs.len() {
                        self.vregs.resize(i + 1, None);
                    }
                    self.vregs[i] = Some(w);
                }
            }
        }
    }

    fn word_bits(&mut self, loc: Option<Loc>, w: Word) -> R<u64> {
        match w {
            Word::Bits(b) => Ok(b),
            Word::Ptr(p) => self.m.ptr_addr(loc, p),
        }
    }

    fn read_bits(&mut self, loc: Option<Loc>, r: Reg) -> R<u64> {
        let w = self.read(loc, r)?;
        self.word_bits(loc, w)
    }

    /// Lean's `offsetWord`.
    fn offset_word(&mut self, loc: Option<Loc>, w: Word, k: i128) -> R<Word> {
        match w {
            Word::Bits(b) => Ok(Word::Bits(b.wrapping_add(k as u64))),
            Word::Ptr(p) => match self.m.offset_by(false, p, k)? {
                Some(Value::Ptr(q)) => Ok(Word::Ptr(q)),
                _ => stuck(loc, "malformed pointer"),
            },
        }
    }

    fn ptr_word_eq(&self, a: Word, b: Word) -> bool {
        match (a, b) {
            (Word::Bits(x), Word::Bits(y)) => x == y,
            (Word::Ptr(p), Word::Ptr(q)) => self.m.ptr_eq(p, q),
            _ => false,
        }
    }

    // Memory

    /// The allocation and offset of the `size` bytes at `w` (Lean's `locate`).
    fn locate(&mut self, loc: Option<Loc>, w: Word, size: u64) -> R<(u32, u64)> {
        let addr = match w {
            Word::Ptr(p) => match self.m.ptrs[p as usize] {
                Ptr::Rel { alloc, off, .. } => {
                    let ai = alloc as usize;
                    if !self.m.allocs.live[ai] {
                        return ub(UbKind::UseAfterFree, loc, self.m.dead_note(alloc));
                    }
                    if let Kind::Func(f) = self.m.allocs.kind[ai] {
                        let f = self.m.fn_name(f);
                        return ub(UbKind::FuncAccess, loc, format!("@{f} is a function"));
                    }
                    let asize = self.m.allocs.size[ai];
                    if !(0 <= off && off + i128::from(size) <= i128::from(asize)) {
                        return ub(
                            UbKind::OutOfBounds,
                            loc,
                            format!("offset {off}, {size} bytes, allocation size {asize}"),
                        );
                    }
                    return Ok((alloc, off as u64));
                }
                Ptr::Abs { addr, .. } => addr,
            },
            Word::Bits(b) => b,
        };
        let a = &self.m.allocs;
        let hit = (1..a.size.len()).find(|&i| {
            a.live[i]
                && a.base[i] != 0
                && a.base[i] <= addr
                && u128::from(addr) + u128::from(size)
                    <= u128::from(a.base[i]) + u128::from(a.size[i])
        });
        match hit {
            Some(i) => Ok((i as u32, addr - a.base[i])),
            None => ub(
                UbKind::OutOfBounds,
                loc,
                format!("address {addr} is in no live allocation"),
            ),
        }
    }

    /// Lean's `wordOfBytes`.
    fn word_of_bytes(&mut self, loc: Option<Loc>, bs: &[Byte]) -> R<Word> {
        if bs.len() == 8
            && let Some(p) = self.m.ptr_of_frags(bs)
        {
            return Ok(Word::Ptr(p));
        }
        let mut n = 0u64;
        for (i, &b) in bs.iter().enumerate() {
            let d = match self.m.frag_to_bits(loc, b)? {
                Byte::Bits(x) => u64::from(x),
                // A `poison` byte: the oracle's choice, 0.
                _ => 0,
            };
            n |= d << (8 * i);
        }
        Ok(Word::Bits(n))
    }

    /// Lean's `bytesOfWord`.
    fn bytes_of_word(
        &mut self,
        loc: Option<Loc>,
        size: u64,
        w: Word,
        out: &mut Vec<Byte>,
    ) -> R<()> {
        out.clear();
        match (w, size) {
            (Word::Ptr(ptr), 8) => out.extend((0..8).map(|i| Byte::Frag { ptr, i })),
            _ => {
                let b = self.word_bits(loc, w)?;
                out.extend((0..size).map(|i| Byte::Bits((b >> (8 * i)) as u8)));
            }
        }
        Ok(())
    }

    fn load(&mut self, loc: Option<Loc>, size: u64, addr: Word) -> R<Word> {
        let (a, off) = self.locate(loc, addr, size)?;
        let mem = &self.m.allocs.bytes[a as usize];
        let bs: Vec<Byte> = (0..size).map(|i| mem.get(off + i)).collect();
        self.word_of_bytes(loc, &bs)
    }

    fn store(&mut self, loc: Option<Loc>, size: u64, addr: Word, v: Word) -> R<()> {
        let mut bs = Vec::with_capacity(8);
        self.bytes_of_word(loc, size, v, &mut bs)?;
        let (a, off) = self.locate(loc, addr, size)?;
        let mem = &mut self.m.allocs.bytes[a as usize];
        for (i, &b) in bs.iter().enumerate() {
            mem.set(off + i as u64, b);
        }
        Ok(())
    }

    // The calling convention

    /// Lean's `valOfWord`.
    fn val_of_word(&mut self, loc: Option<Loc>, t: Ty, w: Word) -> R<Value> {
        match t {
            Ty::Int(n) if n <= 64 => {
                let b = self.word_bits(loc, w)?;
                Ok(Value::Int {
                    w: n,
                    bits: b & mask(n),
                })
            }
            Ty::Ptr => Ok(Value::Ptr(match w {
                Word::Ptr(p) => p,
                Word::Bits(addr) => self.m.new_ptr(Ptr::Abs {
                    addr,
                    cands: Span { start: 0, len: 0 },
                }),
            })),
            Ty::Byte(n) if n <= 64 => {
                let mut bs = Vec::with_capacity(8);
                self.bytes_of_word(loc, 8, w, &mut bs)?;
                let start = self.m.byte_vals.len() as u32;
                self.m.byte_vals.extend_from_slice(&bs[..(n / 8) as usize]);
                Ok(Value::Bytes { start, len: n / 8 })
            }
            Ty::Int(_) | Ty::Byte(_) => stuck(loc, format!("{t} is wider than a register")),
            Ty::Agg(_) | Ty::Slice => stuck(loc, "not a value type"),
        }
    }

    /// Lean's `wordOfVal`.
    fn word_of_val(&mut self, loc: Option<Loc>, v: Value) -> R<Word> {
        Ok(match v {
            Value::Int { bits, .. } => Word::Bits(bits),
            Value::Wide { id, .. } => Word::Bits(
                self.m.wides[id as usize]
                    .iter_u64_digits()
                    .next()
                    .unwrap_or(0),
            ),
            Value::Poison { .. } | Value::PtrPoison => Word::Bits(0),
            Value::Ptr(p) => Word::Ptr(p),
            Value::Bytes { start, len } => {
                let bs = self.m.byte_vals[Span { start, len }.range()].to_vec();
                self.word_of_bytes(loc, &bs)?
            }
            Value::Agg { .. } => return stuck(loc, "an aggregate is not a register value"),
            Value::Unset => return stuck(loc, "no value"),
        })
    }

    /// Lean's `argVals`.
    fn arg_vals(&mut self, loc: Option<Loc>, ps: &[Ty]) -> R<Vec<Value>> {
        let mut out = Vec::with_capacity(ps.len());
        for (i, &t) in ps.iter().enumerate() {
            let w = if i < 8 {
                self.x[i]
            } else {
                let a = self.offset_word(loc, self.sp, 8 * (i as i128 - 8))?;
                self.load(loc, 8, a)?
            };
            out.push(self.val_of_word(loc, t, w)?);
        }
        Ok(out)
    }

    /// Lean's `setResults`.
    fn set_results(&mut self, loc: Option<Loc>, nrets: usize, vs: &[Value]) -> R<()> {
        if nrets <= 2 {
            for (i, &v) in vs.iter().enumerate() {
                self.x[i] = self.word_of_val(loc, v)?;
            }
        } else {
            let area = self.x[8];
            for (i, &v) in vs.iter().enumerate() {
                let a = self.offset_word(loc, area, 8 * i as i128)?;
                let w = self.word_of_val(loc, v)?;
                self.store(loc, 8, a, w)?;
            }
        }
        Ok(())
    }

    /// Lean's `clobber`: the oracle's choice, 0.
    fn clobber(&mut self, keep: usize) {
        for i in keep..19 {
            self.x[i] = Word::Bits(0);
        }
        self.x[30] = Word::Bits(0);
        self.nzcv = 0;
    }

    // Calls and returns

    fn saved_words(&self) -> [Word; 12] {
        let mut out = [Word::Bits(0); 12];
        for (i, w) in out.iter_mut().enumerate() {
            *w = match callee_saved(i) {
                Reg::SP => self.sp,
                r => self.x[r.0 as usize],
            };
        }
        out
    }

    fn rets(&self, f: u32) -> &'m [Ty] {
        let module: &'m Module = self.m.module;
        &module.funcs[f as usize].rets
    }

    /// Lean's `finish`: the outermost call's results (or the exception it threw) and the leaks.
    fn finish(&mut self, loc: Option<Loc>, f: u32) -> R<()> {
        if let Some(w) = self.exn {
            let v = self.val_of_word(loc, Ty::Ptr, w)?;
            let mut out = String::new();
            self.m.render_value(v, &mut out);
            return Err(Box::new(Halt {
                behavior: Behavior::Threw(out),
                loc,
                note: String::new(),
                leaks: self.m.leaks(),
            }));
        }
        let rets = self.rets(f);
        let mut ws = Vec::with_capacity(rets.len());
        for i in 0..rets.len() {
            ws.push(if rets.len() <= 2 {
                self.x[i]
            } else {
                let a = self.offset_word(loc, self.res_area, 8 * i as i128)?;
                self.load(loc, 8, a)?
            });
        }
        let mut out = String::new();
        for (i, (&t, &w)) in rets.iter().zip(&ws).enumerate() {
            let v = self.val_of_word(loc, t, w)?;
            if i > 0 {
                out.push_str(", ");
            }
            self.m.render_value(v, &mut out);
        }
        Err(Box::new(Halt {
            behavior: Behavior::Ret(out),
            loc,
            note: String::new(),
            leaks: self.m.leaks(),
        }))
    }

    /// How many virtual registers function `f` names.
    fn vreg_count(&mut self, f: u32) -> u32 {
        if let Some(&n) = self.nvregs.get(&f) {
            return n;
        }
        let body = &self.m.module.funcs[f as usize].body;
        let mut n = 0;
        let mut stack = vec![body.entry()];
        while let Some(r) = stack.pop() {
            for op in body.ops(r) {
                let k = body.kind(op);
                for i in 0..k.decl().imms.len() {
                    if let Some(Imm::Reg(r)) = k.imm(i)
                        && r.is_virtual()
                    {
                        n = n.max(r.virt_index() + 1);
                    }
                }
                stack.extend_from_slice(body.regions(op));
            }
        }
        self.nvregs.insert(f, n);
        n
    }

    /// Lean's `enter`.
    fn enter(&mut self, loc: Option<Loc>, f: u32) -> R<()> {
        let module: &'m Module = self.m.module;
        let func = &module.funcs[f as usize];
        let body = &func.body;
        let mut ops = body.ops(body.entry());
        let (Some(op), None) = (ops.next(), ops.next()) else {
            return stuck(
                loc,
                format!("@{}'s body must be aarch64.code or func.ret", func.name),
            );
        };
        match (body.kind(op), body.regions(op)) {
            (OpKind::A64Code, &[entry, ..]) => {
                let saved = self.saved_words();
                let n = self.vreg_count(f);
                let vbase = self.vregs.len() as u32;
                self.vregs.resize(self.vregs.len() + n as usize, None);
                self.frames.push(LFrame {
                    func: f,
                    code: op,
                    next: body.ops(entry).next(),
                    vbase,
                    saved,
                });
                self.m.func = f;
                Ok(())
            }
            (OpKind::Ret, []) => {
                let params: Vec<ValueId> = body.params(body.entry()).collect();
                let tys: Vec<Ty> = params.iter().map(|&v| body.ty(v)).collect();
                let vs = self.arg_vals(loc, &tys)?;
                let rloc = body.loc(op);
                let mut outs = Vec::with_capacity(func.rets.len());
                for &a in body.operands(op) {
                    match a.get() {
                        OperandKind::Value(v) => match params.iter().position(|&p| p == v) {
                            Some(i) => outs.push(vs[i]),
                            None => {
                                return stuck(rloc, format!("%{} is not defined", body.name(v)));
                            }
                        },
                        OperandKind::Hole(h) => {
                            return halt(Behavior::Hole(body.hole_name(h).to_owned()), rloc, "");
                        }
                    }
                }
                self.set_results(rloc, func.rets.len(), &outs)
            }
            _ => stuck(
                loc,
                format!("@{}'s body must be aarch64.code or func.ret", func.name),
            ),
        }
    }

    /// Lean's `callExt`: one event, then the results where the convention puts them.
    fn call_ext(&mut self, loc: Option<Loc>, x: u32) -> R<()> {
        let module: &'m Module = self.m.module;
        let ext = &module.externs[x as usize];
        let vs = self.arg_vals(loc, &ext.params)?;
        if vs.len() != ext.params.len()
            || !vs
                .iter()
                .zip(&ext.params)
                .all(|(&v, &t)| self.m.has_ty(v, t))
        {
            return stuck(loc, format!("wrong arguments for @{}", ext.name));
        }
        for (a, t) in self.m.extern_reach(ext, &vs) {
            if self.m.allocs.live[a as usize] {
                self.m.realize(loc, a)?;
                self.m.add_exposure(a, t);
            }
        }
        let mut trace = std::mem::take(&mut self.m.trace);
        trace.push('@');
        trace.push_str(&ext.name);
        trace.push('(');
        for (i, &v) in vs.iter().enumerate() {
            if i > 0 {
                trace.push_str(", ");
            }
            self.m.render_value(v, &mut trace);
        }
        trace.push_str(") -> ");
        if ext.rets.is_empty() {
            trace.push_str("()");
        }
        let mut rs = Vec::with_capacity(ext.rets.len());
        for (i, &t) in ext.rets.iter().enumerate() {
            if i > 0 {
                trace.push_str(", ");
            }
            let v = self.m.zero(t);
            self.m.render_value(v, &mut trace);
            rs.push(v);
        }
        trace.push_str("; ");
        self.m.trace = trace;
        self.set_results(loc, ext.rets.len(), &rs)?;
        self.clobber(if ext.rets.len() <= 2 {
            ext.rets.len()
        } else {
            0
        });
        Ok(())
    }

    /// Call function `f` (an index like `Kind::Func`'s).
    fn call(&mut self, loc: Option<Loc>, f: u32) -> R<()> {
        if f < self.m.nfuncs {
            self.x[30] = Word::Bits(0);
            self.enter(loc, f)
        } else {
            self.call_ext(loc, f - self.m.nfuncs)
        }
    }

    /// The function a word points to the start of (Lean's `funcAt`).
    fn func_at(&mut self, loc: Option<Loc>, w: Word) -> R<u32> {
        let by_alloc = |l: &Self, a: u32, off: i128| -> R<u32> {
            match l.m.allocs.kind[a as usize] {
                Kind::Func(f) if off == 0 => Ok(f),
                Kind::Func(f) => ub(
                    UbKind::BadCall,
                    loc,
                    format!("offset {off} is not the start of @{}", l.m.fn_name(f)),
                ),
                _ => ub(UbKind::BadCall, loc, format!("#{a} is not a function")),
            }
        };
        if let Word::Ptr(p) = w
            && let Ptr::Rel { alloc, off, .. } = self.m.ptrs[p as usize]
        {
            return by_alloc(self, alloc, off);
        }
        let addr = self.word_bits(loc, w)?;
        let a = &self.m.allocs;
        match (1..a.size.len())
            .find(|&i| matches!(a.kind[i], Kind::Func(_)) && a.base[i] == addr && addr != 0)
        {
            Some(i) => by_alloc(self, i as u32, 0),
            None => ub(
                UbKind::BadCall,
                loc,
                format!("address {addr} is not a function"),
            ),
        }
    }

    /// Lean's `ret`.
    fn ret(&mut self, loc: Option<Loc>) -> R<()> {
        let Some(f) = self.frames.last() else {
            return stuck(loc, "no running function");
        };
        let now = self.saved_words();
        for (i, (&was, &is)) in f.saved.iter().zip(&now).enumerate() {
            if !self.ptr_word_eq(was, is) {
                let name = &self.m.module.funcs[f.func as usize].name;
                return stuck(loc, format!("@{name} doesn't preserve {}", callee_saved(i)));
            }
        }
        let f = self.frames.pop().unwrap();
        self.vregs.truncate(f.vbase as usize);
        match self.frames.last() {
            Some(below) => {
                self.m.func = below.func;
                Ok(())
            }
            None => self.finish(loc, f.func),
        }
    }

    fn jump(&mut self, loc: Option<Loc>, label: StrId) -> R<()> {
        let body = self.body();
        let Some(f) = self.frames.last_mut() else {
            return stuck(loc, "no running function");
        };
        let want = body.str(label);
        match body
            .regions(f.code)
            .iter()
            .find(|&&r| body.label(r).is_some_and(|l| body.str(l) == want))
        {
            Some(&r) => {
                f.next = body.ops(r).next();
                Ok(())
            }
            None => stuck(loc, format!("no block ^{want}")),
        }
    }

    /// Lean's `addSub`: `add` and `sub` at 64 bits keep a pointer operand's provenance.
    fn add_sub(&mut self, loc: Option<Loc>, sub: bool, a: Word, b: Word) -> R<Option<Word>> {
        Ok(match (a, b, sub) {
            (Word::Ptr(_), Word::Bits(k), _) => {
                let k = i128::from(k as i64);
                Some(self.offset_word(loc, a, if sub { -k } else { k })?)
            }
            (Word::Bits(k), Word::Ptr(_), false) => {
                Some(self.offset_word(loc, b, i128::from(k as i64))?)
            }
            _ => None,
        })
    }

    /// Lean's `ptrOfWord`.
    fn ptr_of_word(&mut self, w: Word) -> u32 {
        match w {
            Word::Ptr(p) => p,
            Word::Bits(0) => NULL,
            Word::Bits(n) => {
                let a = &self.m.allocs;
                let starts = (1..a.size.len()).find(|&i| a.live[i] && a.base[i] == n);
                let holds = || {
                    (1..a.size.len()).find(|&i| {
                        a.live[i]
                            && a.base[i] != 0
                            && a.base[i] <= n
                            && u128::from(n) < u128::from(a.base[i]) + u128::from(a.size[i])
                    })
                };
                match starts.or_else(holds) {
                    Some(i) => {
                        let off = i128::from(n) - i128::from(a.base[i]);
                        self.m.new_ptr(Ptr::Rel {
                            alloc: i as u32,
                            tag: 0,
                            off,
                        })
                    }
                    None => self.m.new_ptr(Ptr::Abs {
                        addr: n,
                        cands: Span { start: 0, len: 0 },
                    }),
                }
            }
        }
    }

    fn sel(&mut self, loc: Option<Loc>, sf: Sf, r: Reg) -> R<Word> {
        match sf {
            Sf::X => self.read(loc, r),
            Sf::W => Ok(Word::Bits(self.read_bits(loc, r)? & mask(32))),
        }
    }

    // Instructions

    /// Lean's `exec`.
    fn exec(&mut self, op: OpId) -> R<()> {
        let body = self.body();
        let loc = body.loc(op);
        match body.kind(op) {
            OpKind::A64Alu { op, sf, d, n, m } => {
                let (a, b) = (self.read(loc, n)?, self.read(loc, m)?);
                let kept = match (sf, op) {
                    (Sf::X, AluOp::Add) => self.add_sub(loc, false, a, b)?,
                    (Sf::X, AluOp::Sub) => self.add_sub(loc, true, a, b)?,
                    _ => None,
                };
                match kept {
                    Some(w) => self.write(d, w),
                    None => {
                        let (x, y) = (self.word_bits(loc, a)?, self.word_bits(loc, b)?);
                        let (r, f) = alu(op, sf, x, y);
                        self.write(d, Word::Bits(r));
                        if let Some(f) = f {
                            self.nzcv = f;
                        }
                    }
                }
            }
            OpKind::A64AluImm { op, sf, d, n, imm } => {
                let a = self.read(loc, n)?;
                let k = int_bits(body.int(imm));
                let kept = match (sf, op) {
                    (Sf::X, AluImmOp::Add) => self.add_sub(loc, false, a, Word::Bits(k))?,
                    (Sf::X, AluImmOp::Sub) => self.add_sub(loc, true, a, Word::Bits(k))?,
                    _ => None,
                };
                match kept {
                    Some(w) => self.write(d, w),
                    None => {
                        let x = self.word_bits(loc, a)?;
                        let (r, f) = alu(alu_of_imm(op), sf, x, k);
                        self.write(d, Word::Bits(r));
                        if let Some(f) = f {
                            self.nzcv = f;
                        }
                    }
                }
            }
            OpKind::A64ShiftImm {
                op,
                sf,
                d,
                n,
                amount,
            } => {
                let bits = sf.bits();
                if amount >= bits {
                    return stuck(loc, format!("shift amount {amount} is not below {bits}"));
                }
                let x = self.read_bits(loc, n)? & mask(bits);
                let r = match op {
                    ShiftImmOp::Lsl => x << amount,
                    ShiftImmOp::Lsr => x >> amount,
                    ShiftImmOp::Asr => (sext(bits, x) >> amount) as u64,
                };
                self.write(d, Word::Bits(r & mask(bits)));
            }
            OpKind::A64Ext {
                signed,
                sf,
                d,
                n,
                width,
            } => {
                let bits = sf.bits();
                if !(1..=bits).contains(&width) {
                    return stuck(loc, format!("width {width} is not in 1..{bits}"));
                }
                let x = self.read_bits(loc, n)? & mask(width);
                let r = if signed { sext(width, x) as u64 } else { x };
                self.write(d, Word::Bits(r & mask(bits)));
            }
            OpKind::A64Mov { sf, d, n } => {
                let w = self.sel(loc, sf, n)?;
                self.write(d, w);
            }
            OpKind::A64MovWide { op, sf, d, imm, hw } => {
                let bits = sf.bits();
                if !(imm < 65536 && hw.is_multiple_of(16) && hw < bits) {
                    return stuck(loc, "malformed move");
                }
                let old = match op {
                    MovOp::Movk => self.read_bits(loc, d)?,
                    _ => 0,
                };
                let v = u64::from(imm) << hw;
                let r = match op {
                    MovOp::Movz => v,
                    MovOp::Movn => !v,
                    MovOp::Movk => (old & !(0xffff << hw)) | v,
                };
                self.write(d, Word::Bits(r & mask(bits)));
            }
            OpKind::A64Csel { op, c, sf, d, n, m } => {
                if c.holds(self.nzcv) {
                    let w = self.sel(loc, sf, n)?;
                    self.write(d, w);
                } else if op == CselOp::Csel && sf == Sf::X {
                    let w = self.read(loc, m)?;
                    self.write(d, w);
                } else {
                    let y = self.read_bits(loc, m)?;
                    let r = match op {
                        CselOp::Csel => y,
                        CselOp::Csinc => y.wrapping_add(1),
                        CselOp::Csinv => !y,
                        CselOp::Csneg => 0u64.wrapping_sub(y),
                    };
                    self.write(d, Word::Bits(r & mask(sf.bits())));
                }
            }
            OpKind::A64Ldr { size, d, base, off } => {
                let b = self.read(loc, base)?;
                let a = self.offset_word(loc, b, int_offset(body.int(off)))?;
                let w = self.load(loc, size.bytes().into(), a)?;
                self.write(d, w);
            }
            OpKind::A64Str { size, s, base, off } => {
                let b = self.read(loc, base)?;
                let a = self.offset_word(loc, b, int_offset(body.int(off)))?;
                let v = self.read(loc, s)?;
                self.store(loc, size.bytes().into(), a, v)?;
            }
            OpKind::A64Adrl { d, global } => {
                let name = body.str(global);
                match self.m.globals.get(name) {
                    Some(&p) => self.write(d, Word::Ptr(p)),
                    None => return stuck(loc, format!("no global @{name}")),
                }
            }
            OpKind::A64AdrlFunc { d, callee } => {
                let name = body.str(callee);
                let Some(&f) = self.m.funcs.get(name) else {
                    return stuck(loc, format!("no function @{name}"));
                };
                if self.m.fn_ptrs[f as usize] == NONE {
                    self.m.fn_ptrs[f as usize] = self.m.new_alloc(loc, 0, 1, Kind::Func(f));
                }
                self.write(d, Word::Ptr(self.m.fn_ptrs[f as usize]));
            }
            OpKind::A64B { dest } => self.jump(loc, body.succ(dest).label)?,
            OpKind::A64BCond { c, t, f } => {
                let s = if c.holds(self.nzcv) { t } else { f };
                self.jump(loc, body.succ(s).label)?;
            }
            OpKind::A64Ret => self.ret(loc)?,
            OpKind::A64ExnSet { n } => self.exn = Some(self.read(loc, n)?),
            OpKind::A64ExnTake { d } => {
                let Some(w) = self.exn.take() else {
                    return stuck(loc, "no exception is pending");
                };
                self.write(d, w);
            }
            OpKind::A64BExn { t, f } => {
                let s = if self.exn.is_some() { t } else { f };
                self.jump(loc, body.succ(s).label)?;
            }
            OpKind::A64Trap(r) => return halt(Behavior::Trap(r), loc, ""),
            OpKind::A64Bl { callee } => {
                let name = body.str(callee);
                let Some(&f) = self.m.funcs.get(name) else {
                    return stuck(loc, format!("no function @{name}"));
                };
                self.call(loc, f)?;
            }
            OpKind::A64Blr { n, .. } => {
                let w = self.read(loc, n)?;
                let f = self.func_at(loc, w)?;
                self.call(loc, f)?;
            }
            OpKind::A64BlAlloc { family, align } => {
                let size = self.read_bits(loc, Reg::x(0))?;
                let fam = self.m.family(body.str(family));
                let p = self.m.new_alloc(loc, size, align, Kind::Heap(fam));
                self.x[0] = Word::Ptr(p);
                self.clobber(1);
            }
            OpKind::A64BlFree { family } => {
                let p = self.ptr_of_word(self.x[0]);
                self.m.free(loc, body.str(family), Some(p))?;
                self.clobber(0);
            }
            k => return stuck(loc, format!("{} can't run in LFIR", k.mnemonic())),
        }
        Ok(())
    }

    fn step(&mut self) -> R<()> {
        if self.hung {
            return Ok(());
        }
        let body = self.body();
        let Some(f) = self.frames.last_mut() else {
            return stuck(None, "no running function");
        };
        let Some(op) = f.next else {
            return stuck(None, "a block ended without a terminator");
        };
        f.next = body.next(op);
        self.exec(op)
    }

    /// Lean's `start`.
    fn start(&mut self, f: u32, args: &[Value]) -> R<()> {
        let p = self.m.new_alloc(None, STACK, 16, Kind::Stack);
        self.sp = self.offset_word(None, Word::Ptr(p), i128::from(STACK))?;
        let nrets = self.rets(f).len();
        let down = |l: &mut Self, n: usize| -> R<()> {
            let n = n.div_ceil(16) * 16;
            l.sp = l.offset_word(None, l.sp, -(n as i128))?;
            Ok(())
        };
        if nrets > 2 {
            down(self, 8 * nrets)?;
            self.res_area = self.sp;
            self.x[8] = self.sp;
        }
        if args.len() > 8 {
            down(self, 8 * (args.len() - 8))?;
            for (i, &v) in args[8..].iter().enumerate() {
                let a = self.offset_word(None, self.sp, 8 * i as i128)?;
                let w = self.word_of_val(None, v)?;
                self.store(None, 8, a, w)?;
            }
        }
        for (i, &v) in args.iter().take(8).enumerate() {
            self.x[i] = self.word_of_val(None, v)?;
        }
        self.enter(None, f)?;
        if self.frames.is_empty() {
            self.finish(None, f)?;
        }
        Ok(())
    }

    /// Lean's `drive`. A step that halts adds no events, as Lean renders the trace from before
    /// the step.
    fn drive(&mut self, fuel: u64) -> String {
        let mut steps = 0;
        loop {
            if steps >= fuel {
                return format!("{}out of fuel after {fuel} steps", self.m.trace);
            }
            let mark = self.m.trace.len();
            if let Err(h) = self.step() {
                self.m.trace.truncate(mark);
                return format!("{}{}", self.m.trace, h.render());
            }
            steps += 1;
        }
    }
}
