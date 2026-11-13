//! Instruction selection: MFIR (or HFIR made of core ops) to x86-64 machine code over virtual
//! registers.
//!
//! Every SSA value gets a virtual register; region parameters (loop state, block arguments, the
//! results of `cf.if`, `cf.loop`, and `cf.blocks`) are virtual registers written by moves where
//! control reaches them. Structured control flow becomes blocks and branches, laid out in source
//! order with the exit block and trap blocks last.
//!
//! **Integers.** An `iN` (N ≤ 64) lives in the low N bits of a 64-bit register; the bits above
//! are unspecified. Ops whose result's low bits depend only on their operands' low bits (add,
//! sub, mul, logic, `shl`) use them as they are; the others (comparisons, division, right shifts,
//! extensions, overflow checks) sign- or zero-extend their operands to 64 bits first. Wider
//! integers are held as their low 64 bits where only those bits matter, as on AArch64
//! (`low_bits_only`), which covers the lowering of `ptr.index.inbounds`; elsewhere they are
//! rejected.
//!
//! **Edge cases** follow the op's modifiers. `.wrap`, `.nsw`, `.nuw`, and `.ub` compute the
//! wrapped result (poison and UB allow any value); `.trap` branches to a trap block when the
//! op overflows, and `.sat` selects the bound (`cmov`). x86-64's `div` and `idiv` fault on a zero
//! divisor and on 64-bit `MIN / -1`, where AArch64's give a value, so where the modifier defines
//! a result (`.total`, `.wrap`) a branch around the division gives it (`x / 0 = 0`,
//! `x rem 0 = x`, `MIN / -1 = MIN`, `MIN rem -1 = 0`); `.ub` lets the hardware fault, which UB
//! allows. Below 64 bits the operands are extended first, so `MIN / -1` can't fault there. Shifts
//! put the amount in `cl`; amounts of at least the width trap, are reduced modulo the width, or
//! give the all-shifted-out value, as the modifier says. `poison` is 0.
//!
//! **Memory.** `mem.stack` slots are fixed frame slots addressed from `rsp`; loads and stores of
//! odd sizes split into 8-, 4-, 2-, and 1-byte accesses; `mem.copy` copies up to 64 bytes
//! through registers (all loads before any store, so overlap is fine) and calls `memmove` above
//! that. `mem.alloc` calls `malloc` (`aligned_alloc` above 16-byte alignment) and `mem.free`
//! calls `free`, for every family.
//!
//! **Calls** follow the System V AMD64 ABI for integers and pointers: arguments in `rdi`, `rsi`,
//! `rdx`, `rcx`, `r8`, `r9`, then 8-byte stack slots in order; one or two results in `rax` and
//! `rdx`; three or more in 8-byte slots of memory whose address the caller passes in `rdi` (as C
//! returns a struct of 8-byte fields larger than 16 bytes), which shifts the arguments by one. A
//! call of a variadic function sets `al` to 0 (no vector registers). C callees assume their
//! caller extended `char`, `short`, and `_Bool` arguments to 32 bits by their signedness, which
//! FIR's signatures don't record, so an external or indirect call with an integer argument
//! narrower than 32 bits is refused; FIR's own callees extend what they need themselves.
//!
//! **Exceptions** use AArch64's error-return convention (decision: Exceptions at run time):
//! `exn.throw` makes its value the pending exception in `__fir_exn` and returns through the
//! epilogue; after each call that may throw, a test of the slot's flag returns at once (a plain
//! call) or takes the exception and jumps to the handler (`func.invoke`).
//!
//! **Not yet:** floats, variadic functions defined in FIR (`va.*`), structs and arrays by value,
//! and HFIR's building blocks (lower first): each is a compile error.

use rustc_hash::FxHashMap;

use super::mir::*;
use crate::body::{Body, OpId, OperandKind, RegionId, ValueId};
use crate::contract::Support;
use crate::ir::ShiftOp as ShiftOp2;
use crate::ir::{
    AllocFail, ArithOp, BitOp, DivOp, Edge, Loc, Module, OpKind, Ovf, Pred, Shape, ShiftEdge,
    SpaceCfg, Ty,
};
use crate::sem::TrapReason;
use crate::types::{Types, align_up};

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

/// Where an argument goes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ArgLoc {
    Reg(Reg),
    /// An 8-byte stack slot at this offset from the stack pointer at the call.
    Stack(u32),
}

/// Whether a function with these results returns them in memory (three or more).
pub fn in_memory(rets: &[Ty]) -> bool {
    rets.len() > 2
}

/// Where `n` arguments go, with a results area's address first when `sret`; and the size of the
/// stack area they take.
pub fn arg_locs(n: usize, sret: bool) -> (Vec<ArgLoc>, u32) {
    let first = usize::from(sret);
    let mut stack = 0;
    let locs = (first..first + n)
        .map(|i| match ARG_REGS.get(i) {
            Some(&r) => ArgLoc::Reg(r),
            None => {
                stack += 8;
                ArgLoc::Stack(stack - 8)
            }
        })
        .collect();
    (locs, stack)
}

/// The registers a call of this signature reads and writes; `variadic` adds `al`.
pub fn call_shape(params: &[Ty], rets: &[Ty], variadic: bool) -> CallShape {
    let sret = in_memory(rets);
    let mut args: Vec<Reg> = if sret { vec![RDI] } else { Vec::new() };
    args.extend(
        arg_locs(params.len(), sret)
            .0
            .into_iter()
            .filter_map(|l| match l {
                ArgLoc::Reg(r) => Some(r),
                ArgLoc::Stack(_) => None,
            }),
    );
    if variadic {
        args.push(RAX);
    }
    let rets = if sret {
        vec![RAX]
    } else {
        RET_REGS[..rets.len()].to_vec()
    };
    CallShape { args, rets }
}

/// What the module tells the selection of one function.
pub struct ModuleCx<'a> {
    pub m: &'a Module,
    /// Functions, then external functions, by name: the callee indices of calls.
    pub funcs: FxHashMap<&'a str, u32>,
    pub globals: FxHashMap<&'a str, u32>,
    /// Which of the module's functions may return with an exception pending.
    pub throws: Vec<bool>,
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
        ModuleCx {
            m,
            funcs,
            globals,
            throws: crate::codegen::may_throw(m),
        }
    }

    fn variadic(&self, f: u32) -> bool {
        match self.m.funcs.get(f as usize) {
            Some(func) => func.variadic,
            None => self.m.externs[f as usize - self.m.funcs.len()].variadic,
        }
    }

    fn is_extern(&self, f: u32) -> bool {
        f as usize >= self.m.funcs.len()
    }
}

/// Check that a module can be compiled: 64-bit pointers and addresses, MFIR or HFIR, and
/// external functions of supported types.
pub fn check_module(m: &Module) -> Result<()> {
    if m.space.ptr_bits != 64 || m.space.addr_bits != 64 {
        return Err(format!(
            "the x86-64 backend needs 64-bit pointers and addresses, not ptr {} addr {}",
            m.space.ptr_bits, m.space.addr_bits
        ));
    }
    // Selection and the ABI hard-code System V's alignments, which are the default layout's
    // (AAPCS64's agree for integers and pointers); a module laid out otherwise would compile
    // into code that disagrees with its own semantics. The `va_list` layout isn't used: the
    // `va.*` ops are refused.
    let sysv = crate::ir::SpaceCfg::default();
    if m.space.ptr_align != sysv.ptr_align || m.space.ints != sysv.ints {
        let ints = |s: &crate::ir::SpaceCfg| {
            s.ints
                .iter()
                .map(|(w, a)| format!("{w}:{a}"))
                .collect::<Vec<_>>()
                .join(" ")
        };
        return Err(format!(
            "the x86-64 backend needs System V's data layout (ptr align {}, int {}), not ptr \
             align {}, int {}",
            sysv.ptr_align,
            ints(&sysv),
            m.space.ptr_align,
            ints(&m.space)
        ));
    }
    if let crate::Layer::Lfir(_) = m.layer {
        return Err("the module is already LFIR".to_owned());
    }
    for x in &m.externs {
        if x.variadic && in_memory(&x.rets) {
            return Err(format!(
                "extern @{}: a variadic function with more than two results",
                x.name
            ));
        }
        for &t in x.params.iter().chain(&x.rets) {
            check_ty(&m.globals.types, None, t).map_err(|e| format!("extern @{}: {e}", x.name))?;
        }
    }
    for f in &m.funcs {
        if f.variadic {
            return Err(format!(
                "@{}: variadic functions aren't supported by the x86-64 backend yet",
                f.name
            ));
        }
    }
    Ok(())
}

const FLOATS: Support =
    Support::No("is a float op: floats aren't supported by the x86-64 backend yet");
const VARARGS: Support =
    Support::No("is a varargs op: variadic functions aren't supported by the x86-64 backend yet");
const COMPOSITES: Support = Support::No(
    "makes or takes apart a struct or array passed whole: structs and arrays by value aren't supported by the x86-64 backend yet",
);

/// What instruction selection does with ops of a kind ([`crate::contract`]): the integer,
/// pointer, memory, control-flow, call, and exception ops of MFIR, and `ptr.field` and
/// `ptr.index`; not yet floats, `va.*`, or the composites calls pass whole. The HFIR building
/// blocks need lowering first, and LFIR is already selected. Integers wider than 64 bits are a
/// separate, per-type limit ([`check_module`], `check_ty`).
#[deny(clippy::wildcard_enum_match_arm)]
pub fn support(k: OpKind) -> Support {
    const HFIR: Support = Support::No(
        "is HFIR only: lower the module to MFIR first (`fir::lower_checked`, or `fir::backend::prepare`)",
    );
    const LFIR: Support = Support::No("is LFIR: it is already selected");
    match k {
        OpKind::Const(_)
        | OpKind::Poison
        | OpKind::Freeze
        | OpKind::Copy
        | OpKind::Select
        | OpKind::Arith(..)
        | OpKind::Bit(_)
        | OpKind::Div(..)
        | OpKind::Shift(..)
        | OpKind::Cmp(_)
        | OpKind::Zext
        | OpKind::Sext
        | OpKind::Trunc(_)
        | OpKind::MemStack { .. }
        | OpKind::MemAlloc { .. }
        | OpKind::MemFree { .. }
        | OpKind::Load { .. }
        | OpKind::Store { .. }
        | OpKind::PtrOffset { .. }
        | OpKind::PtrAddr
        | OpKind::PtrExpose
        | OpKind::PtrFromExposed
        | OpKind::PtrWithAddr
        | OpKind::PtrNull
        | OpKind::PtrCmp(_)
        | OpKind::Call { .. }
        | OpKind::If
        | OpKind::Loop { .. }
        | OpKind::Yield
        | OpKind::Break
        | OpKind::Continue
        | OpKind::Ret
        | OpKind::Blocks { .. }
        | OpKind::Br { .. }
        | OpKind::CondBr { .. }
        | OpKind::Switch { .. }
        | OpKind::TySize(_)
        | OpKind::TyAlign(_)
        | OpKind::TyOffset { .. }
        | OpKind::PtrField { .. }
        | OpKind::PtrIndex { .. }
        | OpKind::MemStackOf { .. }
        | OpKind::MemCopy { .. }
        | OpKind::MemGlobal { .. }
        | OpKind::FuncAddr { .. }
        | OpKind::CallIndirect(_)
        | OpKind::Check(_)
        | OpKind::Throw
        | OpKind::Invoke { .. }
        | OpKind::InvokeIndirect { .. } => Support::Yes,
        OpKind::FloatConst { .. }
        | OpKind::FloatBin(_)
        | OpKind::FloatUn(_)
        | OpKind::FloatFma
        | OpKind::FloatCmp(_)
        | OpKind::FloatExt
        | OpKind::FloatTrunc
        | OpKind::FloatToInt { .. }
        | OpKind::IntToFloat { .. }
        | OpKind::FloatFromBits
        | OpKind::FloatToBits => FLOATS,
        OpKind::VaStart | OpKind::VaArg | OpKind::VaEnd => VARARGS,
        OpKind::AggMake | OpKind::AggExtract { .. } | OpKind::AggInsert { .. } => COMPOSITES,
        OpKind::Overflow { .. }
        | OpKind::UnionMake { .. }
        | OpKind::UnionTag
        | OpKind::UnionGet { .. }
        | OpKind::SliceMake
        | OpKind::SlicePtr
        | OpKind::SliceLen
        | OpKind::SliceGet { .. }
        | OpKind::SliceSet { .. }
        | OpKind::Try => HFIR,
        OpKind::A64Code
        | OpKind::A64Alu { .. }
        | OpKind::A64AluImm { .. }
        | OpKind::A64ShiftImm { .. }
        | OpKind::A64Ext { .. }
        | OpKind::A64Mov { .. }
        | OpKind::A64MovWide { .. }
        | OpKind::A64Csel { .. }
        | OpKind::A64Ldr { .. }
        | OpKind::A64Str { .. }
        | OpKind::A64Adrl { .. }
        | OpKind::A64AdrlFunc { .. }
        | OpKind::A64B { .. }
        | OpKind::A64BCond { .. }
        | OpKind::A64Ret
        | OpKind::A64Trap(_)
        | OpKind::A64Bl { .. }
        | OpKind::A64Blr { .. }
        | OpKind::A64BlAlloc { .. }
        | OpKind::A64ExnSet { .. }
        | OpKind::A64ExnTake { .. }
        | OpKind::A64BExn { .. }
        | OpKind::A64Falu { .. }
        | OpKind::A64Funary { .. }
        | OpKind::A64Fmadd { .. }
        | OpKind::A64FmovImm { .. }
        | OpKind::A64Fcmp { .. }
        | OpKind::A64Fcsel { .. }
        | OpKind::A64Fcvt { .. }
        | OpKind::A64Cvtf { .. }
        | OpKind::A64Fcvtz { .. }
        | OpKind::A64BlFree { .. } => LFIR,
    }
}

/// Whether an op's results, and its operands, may be integers wider than 64 bits, held as
/// their low 64 bits: the ops whose results' low 64 bits depend only on their operands' (as
/// on AArch64; see `crate::backend::aarch64::isel`).
fn low_bits_only(k: OpKind) -> (bool, bool) {
    match k {
        OpKind::Const(_) | OpKind::Copy | OpKind::Freeze | OpKind::Select | OpKind::Bit(_) => {
            (true, true)
        }
        OpKind::Arith(_, ovf) => {
            let ok = !matches!(ovf, Ovf::Trap(_) | Ovf::Sat(_));
            (ok, ok)
        }
        OpKind::Zext | OpKind::Sext => (true, false),
        OpKind::Trunc(_) => (true, true),
        _ => (false, false),
    }
}

fn check_ty(types: &Types, loc: Option<Loc>, t: Ty) -> Result<()> {
    match t {
        Ty::Int(w) | Ty::Byte(w) if w > 64 => Err(format!(
            "{}{t} is wider than 64 bits, which the x86-64 backend doesn't support yet",
            at(loc)
        )),
        Ty::Float(_) => Err(format!(
            "{}floats aren't supported by the x86-64 backend yet",
            at(loc)
        )),
        _ if types.is_composite(t) => Err(format!(
            "{}structs and arrays by value aren't supported by the x86-64 backend yet",
            at(loc)
        )),
        _ if !t.is_value() => Err(format!(
            "{}a value of an aggregate, union, or slice type is HFIR only: lower the module to MFIR first",
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
fn chunks(size: u64) -> impl Iterator<Item = (u64, u8)> {
    let mut off = 0;
    std::iter::from_fn(move || {
        let left = size - off;
        let s = [8u8, 4, 2, 1].into_iter().find(|&s| u64::from(s) <= left)?;
        let c = (off, s);
        off += u64::from(s);
        Some(c)
    })
}

/// The condition after `cmp a, b` (both extended by the predicate's signedness) under which the
/// predicate holds.
fn cond_of(p: Pred) -> Cond {
    match p {
        Pred::Eq => Cond::E,
        Pred::Ne => Cond::Ne,
        Pred::Slt => Cond::L,
        Pred::Sle => Cond::Le,
        Pred::Sgt => Cond::G,
        Pred::Sge => Cond::Ge,
        Pred::Ult => Cond::B,
        Pred::Ule => Cond::Be,
        Pred::Ugt => Cond::A,
        Pred::Uge => Cond::Ae,
    }
}

fn is_signed(p: Pred) -> bool {
    matches!(p, Pred::Slt | Pred::Sle | Pred::Sgt | Pred::Sge)
}

fn mask(w: u32) -> u64 {
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
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

/// An integer or byte type's width (64 for a pointer).
fn width_bits(t: Ty) -> u32 {
    match t {
        Ty::Int(w) | Ty::Byte(w) => w,
        _ => 64,
    }
}

/// `x` as a sign-extended 32-bit immediate, if it is one.
fn imm32(x: i64) -> Option<i32> {
    i32::try_from(x).ok()
}

/// The types of a call's arguments: its operands' after the first `skip`.
fn arg_tys(body: &Body, op: OpId, skip: usize) -> Vec<Ty> {
    body.operands(op)[skip..]
        .iter()
        .map(|o| match o.get() {
            OperandKind::Value(v) => body.ty(v),
            OperandKind::Hole(h) => body.hole_ty(h),
        })
        .collect()
}

struct Sel<'a, 'c> {
    cx: &'c ModuleCx<'a>,
    body: &'a Body,
    sp: &'a SpaceCfg,
    /// Each block's instructions and locations, by creation.
    blocks: Vec<Vec<(Inst, Option<Loc>)>>,
    /// Blocks laid out after the others: the exit block and trap blocks.
    cold: Vec<bool>,
    /// The blocks in the order selection first switched to them.
    layout: Vec<u32>,
    placed: Vec<bool>,
    cur: u32,
    /// Whether the current block has ended.
    done: bool,
    /// Each value's virtual register (`NONE` until defined).
    vreg: Vec<u32>,
    nv: u32,
    ctx: Vec<Ctx>,
    sigs: Vec<(Vec<Ty>, Vec<Ty>)>,
    sig_shapes: Vec<CallShape>,
    frame: Frame,
    /// Where the locals start above `rsp`, and how far they reach.
    locals_base: u64,
    locals_end: u64,
    exit: u32,
    /// The register that keeps the results area's address (`rdi` on entry), if any.
    res_ptr: Option<Reg>,
    rets: &'a [Ty],
    loc: Option<Loc>,
}

/// Select one function.
pub fn select_func(cx: &ModuleCx<'_>, index: u32) -> Result<MFunc> {
    let f = &cx.m.funcs[index as usize];
    let body = &f.body;
    let mut s = Sel {
        cx,
        body,
        sp: &cx.m.space,
        blocks: Vec::new(),
        cold: Vec::new(),
        layout: Vec::new(),
        placed: Vec::new(),
        cur: 0,
        done: false,
        vreg: vec![NONE; body.num_values()],
        nv: 0,
        ctx: Vec::new(),
        sigs: Vec::new(),
        sig_shapes: Vec::new(),
        frame: Frame::default(),
        locals_base: 0,
        locals_end: 0,
        exit: 0,
        res_ptr: None,
        rets: &f.rets,
        loc: None,
    };
    s.func().map_err(|e| format!("@{}: {e}", f.name))?;
    // Frame offsets are 32-bit displacements: refuse a frame they can't reach, rather than
    // truncate its size.
    if s.locals_end + u64::from(s.frame.outgoing) > FRAME_LIMIT {
        return Err(format!(
            "@{}: the frame needs {} bytes of locals, more than the x86-64 backend's limit of \
             {FRAME_LIMIT}",
            f.name, s.locals_end
        ));
    }
    Ok(s.finish(index))
}

impl Sel<'_, '_> {
    // Building blocks of code

    fn new_block(&mut self, cold: bool) -> u32 {
        self.blocks.push(Vec::new());
        self.cold.push(cold);
        self.placed.push(false);
        (self.blocks.len() - 1) as u32
    }

    fn switch_to(&mut self, b: u32) {
        self.cur = b;
        self.done = false;
        if !self.placed[b as usize] {
            self.placed[b as usize] = true;
            self.layout.push(b);
        }
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
        Reg::V(self.nv - 1)
    }

    fn val(&mut self, v: ValueId) -> Reg {
        if self.vreg[v.index()] == NONE {
            self.nv += 1;
            self.vreg[v.index()] = self.nv - 1;
        }
        Reg::V(self.vreg[v.index()])
    }

    fn ty_of_operand(&self, op: OpId, i: usize) -> Ty {
        match self.body.operands(op)[i].get() {
            OperandKind::Value(v) => self.body.ty(v),
            OperandKind::Hole(h) => self.body.hole_ty(h),
        }
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

    fn result(&mut self, op: OpId, i: usize) -> Reg {
        let v = self.body.results(op).nth(i).unwrap();
        self.val(v)
    }

    /// The width of an op's `i`th operand.
    fn width_of(&self, op: OpId, i: usize) -> u32 {
        width_bits(self.ty_of_operand(op, i))
    }

    fn mov(&mut self, d: Reg, s: Reg) {
        if d != s {
            self.emit(Inst::Mov { d, s });
        }
    }

    /// A fresh register holding `s`.
    fn copy_of(&mut self, s: Reg) -> Reg {
        let t = self.fresh();
        self.mov(t, s);
        t
    }

    fn konst(&mut self, x: u64) -> Reg {
        let t = self.fresh();
        self.emit(Inst::MovImm { d: t, imm: x });
        t
    }

    fn alu(&mut self, op: AluOp, d: Reg, s: Reg) {
        self.emit(Inst::Alu { op, d, s });
    }

    /// `a op b` in a fresh register.
    fn alu_new(&mut self, op: AluOp, a: Reg, b: Reg) -> Reg {
        let t = self.copy_of(a);
        self.alu(op, t, b);
        t
    }

    fn shift_imm(&mut self, op: ShiftOp, d: Reg, amount: u32) {
        self.emit(Inst::ShiftImm {
            op,
            d,
            amount: amount as u8,
        });
    }

    /// `r`'s low `w` bits zero-extended to 64.
    fn zx(&mut self, r: Reg, w: u32) -> Reg {
        if w >= 64 {
            return r;
        }
        let t = self.fresh();
        match w {
            8 | 16 | 32 => self.emit(Inst::Ext {
                signed: false,
                from: w as u8,
                d: t,
                s: r,
            }),
            _ if w < 32 => {
                self.mov(t, r);
                self.emit(Inst::AluImm {
                    op: AluOp::And,
                    d: t,
                    imm: mask(w) as i32,
                });
            }
            _ => {
                self.mov(t, r);
                self.shift_imm(ShiftOp::Shl, t, 64 - w);
                self.shift_imm(ShiftOp::Shr, t, 64 - w);
            }
        }
        t
    }

    /// `r`'s low `w` bits sign-extended to 64.
    fn sx(&mut self, r: Reg, w: u32) -> Reg {
        if w >= 64 {
            return r;
        }
        let t = self.fresh();
        match w {
            8 | 16 | 32 => self.emit(Inst::Ext {
                signed: true,
                from: w as u8,
                d: t,
                s: r,
            }),
            _ => {
                self.mov(t, r);
                self.shift_imm(ShiftOp::Shl, t, 64 - w);
                self.shift_imm(ShiftOp::Sar, t, 64 - w);
            }
        }
        t
    }

    /// The flags of `a - k`.
    fn cmp_imm(&mut self, a: Reg, k: i64) {
        match imm32(k) {
            Some(imm) => self.emit(Inst::CmpImm { a, imm }),
            None => {
                let b = self.konst(k as u64);
                self.emit(Inst::Cmp { a, b });
            }
        }
    }

    /// `d = s + k`.
    fn add_imm(&mut self, d: Reg, s: Reg, k: i64) {
        match imm32(k) {
            Some(off) => self.emit(Inst::Lea { d, base: s, off }),
            None => {
                let t = self.konst(k as u64);
                self.mov(d, s);
                self.alu(AluOp::Add, d, t);
            }
        }
    }

    fn setcc(&mut self, d: Reg, c: Cond) {
        self.emit(Inst::Setcc { c, d });
    }

    /// Branch on bit 0 of `c` (an `i1`).
    fn branch_bit(&mut self, c: Reg, t: u32, f: u32) {
        self.emit(Inst::TestImm { a: c, imm: 1 });
        self.emit(Inst::Jcc { c: Cond::Ne, t, f });
    }

    /// A trap block for the current op, with its location.
    fn trap_block(&mut self, r: TrapReason) -> u32 {
        let b = self.new_block(true);
        self.blocks[b as usize].push((Inst::Trap(r), self.loc));
        b
    }

    /// Trap with reason `r` if condition `c` holds (after the flags are set).
    fn trap_if(&mut self, c: Cond, r: TrapReason) {
        let t = self.trap_block(r);
        let cont = self.new_block(false);
        self.emit(Inst::Jcc { c, t, f: cont });
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
            let tmps: Vec<Reg> = srcs.iter().map(|&s| self.copy_of(s)).collect();
            for (&d, &t) in dsts.iter().zip(&tmps) {
                self.mov(d, t);
            }
        } else {
            for (&d, &s) in dsts.iter().zip(srcs) {
                self.mov(d, s);
            }
        }
    }

    /// `base + off` as a base register and a 32-bit displacement.
    fn addr(&mut self, base: Reg, off: i64) -> (Reg, i32) {
        match imm32(off).filter(|o| o.checked_add(8).is_some()) {
            Some(o) => (base, o),
            None => {
                let t = self.fresh();
                self.add_imm(t, base, off);
                (t, 0)
            }
        }
    }

    /// Load `size` bytes (0 to 8) little-endian into `d`.
    fn load(&mut self, d: Reg, base: Reg, off: i64, size: u64) {
        let (base, off) = self.addr(base, off);
        if size == 0 {
            self.emit(Inst::MovImm { d, imm: 0 });
            return;
        }
        for (o, s) in chunks(size) {
            if o == 0 {
                self.emit(Inst::Load {
                    size: s,
                    d,
                    base,
                    off,
                });
            } else {
                let t = self.fresh();
                self.emit(Inst::Load {
                    size: s,
                    d: t,
                    base,
                    off: off + o as i32,
                });
                self.shift_imm(ShiftOp::Shl, t, 8 * o as u32);
                self.alu(AluOp::Or, d, t);
            }
        }
    }

    /// Store the low `size` bytes (0 to 8) of `v`.
    fn store(&mut self, v: Reg, base: Reg, off: i64, size: u64) {
        let (base, off) = self.addr(base, off);
        for (o, s) in chunks(size) {
            let part = if o == 0 {
                v
            } else {
                let t = self.copy_of(v);
                self.shift_imm(ShiftOp::Shr, t, 8 * o as u32);
                t
            };
            self.emit(Inst::Store {
                size: s,
                s: part,
                base,
                off: off + o as i32,
            });
        }
    }

    /// A frame slot for a local: its offset from `rsp`.
    fn local(&mut self, size: u64, align: u64) -> i64 {
        let off = align_up(u128::from(self.locals_end), align.max(1)) as u64;
        self.locals_end = off + size.max(1);
        self.frame.align = self.frame.align.max(align as u32);
        (self.locals_base + off) as i64
    }

    fn type_size(&self, t: Ty) -> u64 {
        self.body.types().size(self.sp, t) as u64
    }

    // Functions

    fn func(&mut self) -> Result<()> {
        let body = self.body;
        let types = body.types();
        for &t in self.rets {
            check_ty(types, None, t)?;
        }
        // Outgoing arguments and local alignment, known before any local is placed.
        let mut outgoing = 0u64;
        let mut align = 16u64;
        let mut stack = vec![body.entry()];
        while let Some(r) = stack.pop() {
            for op in body.ops(r) {
                let call = match body.kind(op) {
                    OpKind::Call { .. } | OpKind::Invoke { .. } => Some(0),
                    OpKind::CallIndirect(_) | OpKind::InvokeIndirect { .. } => Some(1),
                    OpKind::MemStack { align: a, .. } => {
                        align = align.max(u64::from(a));
                        None
                    }
                    OpKind::MemStackOf { ty, align: a } => {
                        align = align.max(u64::from(a)).max(types.align(self.sp, ty));
                        None
                    }
                    _ => None,
                };
                if let Some(skip) = call {
                    let n = body.operands(op).len() - skip;
                    let sret = in_memory(&body.results(op).map(|v| body.ty(v)).collect::<Vec<_>>());
                    outgoing = outgoing.max(u64::from(arg_locs(n, sret).1));
                }
                stack.extend_from_slice(body.regions(op));
            }
        }
        self.locals_base = align_up(u128::from(outgoing), align) as u64;
        self.frame.outgoing = self.locals_base as u32;
        self.frame.align = 16;
        let entry = self.new_block(false);
        self.exit = self.new_block(true);
        self.switch_to(entry);
        // Parameters, from where the convention puts them: registers first, so nothing reads
        // an argument register after other code.
        let params: Vec<ValueId> = body.params(body.entry()).collect();
        let sret = in_memory(self.rets);
        if sret {
            let r = self.fresh();
            self.mov(r, RDI);
            self.res_ptr = Some(r);
        }
        let (locs, _) = arg_locs(params.len(), sret);
        let mut stacked = Vec::new();
        for (&p, &l) in params.iter().zip(&locs) {
            check_ty(types, None, body.ty(p))?;
            match l {
                ArgLoc::Reg(a) => {
                    let r = self.val(p);
                    self.mov(r, a);
                }
                ArgLoc::Stack(off) => stacked.push((p, off)),
            }
        }
        for (p, off) in stacked {
            let r = self.val(p);
            self.emit(Inst::Load {
                size: 8,
                d: r,
                base: RBP,
                off: 16 + off as i32,
            });
        }
        self.region(body.entry())?;
        // The exit: the emitter's epilogue and `ret`. A function that returns in memory
        // returns the area's address in `rax`, as C does.
        self.switch_to(self.exit);
        self.loc = None;
        if let Some(area) = self.res_ptr {
            self.mov(RAX, area);
        }
        self.emit(Inst::Ret);
        Ok(())
    }

    /// Lay the blocks out and flatten them: in the order selection first filled them (source
    /// order), then the exit block and the trap blocks.
    fn finish(mut self, index: u32) -> MFunc {
        let n = self.blocks.len();
        for b in 0..n {
            // A block that nothing reaches may lack a terminator; it loops on itself.
            if !self.blocks[b]
                .last()
                .is_some_and(|(i, _)| i.is_terminator())
            {
                self.blocks[b].push((Inst::Jmp { t: b as u32 }, None));
            }
        }
        let mut order: Vec<u32> = std::mem::take(&mut self.layout)
            .into_iter()
            .filter(|&b| !self.cold[b as usize])
            .collect();
        let mut placed = vec![false; n];
        for &b in &order {
            placed[b as usize] = true;
        }
        order.extend((0..n as u32).filter(|&b| !placed[b as usize] && !self.cold[b as usize]));
        order.push(self.exit);
        order.extend((0..n as u32).filter(|&b| self.cold[b as usize] && b != self.exit));
        let mut new_index = vec![u32::MAX; n];
        for (i, &b) in order.iter().enumerate() {
            new_index[b as usize] = i as u32;
        }
        let mut out = MFunc {
            index,
            nvregs: self.nv,
            sigs: self.sigs,
            sig_shapes: self.sig_shapes,
            frame: self.frame,
            ..MFunc::default()
        };
        out.frame.locals = align_up(u128::from(self.locals_end), 16) as u32;
        for &b in &order {
            out.blocks.push(out.insts.len() as u32);
            for &(i, loc) in &self.blocks[b as usize] {
                let i = match i {
                    Inst::Jmp { t } => Inst::Jmp {
                        t: new_index[t as usize],
                    },
                    Inst::Jcc { c, t, f } => Inst::Jcc {
                        c,
                        t: new_index[t as usize],
                        f: new_index[f as usize],
                    },
                    i => i,
                };
                out.insts.push(i);
                out.locs.push(loc);
            }
        }
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
                self.emit(Inst::Jmp { t: join });
            }
            Some(Ctx::Blocks { results, exit, .. }) => {
                let (results, exit) = (results.clone(), *exit);
                self.moves(&results, vals);
                self.emit(Inst::Jmp { t: exit });
            }
            _ => self.emit(Inst::Jmp { t: self.cur }),
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
        self.emit(Inst::Jmp { t: b });
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
        if let Support::No(why) = support(kind) {
            return Err(format!("{}{} {why}", at(self.loc), kind.mnemonic()));
        }
        let (wide_results, wide_operands) = low_bits_only(kind);
        for v in body.results(op) {
            let t = body.ty(v);
            if !(wide_results && matches!(t, Ty::Int(_))) {
                check_ty(body.types(), self.loc, t)?;
            }
        }
        for o in body.operands(op) {
            let t = match o.get() {
                OperandKind::Value(v) => body.ty(v),
                OperandKind::Hole(h) => body.hole_ty(h),
            };
            if !(wide_operands && matches!(t, Ty::Int(_))) {
                check_ty(body.types(), self.loc, t)?;
            }
        }
        for &r in body.regions(op) {
            for v in body.params(r) {
                check_ty(body.types(), self.loc, body.ty(v))?;
            }
        }
        match kind {
            OpKind::Const(n) => {
                let bits = int_low_bits(body.int(n));
                let d = self.result(op, 0);
                self.emit(Inst::MovImm { d, imm: bits });
            }
            OpKind::Poison | OpKind::PtrNull => {
                let d = self.result(op, 0);
                self.emit(Inst::MovImm { d, imm: 0 });
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
                self.alias(v, a);
            }
            OpKind::PtrWithAddr => {
                let a = self.operand(op, 1)?;
                let v = body.results(op).next().unwrap();
                self.alias(v, a);
            }
            OpKind::Select => {
                let (c, a, b) = (
                    self.operand(op, 0)?,
                    self.operand(op, 1)?,
                    self.operand(op, 2)?,
                );
                let d = self.result(op, 0);
                let t = self.copy_of(b);
                self.emit(Inst::TestImm { a: c, imm: 1 });
                self.emit(Inst::Cmov {
                    c: Cond::Ne,
                    d: t,
                    s: a,
                });
                self.mov(d, t);
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
                    BitOp::Or => AluOp::Or,
                    BitOp::Xor => AluOp::Xor,
                };
                let t = self.alu_new(o, a, b);
                self.mov(d, t);
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
                self.emit(Inst::Cmp { a, b });
                self.setcc(d, cond_of(p));
            }
            OpKind::PtrCmp(p) => {
                let (a, b) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let d = self.result(op, 0);
                self.emit(Inst::Cmp { a, b });
                self.setcc(d, cond_of(p));
            }
            OpKind::Zext | OpKind::Sext => {
                let w = self.width_of(op, 0);
                let a = self.operand(op, 0)?;
                let d = self.result(op, 0);
                let t = if kind == OpKind::Sext {
                    self.sx(a, w)
                } else {
                    self.zx(a, w)
                };
                self.mov(d, t);
            }
            OpKind::MemStack { size, align } => {
                let off = self.local(size, u64::from(align));
                let d = self.result(op, 0);
                self.add_imm(d, RSP, off);
            }
            OpKind::MemStackOf { ty, align } => {
                let size = self.type_size(ty);
                let a = u64::from(align).max(body.types().align(self.sp, ty));
                let off = self.local(size, a);
                let d = self.result(op, 0);
                self.add_imm(d, RSP, off);
            }
            OpKind::MemAlloc {
                fail,
                family: _,
                align,
            } => {
                let n = self.operand(op, 0)?;
                let d = self.result(op, 0);
                if align > 16 {
                    let a = self.konst(u64::from(align));
                    self.mov(RSI, n);
                    self.mov(RDI, a);
                    self.emit(Inst::CallRt(Runtime::AlignedAlloc));
                } else {
                    self.mov(RDI, n);
                    self.emit(Inst::CallRt(Runtime::Malloc));
                }
                self.mov(d, RAX);
                if fail == AllocFail::Trap {
                    self.emit(Inst::CmpImm { a: d, imm: 0 });
                    self.trap_if(Cond::E, TrapReason::Oom);
                }
            }
            OpKind::MemFree { .. } => {
                let p = self.operand(op, 0)?;
                self.mov(RDI, p);
                self.emit(Inst::CallRt(Runtime::Free));
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
                let t = self.alu_new(AluOp::Add, p, n);
                self.mov(d, t);
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
                let t = self.copy_of(i);
                if stride.is_power_of_two() {
                    self.shift_imm(ShiftOp::Shl, t, stride.trailing_zeros());
                } else {
                    let s = self.konst(stride);
                    self.alu(AluOp::Imul, t, s);
                }
                self.alu(AluOp::Add, t, p);
                self.mov(d, t);
            }
            OpKind::TySize(ty) | OpKind::TyAlign(ty) => {
                let (s, a) = body.types().dims(self.sp, ty);
                let x = if matches!(kind, OpKind::TySize(_)) {
                    s as u64
                } else {
                    a
                };
                let d = self.result(op, 0);
                self.emit(Inst::MovImm { d, imm: x });
            }
            OpKind::TyOffset { ty, index } => {
                let off = body.types().field_offset(self.sp, ty, index).unwrap_or(0) as u64;
                let d = self.result(op, 0);
                self.emit(Inst::MovImm { d, imm: off });
            }
            OpKind::MemGlobal { global } => {
                let g = self.cx.globals[body.str(global)];
                let d = self.result(op, 0);
                self.emit(Inst::LeaGlobal { d, global: g });
            }
            OpKind::FuncAddr { callee } => {
                let func = self.cx.funcs[body.str(callee)];
                let d = self.result(op, 0);
                self.emit(Inst::LeaFunc { d, func });
            }
            OpKind::Call { callee } | OpKind::Invoke { callee, .. } => {
                let func = self.cx.funcs[body.str(callee)];
                let args = self.operands(op)?;
                let ps = arg_tys(body, op, 0);
                let rs: Vec<Ty> = body.results(op).map(|v| body.ty(v)).collect();
                let external = self.cx.is_extern(func);
                if self.cx.variadic(func) {
                    // Through its address, with every argument's type in the call's signature,
                    // and `al` set.
                    let target = self.fresh();
                    self.emit(Inst::LeaFunc { d: target, func });
                    let sig = self.sig(&ps, &rs, true);
                    self.call(op, &args, &ps, &rs, external, true, |s| {
                        s.emit(Inst::CallInd { s: target, sig })
                    })?;
                } else {
                    self.call(op, &args, &ps, &rs, external, false, |s| {
                        s.emit(Inst::Call { func })
                    })?;
                }
                let throws = self.cx.throws.get(func as usize).copied().unwrap_or(false);
                self.after_call(kind, throws);
            }
            OpKind::CallIndirect(sig) | OpKind::InvokeIndirect { sig, .. } => {
                let args = self.operands(op)?;
                let Some(Shape::Func(ps, rs, va)) = body.types().shape_of(sig) else {
                    return Err(format!("{}not a function type", at(self.loc)));
                };
                // A variadic call's signature lists every argument's type.
                let (ps, rs) = if va {
                    (arg_tys(body, op, 1), rs.to_vec())
                } else {
                    (ps.to_vec(), rs.to_vec())
                };
                let sig = self.sig(&ps, &rs, va);
                let target = args[0];
                self.call(op, &args[1..], &ps, &rs, true, va, |s| {
                    s.emit(Inst::CallInd { s: target, sig })
                })?;
                let throws = self.cx.throws.iter().any(|&t| t);
                self.after_call(kind, throws);
            }
            OpKind::Throw => {
                let v = self.operand(op, 0)?;
                self.emit(Inst::ExnSet { s: v });
                self.emit(Inst::Jmp { t: self.exit });
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
                self.emit(Inst::Jmp { t: header });
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
                self.emit(Inst::Jmp { t: labels[0].1 });
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
                self.emit(Inst::Jmp { t: exit });
            }
            OpKind::Continue => {
                let vals = self.operands(op)?;
                let (header, _, params, _) = self.nearest_loop().expect("verified");
                self.moves(&params, &vals);
                self.emit(Inst::Jmp { t: header });
            }
            OpKind::Ret => {
                let vals = self.operands(op)?;
                match self.res_ptr {
                    None => {
                        let dsts = &RET_REGS[..vals.len()];
                        self.moves(dsts, &vals);
                    }
                    Some(area) => {
                        for (i, &v) in vals.iter().enumerate() {
                            self.emit(Inst::Store {
                                size: 8,
                                s: v,
                                base: area,
                                off: 8 * i as i32,
                            });
                        }
                    }
                }
                self.emit(Inst::Jmp { t: self.exit });
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
                let (da, mut rest) = all[1..].split_at(d.nargs as usize);
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
            OpKind::Check(reason) => {
                let c = self.operand(op, 0)?;
                self.emit(Inst::TestImm { a: c, imm: 1 });
                self.trap_if(Cond::E, reason);
            }
            // `support` refuses the rest before this match.
            _ => {
                return Err(format!(
                    "{}internal error: instruction selection claims {} but has no rule for it",
                    at(self.loc),
                    kind.mnemonic()
                ));
            }
        }
        Ok(())
    }

    /// Give value `v` the register `r` (a result that is its operand's bits).
    fn alias(&mut self, v: ValueId, r: Reg) {
        let Reg::V(i) = r else {
            unreachable!("values live in virtual registers")
        };
        self.vreg[v.index()] = i;
    }

    /// The index of an indirect call's signature, with its shape.
    fn sig(&mut self, ps: &[Ty], rs: &[Ty], variadic: bool) -> u32 {
        self.sigs.push((ps.to_vec(), rs.to_vec()));
        self.sig_shapes.push(call_shape(ps, rs, variadic));
        (self.sigs.len() - 1) as u32
    }

    /// A call: arguments where the convention puts them, the call, then the results. A callee
    /// that may be C's (`external`) gets no integer argument narrower than 32 bits: C assumes
    /// its caller extended those by their signedness, which FIR's types don't say.
    #[allow(clippy::too_many_arguments)]
    fn call(
        &mut self,
        op: OpId,
        args: &[Reg],
        ps: &[Ty],
        rets: &[Ty],
        external: bool,
        variadic: bool,
        emit: impl FnOnce(&mut Self),
    ) -> Result<()> {
        if external
            && let Some(t) = ps
                .iter()
                .find(|t| matches!(t, Ty::Int(w) | Ty::Byte(w) if *w < 32))
        {
            return Err(format!(
                "{}an argument of type {t} to a function that may be C's needs its C signedness (C callees on x86-64 expect it extended to 32 bits), which FIR's signatures don't record yet",
                at(self.loc)
            ));
        }
        if variadic && in_memory(rets) {
            return Err(format!(
                "{}a variadic call with more than two results",
                at(self.loc)
            ));
        }
        let sret = in_memory(rets);
        let area = sret.then(|| self.local(8 * rets.len() as u64, 8));
        let (locs, _) = arg_locs(args.len(), sret);
        let (mut dsts, mut srcs) = (Vec::new(), Vec::new());
        for (&a, &l) in args.iter().zip(&locs) {
            match l {
                ArgLoc::Stack(off) => self.emit(Inst::Store {
                    size: 8,
                    s: a,
                    base: RSP,
                    off: off as i32,
                }),
                ArgLoc::Reg(r) => {
                    dsts.push(r);
                    srcs.push(a);
                }
            }
        }
        // The register arguments last, so the argument registers hold them only up to the call.
        for (&d, &s) in dsts.iter().zip(&srcs) {
            self.mov(d, s);
        }
        if let Some(off) = area {
            self.emit(Inst::Lea {
                d: RDI,
                base: RSP,
                off: off as i32,
            });
        }
        if variadic {
            self.emit(Inst::MovImm { d: RAX, imm: 0 });
        }
        emit(self);
        let results: Vec<Reg> = (0..rets.len()).map(|i| self.result(op, i)).collect();
        match area {
            None => {
                for (&d, &r) in results.iter().zip(&RET_REGS) {
                    self.mov(d, r);
                }
            }
            Some(off) => {
                for (i, &d) in results.iter().enumerate() {
                    self.emit(Inst::Load {
                        size: 8,
                        d,
                        base: RSP,
                        off: off as i32 + 8 * i as i32,
                    });
                }
            }
        }
        Ok(())
    }

    /// After a call that may throw: return at once with the exception pending (a plain call),
    /// or take it and jump to the handler (`func.invoke`).
    fn after_call(&mut self, kind: OpKind, throws: bool) {
        if !throws {
            return;
        }
        let cont = self.new_block(false);
        self.emit(Inst::ExnTest);
        match kind {
            OpKind::Invoke { unwind, .. } | OpKind::InvokeIndirect { unwind, .. } => {
                let land = self.new_block(true);
                self.emit(Inst::Jcc {
                    c: Cond::Ne,
                    t: land,
                    f: cont,
                });
                self.switch_to(land);
                let e = self.fresh();
                self.emit(Inst::ExnTake { d: e });
                let label = self.body.str(self.body.succ(unwind).label).to_owned();
                self.jump(&label, &[e]);
            }
            _ => self.emit(Inst::Jcc {
                c: Cond::Ne,
                t: self.exit,
                f: cont,
            }),
        }
        self.switch_to(cont);
    }

    /// Compare `v` (zero-extended) against sorted keys, branching to each case or the default.
    fn switch_tree(&mut self, v: Reg, targets: &[(u64, u32)], dflt: u32) {
        if targets.len() <= 3 {
            for &(k, b) in targets {
                self.cmp_imm(v, k as i64);
                let next = self.new_block(false);
                self.emit(Inst::Jcc {
                    c: Cond::E,
                    t: b,
                    f: next,
                });
                self.switch_to(next);
            }
            self.emit(Inst::Jmp { t: dflt });
            return;
        }
        let mid = targets.len() / 2;
        let (k, b) = targets[mid];
        self.cmp_imm(v, k as i64);
        let ne = self.new_block(false);
        self.emit(Inst::Jcc {
            c: Cond::E,
            t: b,
            f: ne,
        });
        self.switch_to(ne);
        let (lo, hi) = (self.new_block(false), self.new_block(false));
        self.emit(Inst::Jcc {
            c: Cond::B,
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
            let parts: Vec<(u64, u8, Reg)> = chunks(size)
                .map(|(o, sz)| {
                    let t = self.fresh();
                    self.emit(Inst::Load {
                        size: sz,
                        d: t,
                        base: s,
                        off: o as i32,
                    });
                    (o, sz, t)
                })
                .collect();
            for (o, sz, t) in parts {
                self.emit(Inst::Store {
                    size: sz,
                    s: t,
                    base: d,
                    off: o as i32,
                });
            }
            return;
        }
        let n = self.konst(size);
        self.mov(RDI, d);
        self.mov(RSI, s);
        self.mov(RDX, n);
        self.emit(Inst::CallRt(Runtime::Memmove));
    }

    /// `int.add`, `int.sub`, `int.mul` with an overflow modifier.
    fn arith(&mut self, aop: ArithOp, ovf: Ovf, w: u32, d: Reg, a: Reg, b: Reg) {
        let op = match aop {
            ArithOp::Add => AluOp::Add,
            ArithOp::Sub => AluOp::Sub,
            ArithOp::Mul => AluOp::Imul,
        };
        match ovf {
            Ovf::Wrap | Ovf::Nsw | Ovf::Nuw | Ovf::NswNuw | Ovf::Ub(_) => {
                let t = self.alu_new(op, a, b);
                self.mov(d, t);
            }
            Ovf::Trap(signed) => {
                let (r, bad) = self.overflow(aop, signed, w, a, b);
                self.emit(Inst::TestImm { a: bad, imm: 1 });
                self.trap_if(Cond::Ne, TrapReason::Overflow);
                self.mov(d, r);
            }
            Ovf::Sat(signed) => {
                let bound = self.sat_bound(aop, signed, w, a, b);
                let (r, bad) = self.overflow(aop, signed, w, a, b);
                let t = self.copy_of(r);
                self.emit(Inst::TestImm { a: bad, imm: 1 });
                self.emit(Inst::Cmov {
                    c: Cond::Ne,
                    d: t,
                    s: bound,
                });
                self.mov(d, t);
            }
        }
    }

    /// The bound a saturating op gives on overflow.
    fn sat_bound(&mut self, aop: ArithOp, signed: bool, w: u32, a: Reg, b: Reg) -> Reg {
        if !signed {
            return match aop {
                ArithOp::Sub => self.konst(0),
                _ => self.konst(mask(w)),
            };
        }
        // MAX if the result should be positive, MIN if negative: sign ^ MAX. Overflowing sums
        // and differences have their first operand's sign, products their operands' signs'
        // exclusive or.
        let sa = self.sx(a, w);
        let sign = match aop {
            ArithOp::Mul => {
                let sb = self.sx(b, w);
                self.alu_new(AluOp::Xor, sa, sb)
            }
            _ => self.copy_of(sa),
        };
        self.shift_imm(ShiftOp::Sar, sign, 63);
        let max = self.konst(mask(w) >> 1);
        self.alu(AluOp::Xor, sign, max);
        sign
    }

    /// The wrapped result of `a op b`, and a register whose bit 0 says whether the op
    /// overflows (signed or unsigned) at width `w`.
    fn overflow(&mut self, aop: ArithOp, signed: bool, w: u32, a: Reg, b: Reg) -> (Reg, Reg) {
        let bad = self.fresh();
        match aop {
            ArithOp::Add | ArithOp::Sub if w == 64 => {
                let op = if aop == ArithOp::Add {
                    AluOp::Add
                } else {
                    AluOp::Sub
                };
                let r = self.alu_new(op, a, b);
                // Signed: OF. Unsigned: the carry out of an add, the borrow of a sub (CF).
                self.setcc(bad, if signed { Cond::O } else { Cond::B });
                (r, bad)
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
                let r = self.alu_new(op, ax, bx);
                let t = if signed { self.sx(r, w) } else { self.zx(r, w) };
                self.emit(Inst::Cmp { a: t, b: r });
                self.setcc(bad, Cond::Ne);
                (r, bad)
            }
            ArithOp::Mul => {
                let r = self.fresh();
                if signed {
                    // OF: the 128-bit product doesn't fit in 64 bits.
                    let (ax, bx) = (self.sx(a, w), self.sx(b, w));
                    self.mov(r, ax);
                    self.alu(AluOp::Imul, r, bx);
                    self.setcc(bad, Cond::O);
                } else {
                    // CF: the high half of the 128-bit product isn't zero.
                    let (ax, bx) = (self.zx(a, w), self.zx(b, w));
                    self.mov(RAX, ax);
                    self.emit(Inst::MulWide { s: bx });
                    self.setcc(bad, Cond::B);
                    self.mov(r, RAX);
                }
                if w < 64 {
                    let t = if signed { self.sx(r, w) } else { self.zx(r, w) };
                    self.emit(Inst::Cmp { a: t, b: r });
                    let f = self.fresh();
                    self.setcc(f, Cond::Ne);
                    self.alu(AluOp::Or, bad, f);
                }
                (r, bad)
            }
        }
    }

    /// Division and remainder with their edge cases.
    #[allow(clippy::too_many_arguments)]
    fn div(&mut self, dop: DivOp, zero: Edge, ovf: Edge, w: u32, d: Reg, a: Reg, b: Reg) {
        let signed = dop.signed();
        let rem = matches!(dop, DivOp::RemS | DivOp::RemU);
        let (ax, bx) = if signed {
            (self.sx(a, w), self.sx(b, w))
        } else {
            (self.zx(a, w), self.zx(b, w))
        };
        let join = self.new_block(false);
        match zero {
            Edge::Trap => {
                self.emit(Inst::CmpImm { a: bx, imm: 0 });
                self.trap_if(Cond::E, TrapReason::Div0);
            }
            // `x / 0 = 0`, `x rem 0 = x`, without dividing.
            Edge::Total | Edge::Wrap => {
                let (zb, cont) = (self.new_block(false), self.new_block(false));
                self.emit(Inst::CmpImm { a: bx, imm: 0 });
                self.emit(Inst::Jcc {
                    c: Cond::E,
                    t: zb,
                    f: cont,
                });
                self.switch_to(zb);
                if rem {
                    self.mov(d, a);
                } else {
                    self.emit(Inst::MovImm { d, imm: 0 });
                }
                self.emit(Inst::Jmp { t: join });
                self.switch_to(cont);
            }
            // The hardware faults, which UB allows.
            Edge::Ub => {}
        }
        if signed {
            match ovf {
                Edge::Trap => {
                    // MIN / -1: b is -1, then a is MIN.
                    let (check, cont) = (self.new_block(false), self.new_block(false));
                    self.emit(Inst::CmpImm { a: bx, imm: -1 });
                    self.emit(Inst::Jcc {
                        c: Cond::E,
                        t: check,
                        f: cont,
                    });
                    self.switch_to(check);
                    self.cmp_imm(ax, -1i64 << (w - 1));
                    let t = self.trap_block(TrapReason::Overflow);
                    self.emit(Inst::Jcc {
                        c: Cond::E,
                        t,
                        f: cont,
                    });
                    self.switch_to(cont);
                }
                // `MIN / -1 = MIN`, `MIN rem -1 = 0`: at 64 bits `idiv` faults, so a divisor of
                // -1 gives `-a` and 0 without dividing (exactly the results for every `a`).
                Edge::Total | Edge::Wrap if w == 64 => {
                    let (nb, cont) = (self.new_block(false), self.new_block(false));
                    self.emit(Inst::CmpImm { a: bx, imm: -1 });
                    self.emit(Inst::Jcc {
                        c: Cond::E,
                        t: nb,
                        f: cont,
                    });
                    self.switch_to(nb);
                    if rem {
                        self.emit(Inst::MovImm { d, imm: 0 });
                    } else {
                        let t = self.copy_of(ax);
                        self.emit(Inst::Neg { d: t });
                        self.mov(d, t);
                    }
                    self.emit(Inst::Jmp { t: join });
                    self.switch_to(cont);
                }
                // Below 64 bits the extended operands can't overflow; at 64 bits `.ub` lets
                // the hardware fault.
                Edge::Total | Edge::Wrap | Edge::Ub => {}
            }
        }
        self.mov(RAX, ax);
        if signed {
            self.emit(Inst::Cqo);
        } else {
            self.emit(Inst::MovImm { d: RDX, imm: 0 });
        }
        self.emit(Inst::Div { signed, s: bx });
        self.mov(d, if rem { RDX } else { RAX });
        self.emit(Inst::Jmp { t: join });
        self.switch_to(join);
    }

    /// Shifts with their edge case for amounts of at least the width.
    fn shift(&mut self, sop: ShiftOp2, edge: ShiftEdge, w: u32, d: Reg, a: Reg, b: Reg) {
        let amt = self.zx(b, w);
        let amt = match edge {
            ShiftEdge::Trap => {
                self.emit(Inst::CmpImm {
                    a: amt,
                    imm: w as i32,
                });
                self.trap_if(Cond::Ae, TrapReason::Shift);
                amt
            }
            // An `i1` shifts by 0, the amount modulo 1.
            ShiftEdge::Mask if w == 1 => self.konst(0),
            ShiftEdge::Mask if w.is_power_of_two() => {
                let t = self.copy_of(amt);
                self.emit(Inst::AluImm {
                    op: AluOp::And,
                    d: t,
                    imm: (w - 1) as i32,
                });
                t
            }
            ShiftEdge::Mask => {
                let n = self.konst(u64::from(w));
                self.mov(RAX, amt);
                self.emit(Inst::MovImm { d: RDX, imm: 0 });
                self.emit(Inst::Div {
                    signed: false,
                    s: n,
                });
                self.copy_of(RDX)
            }
            ShiftEdge::Total if sop == ShiftOp2::ShrS => {
                // Shifting by w - 1 or more leaves only the sign.
                let top = self.konst(u64::from(w - 1));
                let t = self.copy_of(amt);
                self.emit(Inst::CmpImm {
                    a: amt,
                    imm: (w - 1) as i32,
                });
                self.emit(Inst::Cmov {
                    c: Cond::A,
                    d: t,
                    s: top,
                });
                t
            }
            ShiftEdge::Ub | ShiftEdge::Total => amt,
        };
        let (x, op) = match sop {
            ShiftOp2::Shl => (a, ShiftOp::Shl),
            ShiftOp2::ShrU => (self.zx(a, w), ShiftOp::Shr),
            ShiftOp2::ShrS => (self.sx(a, w), ShiftOp::Sar),
        };
        let r = self.copy_of(x);
        self.mov(RCX, amt);
        self.emit(Inst::ShiftCl { op, d: r });
        if edge == ShiftEdge::Total && sop != ShiftOp2::ShrS {
            // Shifting by w or more shifts everything out.
            let z = self.konst(0);
            self.emit(Inst::CmpImm {
                a: amt,
                imm: w as i32,
            });
            self.emit(Inst::Cmov {
                c: Cond::Ae,
                d: r,
                s: z,
            });
        }
        self.mov(d, r);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn chunks_cover_sizes() {
        for size in 0..20 {
            let cs: Vec<_> = chunks(size).collect();
            assert_eq!(cs.iter().map(|c| u64::from(c.1)).sum::<u64>(), size);
        }
    }

    #[test]
    fn arguments_go_to_registers_then_the_stack() {
        let (locs, stack) = arg_locs(8, false);
        assert_eq!(locs[0], ArgLoc::Reg(RDI));
        assert_eq!(locs[5], ArgLoc::Reg(R9));
        assert_eq!(locs[6], ArgLoc::Stack(0));
        assert_eq!(locs[7], ArgLoc::Stack(8));
        assert_eq!(stack, 16);
        // A results area's address takes `rdi`.
        let (locs, stack) = arg_locs(6, true);
        assert_eq!(locs[0], ArgLoc::Reg(RSI));
        assert_eq!(locs[5], ArgLoc::Stack(0));
        assert_eq!(stack, 8);
    }
}
