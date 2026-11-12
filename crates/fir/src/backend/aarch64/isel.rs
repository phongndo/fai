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
//! checks) sign- or zero-extend their operands first. Wider integers are held as their low 64 bits
//! where only those bits matter (`low_bits_only`), and rejected elsewhere.
//!
//! **Edge cases** follow the op's modifiers: `.wrap`, `.nsw`, `.nuw`, and `.ub` compute the
//! wrapped result (poison and UB allow any value); `.trap` branches to a trap block on overflow;
//! `.sat` selects the bound. Division by zero traps when asked to and otherwise relies on
//! `sdiv`/`udiv` giving 0 (and `msub` giving `x rem 0 = x`), which is what `.total` means; signed
//! `MIN / -1` wraps in hardware. Shifts by at least the width trap, mask the amount, or select
//! the all-shifted-out value. `poison` of any scalar type (`iN`, `ptr`, `bN`) is 0, one of the
//! values it allows. `cf.check.R %ok` tests bit 0 of `%ok` and branches to a trap block with
//! reason `R` (`bounds`, `tag`, …) when it is clear.
//!
//! **Floats** live in FP registers (`fvN`), an `f32` in the low 32 bits. Each float op is one
//! instruction or a few (decision: Instruction selection): `fadd`…`fdiv`, `fneg`, `fabs`,
//! `fsqrt`; `fmadd` for `float.fma` (its addend copied to the destination first); `copysign`
//! through general-purpose registers; `fcmp` and `cset` (two instructions for `ueq` and `one`);
//! `fcvt`; `scvtf`/`ucvtf` after extending the integer; `fcvtzs`/`fcvtzu` at 64 bits, then
//! clamped for `.sat` below 64 bits, with NaN and range checks before them for `.trap`; `fmov`
//! for `from_bits`, `to_bits`, `poison` (from `xzr`), and constants (an 8-bit immediate when one
//! encodes the value, else through a general-purpose register); `fcsel` for `select`. The
//! instructions' NaN results are Arm's, which the source allows (`Fir.AArch64Proofs`).
//!
//! **Composites** (decision: C ABI for aggregates): a struct or array value, which MFIR has only
//! to pass whole across calls, is its leaves' registers, one per scalar (`agg.make`,
//! `agg.extract`, `agg.insert`, and `copy` only regroup them). Where it travels as AAPCS64 says
//! (`super::abi`), its leaves are packed into the `x` registers' words (shifts and `orr`; a
//! pointer that fills a word is moved as it is) or moved to FP registers (an HFA), stored to the
//! stack or to a copy whose address is passed, or stored at `x8` (a large result), and unpacked
//! where it arrives; `va.arg` follows AAPCS64's algorithm for its class. Anything else that takes
//! or gives a composite is rejected.
//!
//! **HFIR.** The building blocks (union and slice values, aggregates beyond what calls pass,
//! `int.*.overflow.*`) are rejected with a message to lower first: drivers compile HFIR through `fir::backend::prepare`,
//! which lowers it to MFIR (`fir lower`). The lowering checks overflow at one more bit (twice
//! the bits for `mul`), so overflow ops on integers wider than 63 bits (32 for `mul`) need the
//! integers above 64 bits that the backend doesn't support yet.
//!
//! **Memory**: `mem.stack` slots are fixed frame slots (a loop iteration's slot is the previous
//! iteration's, which is dead by then); heap allocation calls the family's allocator; loads and
//! stores of odd sizes split into 4-, 2-, and 1-byte accesses; `mem.copy` copies up to 64 bytes
//! through registers and larger sizes in a loop whose direction depends on the addresses, so
//! overlap is fine. **Calls** follow AAPCS64 (see `super::abi`): integers and floats in their own
//! registers, then stack slots, composites by their class; results in `d0`/`d1` when all are
//! floats of one format, otherwise in `x0`/`x1` (a float moved there by `fmov`) or memory at
//! `x8`, a composite where it would be passed first or at `x8`.
//!
//! **Exceptions** use an error-return convention (decision: Exceptions at run time):
//! `exn.throw` makes its value the pending exception (`aarch64.exn.set`) and returns through
//! the epilogue; after each call that may throw ([`may_throw`]), `aarch64.b.exn` tests for a
//! pending exception: a plain call then returns at once, leaving it pending for its own caller,
//! and a `func.invoke` takes it (`aarch64.exn.take`) and jumps to its handler block with it.

use rustc_hash::FxHashMap;

use super::abi::{self, ArgLoc};
use super::mir::{Frame, Inst, MFunc};
use crate::body::{Body, OpId, OperandKind, RegionId, ValueId};
use crate::contract::Support;
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
    /// Which of the module's functions may return with an exception pending
    /// ([`may_throw`]); external functions never do.
    pub throws: Vec<bool>,
}

/// Which functions of a module may throw out of themselves: those with an `exn.throw`, a plain
/// call to one that may, or an indirect call when any function may (a `func.invoke` catches
/// what its callee throws). The least fixed point, so code without throws gets no checks.
pub fn may_throw(m: &Module) -> Vec<bool> {
    let names: FxHashMap<&str, usize> = m
        .funcs
        .iter()
        .enumerate()
        .map(|(i, f)| (f.name.as_str(), i))
        .collect();
    // Each function's own throws, direct callees (plain calls), and whether it calls indirectly.
    let mut own = vec![false; m.funcs.len()];
    let mut callees: Vec<Vec<usize>> = vec![Vec::new(); m.funcs.len()];
    let mut indirect = vec![false; m.funcs.len()];
    for (i, f) in m.funcs.iter().enumerate() {
        let b = &f.body;
        let mut stack = vec![b.entry()];
        while let Some(r) = stack.pop() {
            for op in b.ops(r) {
                match b.kind(op) {
                    OpKind::Throw => own[i] = true,
                    OpKind::Call { callee } => {
                        if let Some(&g) = names.get(b.str(callee)) {
                            callees[i].push(g);
                        }
                    }
                    OpKind::CallIndirect(_) => indirect[i] = true,
                    _ => {}
                }
                stack.extend_from_slice(b.regions(op));
            }
        }
    }
    let mut throws = own;
    loop {
        let any = throws.iter().any(|&t| t);
        let mut changed = false;
        for i in 0..throws.len() {
            if !throws[i] && ((indirect[i] && any) || callees[i].iter().any(|&g| throws[g])) {
                throws[i] = true;
                changed = true;
            }
        }
        if !changed {
            return throws;
        }
    }
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
            throws: may_throw(m),
        }
    }

    /// Whether callee `f` takes variadic arguments.
    pub fn variadic(&self, f: u32) -> bool {
        let m = self.m;
        match m.funcs.get(f as usize) {
            Some(func) => func.variadic,
            None => m.externs[f as usize - m.funcs.len()].variadic,
        }
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
            check_ty(&m.globals.types, None, t).map_err(|e| format!("extern @{}: {e}", x.name))?;
        }
    }
    Ok(())
}

/// What instruction selection does with ops of a kind ([`crate::contract`]): every MFIR op is
/// selected, `agg.make`, `agg.extract`, and `agg.insert` included (they regroup the leaves of a
/// struct or array calls pass whole), and so are `ptr.field` and `ptr.index` (HFIR ops over
/// scalars, so that core-op HFIR compiles without lowering); the other HFIR building blocks need
/// lowering first, and LFIR is already selected. Integers wider than 64 bits are a separate, per-type limit
/// ([`check_module`], `check_ty`).
#[deny(clippy::wildcard_enum_match_arm)]
pub fn support(k: OpKind) -> Support {
    const HFIR: Support = Support::No(
        "is HFIR only: lower the module to MFIR first (`fir::lower_checked`, or `fir::backend::prepare`)",
    );
    const LFIR: Support = Support::No("is an LFIR op: the module is already selected");
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
        | OpKind::FloatConst { .. }
        | OpKind::FloatBin(_)
        | OpKind::FloatUn(_)
        | OpKind::FloatFma
        | OpKind::FloatCmp(_)
        | OpKind::FloatExt
        | OpKind::FloatTrunc
        | OpKind::FloatToInt { .. }
        | OpKind::IntToFloat { .. }
        | OpKind::FloatFromBits
        | OpKind::FloatToBits
        | OpKind::VaStart
        | OpKind::VaArg
        | OpKind::VaEnd
        | OpKind::InvokeIndirect { .. } => Support::Yes,
        // Structs and arrays that calls pass whole (decision: C ABI for aggregates); `Sel::op`
        // refuses composites in any other op.
        OpKind::AggMake | OpKind::AggExtract { .. } | OpKind::AggInsert { .. } => Support::Yes,
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

/// Whether an op's results, and its operands, may be integers wider than 64 bits. Such an
/// integer is held as its low 64 bits (the bits above are unspecified, as for narrower ones), so
/// only ops whose results' low 64 bits depend on nothing but their operands' low 64 bits may
/// touch it: constants, `copy`, `freeze`, `select`, bitwise ops, `int.add`/`sub`/`mul` that
/// don't trap or saturate, extensions *to* a wide type (their operands are narrow), and
/// truncations *from* one (`.nsw`/`.nuw` give `poison` where the value doesn't fit, so the low
/// bits will do). That is what HFIR's lowering emits for `ptr.index.inbounds`: the exact product
/// at twice the address size, truncated with `.nsw`. Anything else (comparisons, division,
/// shifts, memory, calls, parameters and results, region arguments) is rejected.
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
            "{}{t} is wider than 64 bits, which the AArch64 backend doesn't support yet",
            at(loc)
        )),
        // Union and slice values are HFIR's, and so are aggregates other than the composites
        // calls pass whole (decision: C ABI for aggregates; `Sel::op` refuses composites in any
        // other op): core ops over them (a `mem.load` of a struct) select only after the
        // lowering has scalarized them.
        _ if !t.is_value() && !types.is_composite(t) => Err(format!(
            "{}a value of an aggregate, union, or slice type is HFIR only: lower the module to MFIR first",
            at(loc)
        )),
        _ => Ok(()),
    }
}

/// Check a type a call passes whole (a parameter, argument, result, or `va.arg` result): as
/// [`check_ty`], and a composite the convention passes as `x` register words may not have a
/// pointer that doesn't fill one (`abi::splits_ptr`; decision: C ABI for aggregates), since
/// registers could carry it only as address bits, dropping its provenance.
fn check_pass(types: &Types, sp: &SpaceCfg, loc: Option<Loc>, t: Ty) -> Result<()> {
    check_ty(types, loc, t)?;
    if abi::splits_ptr(types, sp, t) {
        return Err(format!(
            "{}{} has a pointer at an offset that isn't a multiple of 8, which can't be passed by value in registers on AArch64",
            at(loc),
            types.show(t)
        ));
    }
    Ok(())
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

/// The size of a value's 8-byte stack slot access (an argument or a result in memory): 4 bytes
/// for an `f32`, 8 for the rest.
fn slot_size(t: Ty) -> MemSize {
    if t == Ty::Float(FloatTy::F32) {
        MemSize::W
    } else {
        MemSize::X
    }
}

/// The format of a float type (`d` for anything else).
fn fsize(t: Ty) -> FSize {
    match t {
        Ty::Float(f) => FSize::of(f),
        _ => FSize::D,
    }
}

/// The 8-bit `fmov` immediate that encodes these bits, if one does.
fn fmov_imm8(fs: FSize, bits: u64) -> Option<u8> {
    (0..=255u8).find(|&i| super::machine_imm(fs, i) == bits)
}

/// The bits of the float of format `fs` nearest to `v` (exact for the bounds used here).
fn float_bits(fs: FSize, v: i128) -> u64 {
    crate::float::from_int(fs.fty(), true, 128, &crate::sem::Bits::of_i128(128, v))
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
    /// The blocks in the order selection first switched to them, and which those are.
    layout: Vec<u32>,
    placed: Vec<bool>,
    cur: u32,
    /// Whether the current block has ended.
    done: bool,
    /// Each value's virtual register (`NONE` until defined).
    vreg: Vec<u32>,
    /// Each composite value's leaves' registers (decision: C ABI for aggregates), by value.
    agg: FxHashMap<u32, Vec<Reg>>,
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
    /// A variadic function's register save areas, for `va.start` (none if it has none).
    va: Option<VaFrame>,
    /// Whether the function is variadic.
    variadic: bool,
    rets: &'a [Ty],
    loc: Option<Loc>,
}

/// Where a variadic function keeps what `va.start` needs (AAPCS64's `va_list`, decision:
/// Varargs): the general-purpose and FP register save areas, as frame slots above `sp` with
/// their sizes, and where the stacked variadic arguments start above `x29`.
#[derive(Clone, Copy, Debug)]
struct VaFrame {
    gr_off: i64,
    gr_size: i64,
    vr_off: i64,
    vr_size: i64,
    stack: i64,
}

/// The types of a call's arguments: its operands' after the first `skip` (the pointer of an
/// indirect call).
fn arg_tys(body: &Body, op: OpId, skip: usize) -> Vec<Ty> {
    body.operands(op)[skip..]
        .iter()
        .map(|o| match o.get() {
            OperandKind::Value(v) => body.ty(v),
            OperandKind::Hole(h) => body.hole_ty(h),
        })
        .collect()
}

/// Whether a function body has a `va.start`.
fn uses_va_start(body: &Body) -> bool {
    let mut stack = vec![body.entry()];
    while let Some(r) = stack.pop() {
        for op in body.ops(r) {
            if body.kind(op) == OpKind::VaStart {
                return true;
            }
            stack.extend_from_slice(body.regions(op));
        }
    }
    false
}

/// Select one function.
pub fn select_func(cx: &ModuleCx<'_>, index: u32, families: &mut Vec<String>) -> Result<MFunc> {
    let f = &cx.m.funcs[index as usize];
    let body = &f.body;
    for &t in &f.rets {
        check_ty(body.types(), None, t).map_err(|e| format!("@{}: {e}", f.name))?;
    }
    if f.rets.len() > 1 && f.rets.iter().any(|&t| body.types().is_composite(t)) {
        return Err(format!(
            "@{}: a struct or array among several results is HFIR only: lower the module to MFIR first",
            f.name
        ));
    }
    let mut s = Sel {
        cx,
        body,
        sp: &cx.m.space,
        families,
        blocks: Vec::new(),
        cold: Vec::new(),
        layout: Vec::new(),
        placed: Vec::new(),
        cur: 0,
        done: false,
        vreg: vec![NONE; body.num_values()],
        agg: FxHashMap::default(),
        nv: 0,
        ctx: Vec::new(),
        sigs: Vec::new(),
        frame: Frame::default(),
        locals_base: 0,
        locals_end: 0,
        exit: 0,
        res_ptr: None,
        va: None,
        variadic: f.variadic,
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
        Reg::virt(self.nv - 1)
    }

    fn fresh_fp(&mut self) -> Reg {
        self.nv += 1;
        Reg::fvirt(self.nv - 1)
    }

    /// A fresh register of `r`'s class.
    fn fresh_like(&mut self, r: Reg) -> Reg {
        if r.is_fp() {
            self.fresh_fp()
        } else {
            self.fresh()
        }
    }

    /// A value's register: an FP one for a float.
    fn val(&mut self, v: ValueId) -> Reg {
        if self.vreg[v.index()] == NONE {
            self.nv += 1;
            self.vreg[v.index()] = self.nv - 1;
        }
        let i = self.vreg[v.index()];
        if self.body.ty(v).is_float() {
            Reg::fvirt(i)
        } else {
            Reg::virt(i)
        }
    }

    /// The type of an op's `i`th operand.
    fn ty_of_operand(&self, op: OpId, i: usize) -> Ty {
        match self.body.operands(op)[i].get() {
            OperandKind::Value(v) => self.body.ty(v),
            OperandKind::Hole(h) => self.body.hole_ty(h),
        }
    }

    /// The format of an op's `i`th operand.
    fn fs_of(&self, op: OpId, i: usize) -> FSize {
        match self.body.operands(op)[i].get() {
            OperandKind::Value(v) => fsize(self.body.ty(v)),
            OperandKind::Hole(h) => fsize(self.body.hole_ty(h)),
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

    /// Copy a register of either class (all 64 bits).
    fn mov(&mut self, d: Reg, n: Reg) {
        if d == n {
        } else if d.is_fp() || n.is_fp() {
            self.fmov(FSize::D, d, n);
        } else {
            self.emit(Inst::Mov { sf: Sf::X, d, n });
        }
    }

    fn fmov(&mut self, fs: FSize, d: Reg, n: Reg) {
        self.emit(Inst::Funary {
            op: FUnaryOp::Fmov,
            fs,
            d,
            n,
        });
    }

    /// `n` in a register of the class `fp` says, moved by `fmov` if it isn't (a float of
    /// format `fs`).
    fn in_class(&mut self, n: Reg, fp: bool, fs: FSize) -> Reg {
        if n.is_fp() == fp {
            return n;
        }
        let t = if fp { self.fresh_fp() } else { self.fresh() };
        self.fmov(fs, t, n);
        t
    }

    /// Put the float of format `fs` with these bits in `d`.
    fn fconst(&mut self, d: Reg, fs: FSize, bits: u64) {
        if bits == 0 {
            self.fmov(FSize::D, d, Reg::XZR);
        } else if let Some(imm) = fmov_imm8(fs, bits) {
            self.emit(Inst::FmovImm { fs, d, imm });
        } else {
            let t = self.konst(bits);
            self.fmov(fs, d, t);
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
                    let t = self.fresh_like(s);
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

    // Composites (decision: C ABI for aggregates)

    /// The leaves of a type of the function's table, with their offsets.
    fn leaves_of(&self, t: Ty) -> Vec<(u64, Ty)> {
        let mut out = Vec::new();
        self.body.types().leaves(self.sp, t, 0, &mut out);
        out.into_iter().map(|(o, t)| (o as u64, t)).collect()
    }

    /// Whether a type is a composite, which calls pass whole.
    fn is_composite(&self, t: Ty) -> bool {
        self.body.types().is_composite(t)
    }

    /// Fresh registers for a composite's leaves, checked to fit registers.
    fn fresh_leaves(&mut self, t: Ty) -> Result<Vec<Reg>> {
        let mut out = Vec::new();
        for (_, l) in self.leaves_of(t) {
            check_ty(self.body.types(), self.loc, l)?;
            out.push(if l.is_float() {
                self.fresh_fp()
            } else {
                self.fresh()
            });
        }
        Ok(out)
    }

    /// A value's registers: a scalar's one, or a composite's leaves'.
    fn regs_of(&mut self, v: ValueId) -> Result<Vec<Reg>> {
        let t = self.body.ty(v);
        if !self.is_composite(t) {
            return Ok(vec![self.val(v)]);
        }
        if let Some(rs) = self.agg.get(&(v.index() as u32)) {
            return Ok(rs.clone());
        }
        let rs = self.fresh_leaves(t)?;
        self.agg.insert(v.index() as u32, rs.clone());
        Ok(rs)
    }

    /// An operand's registers.
    fn operand_regs(&mut self, op: OpId, i: usize) -> Result<Vec<Reg>> {
        match self.body.operands(op)[i].get() {
            OperandKind::Value(v) => self.regs_of(v),
            OperandKind::Hole(h) => Err(format!(
                "{}the hole ?{} can't be compiled",
                at(self.loc),
                self.body.hole_name(h)
            )),
        }
    }

    /// Give a value these registers: a composite its leaves', a scalar the one's.
    fn set_regs(&mut self, v: ValueId, rs: Vec<Reg>) {
        if self.is_composite(self.body.ty(v)) {
            self.agg.insert(v.index() as u32, rs);
        } else if let Some(&r) = rs.first() {
            self.vreg[v.index()] = r.virt_index();
        }
    }

    /// How many leaves each part of a composite has.
    fn part_counts(&self, t: Ty) -> Vec<usize> {
        let parts: Vec<Ty> = match self.body.types().shape_of(t) {
            Some(Shape::Struct(_, fs)) => fs.to_vec(),
            Some(Shape::Array(n, e)) => vec![e; n as usize],
            _ => Vec::new(),
        };
        parts
            .into_iter()
            .map(|p| {
                if p.is_value() {
                    1
                } else {
                    self.leaves_of(p).len()
                }
            })
            .collect()
    }

    /// The bits of a leaf in a general-purpose register, zero-extended from its size.
    fn leaf_bits(&mut self, r: Reg, t: Ty, size: u64) -> Reg {
        let g = if r.is_fp() {
            let g = self.fresh();
            self.fmov(fsize(t), g, r);
            g
        } else {
            r
        };
        self.zx(g, (8 * size) as u32)
    }

    /// The registers a composite passed in registers travels in: an HFA's members in memory
    /// order, or else its words (`pack`).
    fn pieces(&mut self, t: Ty, leaves: &[Reg]) -> Vec<Reg> {
        match abi::pass_kind(self.body.types(), self.sp, t) {
            abi::PassKind::Hfa(..) => abi::hfa_order(self.body.types(), self.sp, t)
                .into_iter()
                .map(|j| leaves[j])
                .collect(),
            _ => self.pack(t, leaves),
        }
    }

    /// The `x` registers a composite of up to 16 bytes travels in: its leaves' bytes, 8 per
    /// register, as `ldr` would load them (padding as zeros). A pointer that fills a word is
    /// that word, so it keeps its provenance.
    fn pack(&mut self, t: Ty, leaves: &[Reg]) -> Vec<Reg> {
        let size = self.type_size(t);
        let ls = self.leaves_of(t);
        let n = size.div_ceil(8);
        let mut out = Vec::new();
        for k in 0..n {
            let (lo, hi) = (8 * k, 8 * k + 8);
            let inside: Vec<(u64, Ty, Reg)> = ls
                .iter()
                .zip(leaves)
                .filter(|&(&(o, l), _)| o < hi && o + self.type_size(l) > lo)
                .map(|(&(o, l), &r)| (o, l, r))
                .collect();
            if let [(o, l, r)] = inside[..]
                && o == lo
                && self.type_size(l) == 8
            {
                out.push(self.in_class(r, false, fsize(l)));
                continue;
            }
            let mut acc: Option<Reg> = None;
            for (o, l, r) in inside {
                let size = self.type_size(l);
                let g = self.leaf_bits(r, l, size);
                let part = if o >= lo {
                    if o == lo {
                        g
                    } else {
                        let d = self.fresh();
                        self.emit(Inst::ShiftImm {
                            op: ShiftImmOp::Lsl,
                            sf: Sf::X,
                            d,
                            n: g,
                            amount: (8 * (o - lo)) as u8,
                        });
                        d
                    }
                } else {
                    let d = self.fresh();
                    self.emit(Inst::ShiftImm {
                        op: ShiftImmOp::Lsr,
                        sf: Sf::X,
                        d,
                        n: g,
                        amount: (8 * (lo - o)) as u8,
                    });
                    d
                };
                acc = Some(match acc {
                    None => part,
                    Some(a) => self.alu_new(AluOp::Orr, a, part),
                });
            }
            out.push(match acc {
                Some(a) => a,
                None => self.konst(0),
            });
        }
        out
    }

    /// A composite's leaves from the registers it travels in (`pack`'s inverse): an HFA's
    /// members as they are, or each leaf's bytes taken out of its words.
    fn unpack(&mut self, t: Ty, regs: &[Reg]) -> Result<Vec<Reg>> {
        if let abi::PassKind::Hfa(..) = abi::pass_kind(self.body.types(), self.sp, t) {
            // Member `i` is the leaf at the `i`th offset, not the `i`th declared.
            let order = abi::hfa_order(self.body.types(), self.sp, t);
            let mut out = regs.to_vec();
            for (i, &j) in order.iter().enumerate() {
                out[j] = regs[i];
            }
            return Ok(out);
        }
        let mut out = Vec::new();
        for (o, l) in self.leaves_of(t) {
            check_ty(self.body.types(), self.loc, l)?;
            let size = self.type_size(l);
            let (k, b) = ((o / 8) as usize, o % 8);
            let g = if b == 0 && size == 8 {
                regs[k]
            } else {
                let lo = if b == 0 {
                    regs[k]
                } else {
                    let d = self.fresh();
                    self.emit(Inst::ShiftImm {
                        op: ShiftImmOp::Lsr,
                        sf: Sf::X,
                        d,
                        n: regs[k],
                        amount: (8 * b) as u8,
                    });
                    d
                };
                if b + size > 8 {
                    let h = self.fresh();
                    self.emit(Inst::ShiftImm {
                        op: ShiftImmOp::Lsl,
                        sf: Sf::X,
                        d: h,
                        n: regs[k + 1],
                        amount: (8 * (8 - b)) as u8,
                    });
                    self.alu_new(AluOp::Orr, lo, h)
                } else {
                    lo
                }
            };
            let r = if l.is_float() {
                let f = self.fresh_fp();
                self.fmov(fsize(l), f, g);
                f
            } else {
                let r = self.fresh();
                self.mov(r, g);
                r
            };
            out.push(r);
        }
        Ok(out)
    }

    /// Store a composite's leaves at `base + off`, each as a store of its type (padding is
    /// left alone).
    fn store_leaves(&mut self, t: Ty, leaves: &[Reg], base: Reg, off: i64) {
        for (&(o, l), &r) in self.leaves_of(t).iter().zip(leaves) {
            let size = self.type_size(l);
            if r.is_fp() {
                self.str_(MemSize::of_bytes(size).unwrap(), r, base, off + o as i64);
            } else {
                self.store(r, base, off + o as i64, size);
            }
        }
    }

    /// Load a composite's leaves from `base + off`.
    fn load_leaves(&mut self, t: Ty, base: Reg, off: i64) -> Result<Vec<Reg>> {
        let mut out = Vec::new();
        for (o, l) in self.leaves_of(t) {
            check_ty(self.body.types(), self.loc, l)?;
            let size = self.type_size(l);
            let r = if l.is_float() {
                let r = self.fresh_fp();
                self.ldr(MemSize::of_bytes(size).unwrap(), r, base, off + o as i64);
                r
            } else {
                let r = self.fresh();
                self.load(r, base, off + o as i64, size);
                r
            };
            out.push(r);
        }
        Ok(out)
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
                    // A variadic call passes every argument by its type, as fixed ones.
                    OpKind::Call { .. } | OpKind::Invoke { .. } => {
                        let ps = arg_tys(body, op, 0);
                        let n = abi::arg_locs(body.types(), self.sp, &ps).1;
                        outgoing = outgoing.max(u64::from(n));
                    }
                    OpKind::CallIndirect(_) | OpKind::InvokeIndirect { .. } => {
                        let ps = arg_tys(body, op, 1);
                        let n = abi::arg_locs(body.types(), self.sp, &ps).1;
                        outgoing = outgoing.max(u64::from(n));
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
        let ps: Vec<Ty> = params.iter().map(|&p| body.ty(p)).collect();
        let (locs, _) = abi::arg_locs(body.types(), self.sp, &ps);
        // First every register argument into virtual registers, then the composites taken
        // apart, so nothing is read from an argument register after other code.
        let mut later = Vec::new();
        for ((&p, &t), &l) in params.iter().zip(&ps).zip(&locs) {
            check_pass(body.types(), self.sp, None, t)?;
            match l {
                ArgLoc::Reg(a) => {
                    let r = self.val(p);
                    self.mov(r, a);
                }
                ArgLoc::Stack(off) => {
                    let r = self.val(p);
                    self.ldr(slot_size(t), r, Reg::FP, 16 + i64::from(off));
                }
                ArgLoc::Regs(..) | ArgLoc::RefReg(_) => {
                    let regs: Vec<Reg> = l
                        .regs()
                        .map(|a| {
                            let r = self.fresh_like(a);
                            self.mov(r, a);
                            r
                        })
                        .collect();
                    later.push((p, t, l, regs));
                }
                ArgLoc::Mem(_) | ArgLoc::RefStack(_) | ArgLoc::Nothing => {
                    later.push((p, t, l, Vec::new()))
                }
            }
        }
        for (p, t, l, regs) in later {
            let leaves = match l {
                ArgLoc::Regs(..) => self.unpack(t, &regs)?,
                ArgLoc::RefReg(_) => self.load_leaves(t, regs[0], 0)?,
                ArgLoc::RefStack(off) => {
                    let q = self.fresh();
                    self.ldr(MemSize::X, q, Reg::FP, 16 + i64::from(off));
                    self.load_leaves(t, q, 0)?
                }
                ArgLoc::Mem(off) => self.load_leaves(t, Reg::FP, 16 + i64::from(off))?,
                _ => Vec::new(),
            };
            self.agg.insert(p.index() as u32, leaves);
        }
        for &t in self.rets {
            check_pass(body.types(), self.sp, None, t)?;
        }
        if abi::res_regs(body.types(), self.sp, self.rets).is_none() {
            let r = self.fresh();
            self.mov(r, Reg::x(8));
            self.res_ptr = Some(r);
        }
        if self.variadic && uses_va_start(body) {
            self.save_va_regs(&ps);
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
                self.blocks[b].push((Inst::B { t: b as u32 }, None));
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
        let sig_shapes = self
            .sigs
            .iter()
            .map(|(p, r)| abi::CallShape::of(self.body.types(), self.sp, p, r))
            .collect();
        let mut out = MFunc {
            index,
            nvregs: self.nv,
            sigs: self.sigs,
            sig_shapes,
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
                    Inst::BExn { t, f } => Inst::BExn {
                        t: new_index[t as usize],
                        f: new_index[f as usize],
                    },
                    i => i,
                };
                out.insts.push(i);
                out.locs.push(loc);
            }
        }
        // The prologue's `sub sp, sp, N` is its fifth instruction. Before allocation it makes
        // room for the outgoing arguments and the locals, so the code runs as it is; the frame
        // lowering replaces it.
        out.frame.alloc_at = 4;
        out.insts[4] = Inst::AluImm {
            op: AluImmOp::Sub,
            sf: Sf::X,
            d: Reg::SP,
            n: Reg::SP,
            imm: i64::from(out.frame.outgoing + out.frame.locals),
        };
        // A local aligned beyond 16 needs `sp` realigned, before allocation too, so that the
        // code that runs as it is puts such a local where its alignment says (`ptr.addr` shows
        // it). The frame lowering replaces this pair with its own.
        if out.frame.align > 16 {
            let x16 = Reg::x(16);
            let realign = [
                Inst::Mov {
                    sf: Sf::X,
                    d: x16,
                    n: Reg::SP,
                },
                Inst::AluImm {
                    op: AluImmOp::And,
                    sf: Sf::X,
                    d: Reg::SP,
                    n: x16,
                    imm: -i64::from(out.frame.align),
                },
            ];
            out.insts.splice(5..5, realign);
            out.locs.splice(5..5, [None, None]);
            for b in out.blocks.iter_mut().filter(|b| **b > 4) {
                *b += 2;
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
        let (wide_results, wide_operands) = low_bits_only(kind);
        // Wide integers are rejected where their high bits matter.
        for v in body.results(op) {
            if !wide_results {
                check_ty(body.types(), self.loc, body.ty(v))?;
            }
        }
        for o in body.operands(op) {
            if let OperandKind::Value(v) = o.get()
                && !wide_operands
            {
                check_ty(body.types(), self.loc, body.ty(v))?;
            }
        }
        // Composites are made, taken apart, copied, and passed through calls; nothing else
        // takes or gives one.
        let composite_ok = matches!(
            kind,
            OpKind::AggMake
                | OpKind::AggExtract { .. }
                | OpKind::AggInsert { .. }
                | OpKind::Copy
                | OpKind::Call { .. }
                | OpKind::Invoke { .. }
                | OpKind::CallIndirect(_)
                | OpKind::InvokeIndirect { .. }
                | OpKind::Ret
                | OpKind::VaArg
        );
        // A composite among several results is HFIR's (the lowering scalarizes those).
        let several = match kind {
            OpKind::Ret => self.rets.len() > 1 && self.rets.iter().any(|&t| self.is_composite(t)),
            OpKind::Call { .. }
            | OpKind::Invoke { .. }
            | OpKind::CallIndirect(_)
            | OpKind::InvokeIndirect { .. } => {
                body.results(op).len() > 1
                    && body.results(op).any(|v| self.is_composite(body.ty(v)))
            }
            _ => false,
        };
        if several {
            return Err(format!(
                "{}a struct or array among several results is HFIR only: lower the module to MFIR first",
                at(self.loc)
            ));
        }
        if !composite_ok {
            let types = body.types();
            let mut tys: Vec<Ty> = body.results(op).map(|v| body.ty(v)).collect();
            tys.extend(arg_tys(body, op, 0));
            for &r in body.regions(op) {
                tys.extend(body.params(r).map(|v| body.ty(v)));
            }
            if let Some(&t) = tys.iter().find(|&&t| types.is_composite(t)) {
                return Err(format!(
                    "{}{} values are passed through calls, made, and taken apart; in {} they are HFIR only: lower the module to MFIR first",
                    at(self.loc),
                    types.show(t),
                    kind.mnemonic()
                ));
            }
        }
        match kind {
            OpKind::AggMake => {
                let mut leaves = Vec::new();
                for i in 0..body.operands(op).len() {
                    leaves.extend(self.operand_regs(op, i)?);
                }
                let v = body.results(op).next().unwrap();
                self.set_regs(v, leaves);
            }
            OpKind::AggExtract { index } => {
                let a = self.operand_regs(op, 0)?;
                let counts = self.part_counts(self.ty_of_operand(op, 0));
                let start: usize = counts[..index as usize].iter().sum();
                let part = a[start..start + counts[index as usize]].to_vec();
                let v = body.results(op).next().unwrap();
                self.set_regs(v, part);
            }
            OpKind::AggInsert { index } => {
                let a = self.operand_regs(op, 0)?;
                let x = self.operand_regs(op, 1)?;
                let counts = self.part_counts(self.ty_of_operand(op, 0));
                let start: usize = counts[..index as usize].iter().sum();
                let mut leaves = a[..start].to_vec();
                leaves.extend(x);
                leaves.extend_from_slice(&a[start + counts[index as usize]..]);
                let v = body.results(op).next().unwrap();
                self.set_regs(v, leaves);
            }
            OpKind::Copy if self.is_composite(self.ty_of_operand(op, 0)) => {
                let a = self.operand_regs(op, 0)?;
                let v = body.results(op).next().unwrap();
                self.set_regs(v, a);
            }
            OpKind::Const(n) => {
                let w = width_bits(body.ty(body.results(op).next().unwrap()));
                let bits = int_low_bits(body.int(n));
                let d = self.result(op, 0);
                self.mov_int(d, w, bits);
            }
            OpKind::Poison | OpKind::PtrNull => {
                let d = self.result(op, 0);
                if d.is_fp() {
                    self.fmov(FSize::D, d, Reg::XZR);
                } else {
                    self.mov_imm(d, 0);
                }
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
                if d.is_fp() {
                    self.emit(Inst::Fcsel {
                        c: Cond::Ne,
                        fs: FSize::D,
                        d,
                        n: a,
                        m: b,
                    });
                } else {
                    self.emit(Inst::Csel {
                        op: CselOp::Csel,
                        c: Cond::Ne,
                        sf: Sf::X,
                        d,
                        n: a,
                        m: b,
                    });
                }
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
                if d.is_fp() {
                    self.ldr(MemSize::of_bytes(size).unwrap(), d, p, 0);
                } else {
                    self.load(d, p, 0, size);
                }
            }
            OpKind::Store { ty, .. } => {
                let (v, p) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let size = self.type_size(ty);
                if v.is_fp() {
                    self.str_(MemSize::of_bytes(size).unwrap(), v, p, 0);
                } else {
                    self.store(v, p, 0, size);
                }
            }
            OpKind::VaStart => {
                let ap = self.operand(op, 0)?;
                self.va_start(ap)?;
            }
            OpKind::VaArg => {
                let ap = self.operand(op, 0)?;
                let v = body.results(op).next().unwrap();
                let t = body.ty(v);
                if self.is_composite(t) {
                    let leaves = self.va_arg_composite(ap, t)?;
                    self.set_regs(v, leaves);
                } else {
                    let d = self.val(v);
                    self.va_arg(ap, t, d);
                }
            }
            // The cursor needs no cleanup on AAPCS64.
            OpKind::VaEnd => {}
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
            OpKind::Call { callee } | OpKind::Invoke { callee, .. } => {
                let func = self.cx.funcs[body.str(callee)];
                let args = (0..body.operands(op).len())
                    .map(|i| self.operand_regs(op, i))
                    .collect::<Result<Vec<_>>>()?;
                // The argument and result types as the call has them, in this function's table.
                let ps = arg_tys(body, op, 0);
                let rs: Vec<Ty> = body.results(op).map(|v| body.ty(v)).collect();
                if self.cx.variadic(func) {
                    // A variadic callee is called through its address, with every argument's
                    // type in the call's signature: on Linux, variadic arguments go where fixed
                    // ones of their types would (decision: Varargs).
                    self.sigs.push((ps.clone(), rs.clone()));
                    let sig = (self.sigs.len() - 1) as u32;
                    let target = self.fresh();
                    self.emit(Inst::AdrlFunc { d: target, func });
                    self.call(op, &args, &ps, &rs, |s| {
                        s.emit(Inst::Blr { n: target, sig });
                    })?;
                } else {
                    self.call(op, &args, &ps, &rs, |s| {
                        s.emit(Inst::Bl { func });
                    })?;
                }
                let throws = self.cx.throws.get(func as usize).copied().unwrap_or(false);
                self.after_call(kind, throws);
            }
            OpKind::CallIndirect(sig) | OpKind::InvokeIndirect { sig, .. } => {
                let args = (0..body.operands(op).len())
                    .map(|i| self.operand_regs(op, i))
                    .collect::<Result<Vec<_>>>()?;
                let Some(Shape::Func(ps, rs, va)) = body.types().shape_of(sig) else {
                    return Err(format!("{}not a function type", at(self.loc)));
                };
                // A variadic call's signature lists every argument's type.
                let (ps, rs) = if va {
                    (arg_tys(body, op, 1), rs.to_vec())
                } else {
                    (ps.to_vec(), rs.to_vec())
                };
                self.sigs.push((ps.clone(), rs.clone()));
                let sig = (self.sigs.len() - 1) as u32;
                let target = args[0][0];
                self.call(op, &args[1..], &ps, &rs, |s| {
                    s.emit(Inst::Blr { n: target, sig });
                })?;
                let throws = self.cx.throws.iter().any(|&t| t);
                self.after_call(kind, throws);
            }
            OpKind::Throw => {
                // Make it the pending exception and return through the epilogue (decision:
                // Exceptions at run time).
                let v = self.operand(op, 0)?;
                self.emit(Inst::ExnSet { n: v });
                self.emit(Inst::B { t: self.exit });
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
            OpKind::Ret if self.rets.len() == 1 && self.is_composite(self.rets[0]) => {
                let t = self.rets[0];
                check_pass(body.types(), self.sp, self.loc, t)?;
                let leaves = self.operand_regs(op, 0)?;
                match self.res_ptr {
                    None => {
                        let dsts =
                            abi::res_regs(body.types(), self.sp, self.rets).unwrap_or_default();
                        let srcs = self.pieces(t, &leaves);
                        self.moves(&dsts, &srcs);
                    }
                    Some(area) => self.store_leaves(t, &leaves, area, 0),
                }
                self.emit(Inst::B { t: self.exit });
            }
            OpKind::Ret => {
                let vals = self.operands(op)?;
                let rets = self.rets;
                match self.res_ptr {
                    None => {
                        let dsts = abi::res_regs(body.types(), self.sp, rets).unwrap_or_default();
                        let srcs: Vec<Reg> = vals
                            .iter()
                            .zip(&dsts)
                            .zip(rets)
                            .map(|((&v, &r), &t)| self.in_class(v, r.is_fp(), fsize(t)))
                            .collect();
                        self.moves(&dsts, &srcs);
                    }
                    Some(area) => {
                        for (i, (&v, &t)) in vals.iter().zip(rets).enumerate() {
                            self.str_(slot_size(t), v, area, 8 * i as i64);
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
            OpKind::FloatConst { value } => {
                let d = self.result(op, 0);
                let fs = fsize(body.ty(body.results(op).next().unwrap()));
                self.fconst(d, fs, value);
            }
            OpKind::FloatBin(fop) => {
                let (a, b) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let fs = self.fs_of(op, 0);
                let d = self.result(op, 0);
                let op = match fop {
                    FBinOp::Add => FAluOp::Fadd,
                    FBinOp::Sub => FAluOp::Fsub,
                    FBinOp::Mul => FAluOp::Fmul,
                    FBinOp::Div => FAluOp::Fdiv,
                    FBinOp::Copysign => {
                        self.copysign(fs, d, a, b);
                        return Ok(());
                    }
                };
                self.emit(Inst::Falu {
                    op,
                    fs,
                    d,
                    n: a,
                    m: b,
                });
            }
            OpKind::FloatUn(fop) => {
                let a = self.operand(op, 0)?;
                let fs = self.fs_of(op, 0);
                let d = self.result(op, 0);
                let op = match fop {
                    FUnOp::Neg => FUnaryOp::Fneg,
                    FUnOp::Abs => FUnaryOp::Fabs,
                    FUnOp::Sqrt => FUnaryOp::Fsqrt,
                };
                self.emit(Inst::Funary { op, fs, d, n: a });
            }
            OpKind::FloatFma => {
                // `fmadd` adds to its destination: `d = c`, then `d += a * b`.
                let (a, b, c) = (
                    self.operand(op, 0)?,
                    self.operand(op, 1)?,
                    self.operand(op, 2)?,
                );
                let fs = self.fs_of(op, 0);
                let d = self.result(op, 0);
                self.mov(d, c);
                self.emit(Inst::Fmadd { fs, d, n: a, m: b });
            }
            OpKind::FloatCmp(p) => {
                let (a, b) = (self.operand(op, 0)?, self.operand(op, 1)?);
                let fs = self.fs_of(op, 0);
                let d = self.result(op, 0);
                self.emit(Inst::Fcmp { fs, n: a, m: b });
                self.fcset(d, p);
            }
            OpKind::FloatExt | OpKind::FloatTrunc => {
                let a = self.operand(op, 0)?;
                let src = self.fs_of(op, 0);
                let d = self.result(op, 0);
                let dst = fsize(body.ty(body.results(op).next().unwrap()));
                self.emit(Inst::Fcvt { dst, src, d, n: a });
            }
            OpKind::FloatToInt { signed, edge } => {
                let a = self.operand(op, 0)?;
                let fs = self.fs_of(op, 0);
                let d = self.result(op, 0);
                let w = width_bits(body.ty(body.results(op).next().unwrap()));
                self.float_to_int(signed, edge, w, fs, d, a);
            }
            OpKind::IntToFloat { signed } => {
                let w = self.width_of(op, 0);
                let a = self.operand(op, 0)?;
                let d = self.result(op, 0);
                let fs = fsize(body.ty(body.results(op).next().unwrap()));
                let x = if signed { self.sx(a, w) } else { self.zx(a, w) };
                self.emit(Inst::Cvtf {
                    signed,
                    fs,
                    sf: Sf::X,
                    d,
                    n: x,
                });
            }
            OpKind::FloatFromBits => {
                let a = self.operand(op, 0)?;
                let d = self.result(op, 0);
                let fs = fsize(body.ty(body.results(op).next().unwrap()));
                self.fmov(fs, d, a);
            }
            OpKind::FloatToBits => {
                let a = self.operand(op, 0)?;
                let fs = self.fs_of(op, 0);
                let d = self.result(op, 0);
                self.fmov(fs, d, a);
            }
            OpKind::Check(reason) => {
                // Bit 0 holds the `i1`; a `poison` one (UB) may trap or not.
                let c = self.operand(op, 0)?;
                self.emit(Inst::AluImm {
                    op: AluImmOp::Ands,
                    sf: Sf::X,
                    d: Reg::XZR,
                    n: c,
                    imm: 1,
                });
                self.trap_if(Cond::Eq, reason);
            }
            k => {
                return Err(match support(k) {
                    Support::No(why) => format!("{}{} {why}", at(self.loc), k.mnemonic()),
                    Support::Yes => format!(
                        "{}internal error: {} is declared supported (`isel::support`) but \
                         instruction selection has no case for it",
                        at(self.loc),
                        k.mnemonic()
                    ),
                });
            }
        }
        Ok(())
    }

    /// `float.copysign`: `a`'s magnitude and `b`'s sign, on their bits.
    fn copysign(&mut self, fs: FSize, d: Reg, a: Reg, b: Reg) {
        let sign = 1u64 << (fs.bits() - 1);
        let (ta, tb) = (self.fresh(), self.fresh());
        self.fmov(fs, ta, a);
        self.fmov(fs, tb, b);
        let (ma, mb) = (self.fresh(), self.fresh());
        self.emit(Inst::AluImm {
            op: AluImmOp::And,
            sf: Sf::X,
            d: ma,
            n: ta,
            imm: (sign - 1) as i64,
        });
        self.emit(Inst::AluImm {
            op: AluImmOp::And,
            sf: Sf::X,
            d: mb,
            n: tb,
            imm: sign as i64,
        });
        let t = self.alu_new(AluOp::Orr, ma, mb);
        self.fmov(fs, d, t);
    }

    /// `d` = whether float predicate `p` holds, after `fcmp`: one condition on the flags, or
    /// two for `ueq` (equal or unordered) and `one` (less or greater).
    fn fcset(&mut self, d: Reg, p: FPred) {
        let c = match p {
            FPred::Oeq => Cond::Eq,
            FPred::Olt => Cond::Mi,
            FPred::Ole => Cond::Ls,
            FPred::Ogt => Cond::Gt,
            FPred::Oge => Cond::Ge,
            FPred::Ord => Cond::Vc,
            FPred::Uno => Cond::Vs,
            FPred::Une => Cond::Ne,
            FPred::Ult => Cond::Lt,
            FPred::Ule => Cond::Le,
            FPred::Ugt => Cond::Hi,
            FPred::Uge => Cond::Hs,
            FPred::Ueq | FPred::One => {
                // `csinc d, t, xzr, c`: `t` if `c` holds, else 1.
                let (first, c) = if p == FPred::Ueq {
                    (Cond::Eq, Cond::Vc)
                } else {
                    (Cond::Mi, Cond::Le)
                };
                let t = self.fresh();
                self.cset(t, first);
                self.emit(Inst::Csel {
                    op: CselOp::Csinc,
                    c,
                    sf: Sf::X,
                    d,
                    n: t,
                    m: Reg::XZR,
                });
                return;
            }
        };
        self.cset(d, c);
    }

    /// `float.to_int` into `w` bits: `fcvtzs`/`fcvtzu` at 64 bits, which saturate and give 0 for
    /// NaN, then a clamp to `w` bits for `.sat`; `.trap` first traps on NaN and on values whose
    /// integer part is out of range (compared with exactly representable bounds); `.ub` needs
    /// neither.
    fn float_to_int(&mut self, signed: bool, edge: CvtEdge, w: u32, fs: FSize, d: Reg, a: Reg) {
        if edge == CvtEdge::Trap {
            self.emit(Inst::Fcmp { fs, n: a, m: a });
            self.trap_if(Cond::Vs, TrapReason::Convert);
            // The integer part is at least `lo` when `a > lo - 1`, or, where `lo - 1` doesn't
            // fit the format (no float lies between it and `lo`), when `a ≥ lo`.
            let m = if fs == FSize::S { 23 } else { 52 };
            let (lo, hi): (i128, i128) = if signed {
                (-(1i128 << (w - 1)), 1i128 << (w - 1))
            } else {
                (0, 1i128 << w)
            };
            let exact = !signed || w <= m + 1;
            let lb = self.fresh_fp();
            self.fconst(lb, fs, float_bits(fs, if exact { lo - 1 } else { lo }));
            self.emit(Inst::Fcmp { fs, n: a, m: lb });
            self.trap_if(if exact { Cond::Ls } else { Cond::Mi }, TrapReason::Convert);
            let hb = self.fresh_fp();
            self.fconst(hb, fs, float_bits(fs, hi));
            self.emit(Inst::Fcmp { fs, n: a, m: hb });
            self.trap_if(Cond::Ge, TrapReason::Convert);
        }
        let r = self.fresh();
        self.emit(Inst::Fcvtz {
            signed,
            sf: Sf::X,
            fs,
            d: r,
            n: a,
        });
        if edge != CvtEdge::Sat || w >= 64 {
            self.mov(d, r);
            return;
        }
        // Clamp the 64-bit result to `w` bits.
        let hi = if signed { mask(w - 1) } else { mask(w) };
        let h = self.konst(hi);
        self.alu(AluOp::Subs, Reg::XZR, r, h);
        let c = if signed { Cond::Gt } else { Cond::Hi };
        if !signed {
            self.emit(Inst::Csel {
                op: CselOp::Csel,
                c,
                sf: Sf::X,
                d,
                n: h,
                m: r,
            });
            return;
        }
        let t = self.fresh();
        self.emit(Inst::Csel {
            op: CselOp::Csel,
            c,
            sf: Sf::X,
            d: t,
            n: h,
            m: r,
        });
        let l = self.konst(!mask(w - 1));
        self.alu(AluOp::Subs, Reg::XZR, t, l);
        self.emit(Inst::Csel {
            op: CselOp::Csel,
            c: Cond::Lt,
            sf: Sf::X,
            d,
            n: l,
            m: t,
        });
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

    /// A call: arguments where the convention puts them (each argument's registers: a scalar's
    /// one, a composite's leaves'), the call, then the results. The types are this function's.
    fn call(
        &mut self,
        op: OpId,
        args: &[Vec<Reg>],
        ps: &[Ty],
        rets: &[Ty],
        emit: impl FnOnce(&mut Self),
    ) -> Result<()> {
        let types = self.body.types();
        for &t in ps.iter().chain(rets) {
            check_pass(types, self.sp, self.loc, t)?;
        }
        let (locs, _) = abi::arg_locs(types, self.sp, ps);
        let (mut dsts, mut srcs) = (Vec::new(), Vec::new());
        for ((a, &t), &l) in args.iter().zip(ps).zip(&locs) {
            match l {
                ArgLoc::Stack(off) => self.str_(slot_size(t), a[0], Reg::SP, i64::from(off)),
                ArgLoc::Reg(r) => {
                    dsts.push(r);
                    srcs.push(a[0]);
                }
                ArgLoc::Regs(..) => {
                    let pieces = self.pieces(t, a);
                    dsts.extend(l.regs());
                    srcs.extend(pieces);
                }
                ArgLoc::Mem(off) => self.store_leaves(t, a, Reg::SP, i64::from(off)),
                ArgLoc::RefReg(_) | ArgLoc::RefStack(_) => {
                    // A copy the callee owns, in this frame.
                    let (size, align) = types.dims(self.sp, t);
                    let slot = self.local(size as u64, align);
                    self.store_leaves(t, a, Reg::SP, slot);
                    let p = self.fresh();
                    self.add_imm(p, Reg::SP, slot);
                    match l {
                        ArgLoc::RefReg(r) => {
                            dsts.push(r);
                            srcs.push(p);
                        }
                        ArgLoc::RefStack(off) => self.str_(MemSize::X, p, Reg::SP, i64::from(off)),
                        _ => unreachable!(),
                    }
                }
                ArgLoc::Nothing => {}
            }
        }
        let rr = abi::res_regs(types, self.sp, rets);
        let whole = rets.len() == 1 && types.is_composite(rets[0]);
        let area = match (&rr, whole) {
            (Some(_), _) => None,
            (None, true) => {
                let (size, align) = types.dims(self.sp, rets[0]);
                Some(self.local(size as u64, align))
            }
            (None, false) => Some(self.local(8 * rets.len() as u64, 8)),
        };
        if let Some(off) = area {
            self.add_imm(Reg::x(8), Reg::SP, off);
        }
        self.moves(&dsts, &srcs);
        emit(self);
        if whole {
            let t = rets[0];
            let v = self.body.results(op).next().unwrap();
            let leaves = match (rr, area) {
                (Some(rs), _) => {
                    let regs: Vec<Reg> = rs
                        .iter()
                        .map(|&r| {
                            let d = self.fresh_like(r);
                            self.mov(d, r);
                            d
                        })
                        .collect();
                    self.unpack(t, &regs)?
                }
                (None, Some(off)) => self.load_leaves(t, Reg::SP, off)?,
                (None, None) => unreachable!(),
            };
            self.set_regs(v, leaves);
            return Ok(());
        }
        let results: Vec<Reg> = (0..rets.len()).map(|i| self.result(op, i)).collect();
        match (rr, area) {
            (Some(rs), _) => {
                for ((&r, &t), &s) in results.iter().zip(rets).zip(&rs) {
                    if r.is_fp() == s.is_fp() {
                        self.mov(r, s);
                    } else {
                        self.fmov(fsize(t), r, s);
                    }
                }
            }
            (None, Some(off)) => {
                for (i, (&r, &t)) in results.iter().zip(rets).enumerate() {
                    self.ldr(slot_size(t), r, Reg::SP, off + 8 * i as i64);
                }
            }
            (None, None) => unreachable!(),
        }
        Ok(())
    }

    /// Save the argument registers a variadic function's named parameters leave over, as
    /// AAPCS64 lays them out for `va_list` (decision: Varargs): `x[n]`…`x7` in 8-byte slots
    /// ending at `__gr_top`, and `d[m]`…`d7` (the low 64 bits FIR uses of `q[m]`…`q7`) in 16-byte
    /// slots ending at `__vr_top`.
    fn save_va_regs(&mut self, ps: &[Ty]) {
        // NGRN, NSRN, and NSAA after the named parameters, composites included.
        let (_, (gp, fp, stack)) = abi::arg_state(self.body.types(), self.sp, ps);
        let (gr_size, vr_size) = (8 * i64::from(8 - gp), 16 * i64::from(8 - fp));
        let gr_off = self.local(gr_size as u64, 8);
        let vr_off = self.local(vr_size as u64, 16);
        for i in gp..8 {
            let off = gr_off + 8 * i64::from(i - gp);
            self.str_(MemSize::X, Reg::x(i), Reg::SP, off);
        }
        for i in fp..8 {
            let off = vr_off + 16 * i64::from(i - fp);
            self.str_(MemSize::X, Reg::d(i), Reg::SP, off);
        }
        self.va = Some(VaFrame {
            gr_off,
            gr_size,
            vr_off,
            vr_size,
            stack: 16 + i64::from(stack),
        });
    }

    /// `va.start`: fill the `va_list` at `ap` (AAPCS64: `__stack`, `__gr_top`, `__vr_top`,
    /// `__gr_offs`, `__vr_offs`).
    fn va_start(&mut self, ap: Reg) -> Result<()> {
        let Some(va) = self.va else {
            return Err(format!(
                "{}va.start in a function that isn't variadic",
                at(self.loc)
            ));
        };
        let words = [
            (Reg::FP, va.stack),
            (Reg::SP, va.gr_off + va.gr_size),
            (Reg::SP, va.vr_off + va.vr_size),
        ];
        for (i, (base, off)) in words.into_iter().enumerate() {
            let t = self.fresh();
            self.add_imm(t, base, off);
            self.str_(MemSize::X, t, ap, 8 * i as i64);
        }
        for (i, size) in [va.gr_size, va.vr_size].into_iter().enumerate() {
            let t = self.konst(-size as u64);
            self.str_(MemSize::W, t, ap, 24 + 4 * i as i64);
        }
        Ok(())
    }

    /// `va.arg T`: AAPCS64's algorithm (decision: Varargs). While the class's offset
    /// (`__gr_offs` or `__vr_offs`) is negative, the argument is in the register save area at
    /// the top (`__gr_top`, `__vr_top`) plus the offset, and the offset moves on by a register's
    /// slot (8 or 16 bytes); after that, it is at `__stack`, which moves on by 8 bytes.
    fn va_arg(&mut self, ap: Reg, t: Ty, d: Reg) {
        let size = self.type_size(t);
        let (offs_at, top_at, step) = if t.is_float() {
            (28, 16, 16)
        } else {
            (24, 8, 8)
        };
        let (reg, stack, join) = (
            self.new_block(false),
            self.new_block(false),
            self.new_block(false),
        );
        let w = self.fresh();
        self.ldr(MemSize::W, w, ap, offs_at);
        let offs = self.sx(w, 32);
        self.cmp_imm(offs, 0);
        let check = self.new_block(false);
        self.emit(Inst::BCond {
            c: Cond::Ge,
            t: stack,
            f: check,
        });
        self.switch_to(check);
        let next = self.fresh();
        self.add_imm(next, offs, step);
        self.str_(MemSize::W, next, ap, offs_at);
        self.cmp_imm(next, 0);
        self.emit(Inst::BCond {
            c: Cond::Gt,
            t: stack,
            f: reg,
        });
        self.switch_to(reg);
        let top = self.fresh();
        self.ldr(MemSize::X, top, ap, top_at);
        let at = self.alu_new(AluOp::Add, top, offs);
        self.load_into(d, at, size);
        self.emit(Inst::B { t: join });
        self.switch_to(stack);
        let sp = self.fresh();
        self.ldr(MemSize::X, sp, ap, 0);
        self.load_into(d, sp, size);
        let sp2 = self.fresh();
        self.add_imm(sp2, sp, 8);
        self.str_(MemSize::X, sp2, ap, 0);
        self.emit(Inst::B { t: join });
        self.switch_to(join);
    }

    /// `va.arg` of a composite: AAPCS64's algorithm (decision: Varargs) for its class. Up to 16
    /// bytes, it takes as many 8-byte slots of the general-purpose save area as it has words
    /// (from an even one if it is 16-byte aligned), or else the stack; an HFA takes one 16-byte
    /// slot of the FP save area per member, or else the stack; a larger one is a pointer, read
    /// as a general-purpose argument, to a copy. Once a class's offset turns positive it stays,
    /// and the arguments after go on the stack too, as the caller placed them.
    fn va_arg_composite(&mut self, ap: Reg, t: Ty) -> Result<Vec<Reg>> {
        check_pass(self.body.types(), self.sp, self.loc, t)?;
        let kind = abi::pass_kind(self.body.types(), self.sp, t);
        let size = self.type_size(t);
        if kind == abi::PassKind::Ref {
            let p = self.fresh();
            self.va_arg(ap, Ty::Ptr, p);
            return self.load_leaves(t, p, 0);
        }
        let (fp, slots, even) = match kind {
            abi::PassKind::Hfa(_, n) => (true, n, false),
            abi::PassKind::Words(n, even) => (false, n, even),
            _ => (false, 0, false),
        };
        let (offs_at, top_at, step) = if fp { (28, 16, 16) } else { (24, 8, 8) };
        let (reg, stack, join) = (
            self.new_block(false),
            self.new_block(false),
            self.new_block(false),
        );
        let leaves = self.fresh_leaves(t)?;
        let w = self.fresh();
        self.ldr(MemSize::W, w, ap, offs_at);
        let offs0 = self.sx(w, 32);
        self.cmp_imm(offs0, 0);
        let check = self.new_block(false);
        self.emit(Inst::BCond {
            c: Cond::Ge,
            t: stack,
            f: check,
        });
        self.switch_to(check);
        let offs = if even {
            let t = self.fresh();
            self.add_imm(t, offs0, 15);
            let m = self.konst(-16i64 as u64);
            self.alu_new(AluOp::And, t, m)
        } else {
            offs0
        };
        let next = self.fresh();
        self.add_imm(next, offs, i64::from(step * slots));
        self.str_(MemSize::W, next, ap, offs_at);
        self.cmp_imm(next, 0);
        self.emit(Inst::BCond {
            c: Cond::Gt,
            t: stack,
            f: reg,
        });
        self.switch_to(reg);
        let top = self.fresh();
        self.ldr(MemSize::X, top, ap, top_at);
        let at = self.alu_new(AluOp::Add, top, offs);
        let got = if fp {
            // One member per 16-byte slot, in memory order: the leaf at offset `o` is member
            // `o / size`.
            let mut got = Vec::new();
            for (o, l) in self.leaves_of(t) {
                let r = self.fresh_fp();
                let size = self.type_size(l);
                let i = o / size;
                self.ldr(MemSize::of_bytes(size).unwrap(), r, at, 16 * i as i64);
                got.push(r);
            }
            got
        } else {
            self.load_leaves(t, at, 0)?
        };
        self.moves(&leaves, &got);
        self.emit(Inst::B { t: join });
        self.switch_to(stack);
        let sp0 = self.fresh();
        self.ldr(MemSize::X, sp0, ap, 0);
        let sp = if even {
            let t = self.fresh();
            self.add_imm(t, sp0, 15);
            let m = self.konst(-16i64 as u64);
            self.alu_new(AluOp::And, t, m)
        } else {
            sp0
        };
        let got = self.load_leaves(t, sp, 0)?;
        self.moves(&leaves, &got);
        let sp2 = self.fresh();
        self.add_imm(sp2, sp, size.next_multiple_of(8) as i64);
        self.str_(MemSize::X, sp2, ap, 0);
        self.emit(Inst::B { t: join });
        self.switch_to(join);
        Ok(leaves)
    }

    /// Load `size` bytes at `base` into `d`, of either class.
    fn load_into(&mut self, d: Reg, base: Reg, size: u64) {
        if d.is_fp() {
            self.ldr(MemSize::of_bytes(size).unwrap(), d, base, 0);
        } else {
            self.load(d, base, 0, size);
        }
    }

    /// After a call that may throw: if an exception is pending, a plain call returns at once
    /// (through the epilogue, leaving it pending for its caller), and a `func.invoke` takes it
    /// and jumps to its handler block with it.
    fn after_call(&mut self, kind: OpKind, throws: bool) {
        if !throws {
            return;
        }
        let cont = self.new_block(false);
        match kind {
            OpKind::Invoke { unwind, .. } | OpKind::InvokeIndirect { unwind, .. } => {
                let land = self.new_block(true);
                self.emit(Inst::BExn { t: land, f: cont });
                self.switch_to(land);
                let e = self.fresh();
                self.emit(Inst::ExnTake { d: e });
                let label = self.body.str(self.body.succ(unwind).label).to_owned();
                self.jump(&label, &[e]);
            }
            _ => self.emit(Inst::BExn {
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
            // An `i1` shifts by 0, the amount modulo 1.
            ShiftEdge::Mask if w == 1 => self.konst(0),
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

/// An integer or byte type's width (64 for a pointer).
fn width_bits(t: Ty) -> u32 {
    match t {
        Ty::Int(w) | Ty::Byte(w) => w,
        _ => 64,
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
