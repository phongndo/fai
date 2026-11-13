//! The backend's working form of LFIR: one function's machine code as flat arrays.
//!
//! Each [`Inst`] is one `aarch64.*` op with its immediates inline (block indices instead of
//! labels, symbol indices instead of names), so instruction selection, register allocation,
//! and the emitter work on `Copy` values in a `Vec` without a [`fai_ir::Body`]'s side tables.
//! [`super::lfir`] turns it into an LFIR module (text, the interpreters), and
//! [`super::emit`] into assembly. A function's blocks are runs of `insts`, in layout order.

use fai_ir::ir::{
    AluImmOp, AluOp, Cond, CselOp, FAluOp, FSize, FUnaryOp, Loc, MemSize, MovOp, Reg, Sf,
    ShiftImmOp, TrapReason, Ty,
};

/// One instruction: an `aarch64.*` op of LFIR. Blocks are indices into [`MFunc::blocks`];
/// functions are indices like the interpreter's (the module's functions, then its external
/// functions); globals are indices into the module's globals.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Inst {
    Alu {
        op: AluOp,
        sf: Sf,
        d: Reg,
        n: Reg,
        m: Reg,
    },
    AluImm {
        op: AluImmOp,
        sf: Sf,
        d: Reg,
        n: Reg,
        imm: i64,
    },
    ShiftImm {
        op: ShiftImmOp,
        sf: Sf,
        d: Reg,
        n: Reg,
        amount: u8,
    },
    Ext {
        signed: bool,
        sf: Sf,
        d: Reg,
        n: Reg,
        width: u8,
    },
    Mov {
        sf: Sf,
        d: Reg,
        n: Reg,
    },
    MovWide {
        op: MovOp,
        sf: Sf,
        d: Reg,
        imm: u16,
        hw: u8,
    },
    Csel {
        op: CselOp,
        c: Cond,
        sf: Sf,
        d: Reg,
        n: Reg,
        m: Reg,
    },
    Ldr {
        size: MemSize,
        d: Reg,
        base: Reg,
        off: i64,
    },
    Str {
        size: MemSize,
        s: Reg,
        base: Reg,
        off: i64,
    },
    Adrl {
        d: Reg,
        global: u32,
    },
    AdrlFunc {
        d: Reg,
        func: u32,
    },
    B {
        t: u32,
    },
    BCond {
        c: Cond,
        t: u32,
        f: u32,
    },
    Ret,
    Trap(TrapReason),
    Bl {
        func: u32,
    },
    /// A call through `n`; `sig` indexes [`MFunc::sigs`].
    Blr {
        n: Reg,
        sig: u32,
    },
    /// `family` indexes [`MModule::families`].
    BlAlloc {
        family: u32,
        align: u32,
    },
    BlFree {
        family: u32,
    },
    /// `aarch64.exn.set`: `n` becomes the pending exception.
    ExnSet {
        n: Reg,
    },
    /// `aarch64.exn.take`: `d` gets the pending exception, which stops being pending.
    ExnTake {
        d: Reg,
    },
    /// `aarch64.b.exn`: to `t` if an exception is pending, else to `f`.
    BExn {
        t: u32,
        f: u32,
    },
    Falu {
        op: FAluOp,
        fs: FSize,
        d: Reg,
        n: Reg,
        m: Reg,
    },
    /// `fmov` (also between classes), `fabs`, `fneg`, `fsqrt`.
    Funary {
        op: FUnaryOp,
        fs: FSize,
        d: Reg,
        n: Reg,
    },
    /// `d := n * m + d`.
    Fmadd {
        fs: FSize,
        d: Reg,
        n: Reg,
        m: Reg,
    },
    FmovImm {
        fs: FSize,
        d: Reg,
        imm: u8,
    },
    Fcmp {
        fs: FSize,
        n: Reg,
        m: Reg,
    },
    Fcsel {
        c: Cond,
        fs: FSize,
        d: Reg,
        n: Reg,
        m: Reg,
    },
    Fcvt {
        dst: FSize,
        src: FSize,
        d: Reg,
        n: Reg,
    },
    Cvtf {
        signed: bool,
        fs: FSize,
        sf: Sf,
        d: Reg,
        n: Reg,
    },
    Fcvtz {
        signed: bool,
        sf: Sf,
        fs: FSize,
        d: Reg,
        n: Reg,
    },
}

impl Inst {
    /// Whether the instruction ends a block.
    pub fn is_terminator(self) -> bool {
        matches!(
            self,
            Inst::B { .. } | Inst::BCond { .. } | Inst::Ret | Inst::Trap(_) | Inst::BExn { .. }
        )
    }

    /// Whether the instruction is a call, which clobbers the caller-saved registers.
    pub fn is_call(self) -> bool {
        matches!(
            self,
            Inst::Bl { .. } | Inst::Blr { .. } | Inst::BlAlloc { .. } | Inst::BlFree { .. }
        )
    }

    /// The registers the instruction writes and reads, apart from what a call does under the
    /// calling convention (its argument registers and [`CALLER_SAVED`]; see `regalloc`).
    pub fn regs(self, defs: &mut Vec<Reg>, uses: &mut Vec<Reg>) {
        defs.clear();
        uses.clear();
        match self {
            Inst::Alu { d, n, m, .. }
            | Inst::Csel { d, n, m, .. }
            | Inst::Falu { d, n, m, .. }
            | Inst::Fcsel { d, n, m, .. } => {
                defs.push(d);
                uses.extend([n, m]);
            }
            Inst::Fmadd { d, n, m, .. } => {
                defs.push(d);
                uses.extend([n, m, d]);
            }
            Inst::Funary { d, n, .. }
            | Inst::Fcvt { d, n, .. }
            | Inst::Cvtf { d, n, .. }
            | Inst::Fcvtz { d, n, .. } => {
                defs.push(d);
                uses.push(n);
            }
            Inst::FmovImm { d, .. } => defs.push(d),
            Inst::Fcmp { n, m, .. } => uses.extend([n, m]),
            Inst::AluImm { d, n, .. }
            | Inst::ShiftImm { d, n, .. }
            | Inst::Ext { d, n, .. }
            | Inst::Mov { d, n, .. } => {
                defs.push(d);
                uses.push(n);
            }
            Inst::MovWide { op, d, .. } => {
                defs.push(d);
                if op == MovOp::Movk {
                    uses.push(d);
                }
            }
            Inst::Ldr { d, base, .. } => {
                defs.push(d);
                uses.push(base);
            }
            Inst::Str { s, base, .. } => uses.extend([s, base]),
            Inst::Adrl { d, .. } | Inst::AdrlFunc { d, .. } => defs.push(d),
            Inst::Blr { n, .. } | Inst::ExnSet { n } => uses.push(n),
            Inst::ExnTake { d } => defs.push(d),
            Inst::B { .. }
            | Inst::BExn { .. }
            | Inst::BCond { .. }
            | Inst::Ret
            | Inst::Trap(_)
            | Inst::Bl { .. }
            | Inst::BlAlloc { .. }
            | Inst::BlFree { .. } => {}
        }
    }

    /// The instruction with every register renamed by `f`.
    pub fn map_regs(self, mut f: impl FnMut(Reg, bool) -> Reg) -> Inst {
        // `f(r, is_def)`; a `movk`'s or `fmadd`'s destination is both, and is renamed once, as
        // a def.
        match self {
            Inst::Falu { op, fs, d, n, m } => Inst::Falu {
                op,
                fs,
                n: f(n, false),
                m: f(m, false),
                d: f(d, true),
            },
            Inst::Fcsel { c, fs, d, n, m } => Inst::Fcsel {
                c,
                fs,
                n: f(n, false),
                m: f(m, false),
                d: f(d, true),
            },
            Inst::Fmadd { fs, d, n, m } => Inst::Fmadd {
                fs,
                n: f(n, false),
                m: f(m, false),
                d: f(d, true),
            },
            Inst::Funary { op, fs, d, n } => Inst::Funary {
                op,
                fs,
                n: f(n, false),
                d: f(d, true),
            },
            Inst::Fcvt { dst, src, d, n } => Inst::Fcvt {
                dst,
                src,
                n: f(n, false),
                d: f(d, true),
            },
            Inst::Cvtf {
                signed,
                fs,
                sf,
                d,
                n,
            } => Inst::Cvtf {
                signed,
                fs,
                sf,
                n: f(n, false),
                d: f(d, true),
            },
            Inst::Fcvtz {
                signed,
                sf,
                fs,
                d,
                n,
            } => Inst::Fcvtz {
                signed,
                sf,
                fs,
                n: f(n, false),
                d: f(d, true),
            },
            Inst::FmovImm { fs, d, imm } => Inst::FmovImm {
                fs,
                d: f(d, true),
                imm,
            },
            Inst::Fcmp { fs, n, m } => Inst::Fcmp {
                fs,
                n: f(n, false),
                m: f(m, false),
            },
            Inst::Alu { op, sf, d, n, m } => Inst::Alu {
                op,
                sf,
                n: f(n, false),
                m: f(m, false),
                d: f(d, true),
            },
            Inst::Csel { op, c, sf, d, n, m } => Inst::Csel {
                op,
                c,
                sf,
                n: f(n, false),
                m: f(m, false),
                d: f(d, true),
            },
            Inst::AluImm { op, sf, d, n, imm } => Inst::AluImm {
                op,
                sf,
                n: f(n, false),
                d: f(d, true),
                imm,
            },
            Inst::ShiftImm {
                op,
                sf,
                d,
                n,
                amount,
            } => Inst::ShiftImm {
                op,
                sf,
                n: f(n, false),
                d: f(d, true),
                amount,
            },
            Inst::Ext {
                signed,
                sf,
                d,
                n,
                width,
            } => Inst::Ext {
                signed,
                sf,
                n: f(n, false),
                d: f(d, true),
                width,
            },
            Inst::Mov { sf, d, n } => Inst::Mov {
                sf,
                n: f(n, false),
                d: f(d, true),
            },
            Inst::MovWide { op, sf, d, imm, hw } => Inst::MovWide {
                op,
                sf,
                d: f(d, true),
                imm,
                hw,
            },
            Inst::Ldr { size, d, base, off } => Inst::Ldr {
                size,
                base: f(base, false),
                d: f(d, true),
                off,
            },
            Inst::Str { size, s, base, off } => Inst::Str {
                size,
                s: f(s, false),
                base: f(base, false),
                off,
            },
            Inst::Adrl { d, global } => Inst::Adrl {
                d: f(d, true),
                global,
            },
            Inst::AdrlFunc { d, func } => Inst::AdrlFunc {
                d: f(d, true),
                func,
            },
            Inst::Blr { n, sig } => Inst::Blr {
                n: f(n, false),
                sig,
            },
            Inst::ExnSet { n } => Inst::ExnSet { n: f(n, false) },
            Inst::ExnTake { d } => Inst::ExnTake { d: f(d, true) },
            i => i,
        }
    }
}

/// One function's machine code.
#[derive(Clone, Debug, Default)]
pub struct MFunc {
    /// The function's index in the module.
    pub index: u32,
    /// The instructions, block after block.
    pub insts: Vec<Inst>,
    /// Each instruction's source location (a column parallel to `insts`).
    pub locs: Vec<Option<Loc>>,
    /// Where each block starts in `insts`; a block ends where the next starts.
    pub blocks: Vec<u32>,
    /// How many virtual registers the code names (`v0` to `vN-1`).
    pub nvregs: u32,
    /// The signatures of calls through pointers: parameter and result types, of the source
    /// function's type table.
    pub sigs: Vec<(Vec<Ty>, Vec<Ty>)>,
    /// The registers each of those calls reads and writes.
    pub sig_shapes: Vec<super::abi::CallShape>,
    pub frame: Frame,
}

/// What the frame lowering needs to know about a function's stack frame.
#[derive(Clone, Copy, Debug, Default)]
pub struct Frame {
    /// The size of the outgoing-argument area at the bottom of the frame.
    pub outgoing: u32,
    /// The size of the locals (`mem.stack` slots and results areas), right above it.
    pub locals: u32,
    /// The largest alignment a local needs.
    pub align: u32,
    /// The spill slots' size, right above the locals (set by the register allocator).
    pub spills: u32,
    /// The callee-saved registers the code uses (set by the register allocator): bit `r` for
    /// `xr`.
    pub saved: u32,
    /// The callee-saved FP registers the code uses: bit `r` for `dr`.
    pub saved_fp: u32,
    /// Where the prologue's `sub sp, sp, N` is (an index into `insts`): the instruction the
    /// frame lowering replaces.
    pub alloc_at: u32,
    /// The exit block, which restores the frame and returns.
    pub exit: u32,
}

impl MFunc {
    pub fn block_range(&self, b: usize) -> std::ops::Range<usize> {
        let start = self.blocks[b] as usize;
        let end = self
            .blocks
            .get(b + 1)
            .map_or(self.insts.len(), |&e| e as usize);
        start..end
    }
}

/// A module's machine code, with what the emitter needs besides the functions.
#[derive(Clone, Debug, Default)]
pub struct MModule {
    pub funcs: Vec<MFunc>,
    /// The allocator families named by `mem.alloc` and `mem.free`.
    pub families: Vec<String>,
}

/// The general-purpose registers a call may change: `x0`…`x18` and `x30` (the FP ones are
/// `super::abi::FP_CALLER_SAVED`).
pub const CALLER_SAVED: [u32; 20] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 30,
];
