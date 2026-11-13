//! The x86-64 backend's machine code: one function as flat arrays of [`Inst`], over virtual
//! registers before allocation and physical ones after.
//!
//! Instructions are x86-64's two-address forms (`add d, s` reads and writes `d`), all 64 bits
//! wide unless they say otherwise, so a value's register always holds 64 bits of which the
//! value uses the low ones (see `super::isel`). Registers named by the hardware for an
//! instruction (`rax` and `rdx` for division, `cl` for shift amounts, the argument and result
//! registers of calls) appear in the code as physical registers, before and after allocation.
//! Blocks are runs of `insts`, in layout order, each ending in a terminator; a function's
//! prologue and epilogue are the emitter's, from [`Frame`].

use crate::ir::{Loc, Ty};
use crate::sem::TrapReason;

/// A register: one of the sixteen general-purpose registers by its hardware number, or a
/// virtual register.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Reg {
    /// `rax` 0, `rcx` 1, `rdx` 2, `rbx` 3, `rsp` 4, `rbp` 5, `rsi` 6, `rdi` 7, `r8`…`r15`.
    P(u8),
    V(u32),
}

pub const RAX: Reg = Reg::P(0);
pub const RCX: Reg = Reg::P(1);
pub const RDX: Reg = Reg::P(2);
pub const RSP: Reg = Reg::P(4);
pub const RBP: Reg = Reg::P(5);
pub const RSI: Reg = Reg::P(6);
pub const RDI: Reg = Reg::P(7);
pub const R8: Reg = Reg::P(8);
pub const R9: Reg = Reg::P(9);
/// Scratch registers for spilled values, never allocated (`r10` and `r11` carry no arguments in
/// the System V ABI, and calls may clobber them).
pub const R10: Reg = Reg::P(10);
pub const R11: Reg = Reg::P(11);

/// The integer argument registers of the System V AMD64 ABI, in order.
pub const ARG_REGS: [Reg; 6] = [RDI, RSI, RDX, RCX, R8, R9];
/// The result registers.
pub const RET_REGS: [Reg; 2] = [RAX, RDX];
/// The registers a call may change: every general-purpose register but `rbx`, `rbp`, `rsp`,
/// and `r12`…`r15`.
pub const CALLER_SAVED: [u8; 9] = [0, 1, 2, 6, 7, 8, 9, 10, 11];
/// The callee-saved registers allocation may use.
pub const CALLEE_SAVED: [u8; 5] = [3, 12, 13, 14, 15];

impl Reg {
    pub fn is_virtual(self) -> bool {
        matches!(self, Reg::V(_))
    }
}

impl std::fmt::Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Reg::P(n) => f.write_str(super::emit::reg64(n)),
            Reg::V(n) => write!(f, "v{n}"),
        }
    }
}

/// Two-operand ALU operations: `d = d op s`. All set the flags.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AluOp {
    Add,
    Sub,
    And,
    Or,
    Xor,
    Imul,
}

/// Shifts.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ShiftOp {
    Shl,
    Shr,
    Sar,
}

/// Condition codes, as `jcc`, `setcc`, and `cmovcc` spell them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Cond {
    E,
    Ne,
    L,
    Le,
    G,
    Ge,
    B,
    Be,
    A,
    Ae,
    O,
    No,
}

impl Cond {
    pub fn invert(self) -> Cond {
        match self {
            Cond::E => Cond::Ne,
            Cond::Ne => Cond::E,
            Cond::L => Cond::Ge,
            Cond::Ge => Cond::L,
            Cond::Le => Cond::G,
            Cond::G => Cond::Le,
            Cond::B => Cond::Ae,
            Cond::Ae => Cond::B,
            Cond::Be => Cond::A,
            Cond::A => Cond::Be,
            Cond::O => Cond::No,
            Cond::No => Cond::O,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Cond::E => "e",
            Cond::Ne => "ne",
            Cond::L => "l",
            Cond::Le => "le",
            Cond::G => "g",
            Cond::Ge => "ge",
            Cond::B => "b",
            Cond::Be => "be",
            Cond::A => "a",
            Cond::Ae => "ae",
            Cond::O => "o",
            Cond::No => "no",
        }
    }
}

/// A runtime function the code calls: the C library's allocator and `memmove`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Runtime {
    /// `malloc(rdi)`.
    Malloc,
    /// `aligned_alloc(rdi, rsi)`.
    AlignedAlloc,
    /// `free(rdi)`.
    Free,
    /// `memmove(rdi, rsi, rdx)`.
    Memmove,
}

impl Runtime {
    pub fn name(self) -> &'static str {
        match self {
            Runtime::Malloc => "malloc",
            Runtime::AlignedAlloc => "aligned_alloc",
            Runtime::Free => "free",
            Runtime::Memmove => "memmove",
        }
    }

    /// The argument registers it reads.
    pub fn args(self) -> &'static [Reg] {
        match self {
            Runtime::Malloc | Runtime::Free => &ARG_REGS[..1],
            Runtime::AlignedAlloc => &ARG_REGS[..2],
            Runtime::Memmove => &ARG_REGS[..3],
        }
    }
}

/// One instruction. Blocks are indices into [`MFunc::blocks`]; functions are indices like the
/// interpreter's (the module's functions, then its external functions); globals are indices
/// into the module's globals. Memory operands are a base register and a displacement.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Inst {
    /// `mov d, s` (64 bits).
    Mov {
        d: Reg,
        s: Reg,
    },
    /// `d = imm` (the emitter picks `movl`, `movq`, or `movabsq`; never touches the flags).
    MovImm {
        d: Reg,
        imm: u64,
    },
    /// `d = d op s`.
    Alu {
        op: AluOp,
        d: Reg,
        s: Reg,
    },
    /// `d = d op imm`.
    AluImm {
        op: AluOp,
        d: Reg,
        imm: i32,
    },
    /// `d = -d`.
    Neg {
        d: Reg,
    },
    /// `d = d op cl`: the amount is `rcx`'s low 6 bits.
    ShiftCl {
        op: ShiftOp,
        d: Reg,
    },
    /// `d = d op amount`, `amount < 64`.
    ShiftImm {
        op: ShiftOp,
        d: Reg,
        amount: u8,
    },
    /// `d` = the low `from` bits of `s` (8, 16, or 32), sign- or zero-extended to 64 bits.
    Ext {
        signed: bool,
        from: u8,
        d: Reg,
        s: Reg,
    },
    /// The flags of `a - b`.
    Cmp {
        a: Reg,
        b: Reg,
    },
    /// The flags of `a - imm`.
    CmpImm {
        a: Reg,
        imm: i32,
    },
    /// The flags of `a & imm`.
    TestImm {
        a: Reg,
        imm: i32,
    },
    /// `d = cond ? 1 : 0` (`setcc` and `movzbl`).
    Setcc {
        c: Cond,
        d: Reg,
    },
    /// `d = cond ? s : d`.
    Cmov {
        c: Cond,
        d: Reg,
        s: Reg,
    },
    /// `rdx:rax = sign-extension of rax` (`cqto`).
    Cqo,
    /// `rax, rdx = rdx:rax / s, rdx:rax rem s` (`idivq`, or `divq` unsigned).
    Div {
        signed: bool,
        s: Reg,
    },
    /// `rdx:rax = rax * s`, unsigned (`mulq`): `CF` and `OF` say whether `rdx` is nonzero.
    MulWide {
        s: Reg,
    },
    /// `d` = the `size` bytes (1, 2, 4, 8) at `base + off`, zero-extended.
    Load {
        size: u8,
        d: Reg,
        base: Reg,
        off: i32,
    },
    /// The low `size` bytes of `s` to `base + off`.
    Store {
        size: u8,
        s: Reg,
        base: Reg,
        off: i32,
    },
    /// `d = base + off` (`leaq`; the flags are kept).
    Lea {
        d: Reg,
        base: Reg,
        off: i32,
    },
    /// `d` = a global's address.
    LeaGlobal {
        d: Reg,
        global: u32,
    },
    /// `d` = a function's address (an external function's from the GOT).
    LeaFunc {
        d: Reg,
        func: u32,
    },
    /// A direct call (of a function that isn't variadic: those are called through their
    /// address, with `al` set).
    Call {
        func: u32,
    },
    /// A call through `s`; `sig` indexes [`MFunc::sigs`].
    CallInd {
        s: Reg,
        sig: u32,
    },
    /// A call of the C library.
    CallRt(Runtime),
    Jmp {
        t: u32,
    },
    /// To `t` if the condition holds, else to `f`.
    Jcc {
        c: Cond,
        t: u32,
        f: u32,
    },
    /// The epilogue and `ret`.
    Ret,
    /// `__fir_trap(reason, line, col)`, which doesn't return.
    Trap(TrapReason),
    /// `s` becomes the pending exception in `__fir_exn` (decision: Exceptions at run time).
    ExnSet {
        s: Reg,
    },
    /// `d` gets the pending exception, which stops being pending.
    ExnTake {
        d: Reg,
    },
    /// The flags of comparing `__fir_exn`'s flag with 0: `ne` while an exception is pending.
    ExnTest,
}

impl Inst {
    /// Whether the instruction ends a block.
    pub fn is_terminator(self) -> bool {
        matches!(
            self,
            Inst::Jmp { .. } | Inst::Jcc { .. } | Inst::Ret | Inst::Trap(_)
        )
    }

    /// Whether the instruction is a call, which clobbers [`CALLER_SAVED`].
    pub fn is_call(self) -> bool {
        matches!(
            self,
            Inst::Call { .. } | Inst::CallInd { .. } | Inst::CallRt(_)
        )
    }

    /// The registers the instruction writes and reads, apart from what a call does under the
    /// calling convention (its argument and result registers and [`CALLER_SAVED`]; see
    /// `super::regalloc::effects`).
    pub fn regs(self, defs: &mut Vec<Reg>, uses: &mut Vec<Reg>) {
        defs.clear();
        uses.clear();
        match self {
            Inst::Mov { d, s } | Inst::Ext { d, s, .. } => {
                defs.push(d);
                uses.push(s);
            }
            Inst::MovImm { d, .. } | Inst::Setcc { d, .. } => defs.push(d),
            Inst::Alu { d, s, .. } | Inst::Cmov { d, s, .. } => {
                defs.push(d);
                uses.extend([d, s]);
            }
            Inst::AluImm { d, .. } | Inst::Neg { d } | Inst::ShiftImm { d, .. } => {
                defs.push(d);
                uses.push(d);
            }
            Inst::ShiftCl { d, .. } => {
                defs.push(d);
                uses.extend([d, RCX]);
            }
            Inst::Cmp { a, b } => uses.extend([a, b]),
            Inst::CmpImm { a, .. } | Inst::TestImm { a, .. } => uses.push(a),
            Inst::Cqo => {
                defs.push(RDX);
                uses.push(RAX);
            }
            Inst::Div { s, .. } => {
                defs.extend([RAX, RDX]);
                uses.extend([RAX, RDX, s]);
            }
            Inst::MulWide { s } => {
                defs.extend([RAX, RDX]);
                uses.extend([RAX, s]);
            }
            Inst::Load { d, base, .. } | Inst::Lea { d, base, .. } => {
                defs.push(d);
                uses.push(base);
            }
            Inst::Store { s, base, .. } => uses.extend([s, base]),
            Inst::LeaGlobal { d, .. } | Inst::LeaFunc { d, .. } => defs.push(d),
            Inst::CallInd { s, .. } | Inst::ExnSet { s } => uses.push(s),
            Inst::ExnTake { d } => defs.push(d),
            Inst::ExnTest
            | Inst::Call { .. }
            | Inst::CallRt(_)
            | Inst::Jmp { .. }
            | Inst::Jcc { .. }
            | Inst::Ret
            | Inst::Trap(_) => {}
        }
    }

    /// The instruction with every register renamed by `f(r, is_def)`. A register both read and
    /// written (a two-address destination) is renamed once, as a def.
    pub fn map_regs(self, mut f: impl FnMut(Reg, bool) -> Reg) -> Inst {
        match self {
            Inst::Mov { d, s } => Inst::Mov {
                s: f(s, false),
                d: f(d, true),
            },
            Inst::MovImm { d, imm } => Inst::MovImm { d: f(d, true), imm },
            Inst::Alu { op, d, s } => Inst::Alu {
                op,
                s: f(s, false),
                d: f(d, true),
            },
            Inst::AluImm { op, d, imm } => Inst::AluImm {
                op,
                d: f(d, true),
                imm,
            },
            Inst::Neg { d } => Inst::Neg { d: f(d, true) },
            Inst::ShiftCl { op, d } => Inst::ShiftCl { op, d: f(d, true) },
            Inst::ShiftImm { op, d, amount } => Inst::ShiftImm {
                op,
                d: f(d, true),
                amount,
            },
            Inst::Ext { signed, from, d, s } => Inst::Ext {
                signed,
                from,
                s: f(s, false),
                d: f(d, true),
            },
            Inst::Cmp { a, b } => Inst::Cmp {
                a: f(a, false),
                b: f(b, false),
            },
            Inst::CmpImm { a, imm } => Inst::CmpImm {
                a: f(a, false),
                imm,
            },
            Inst::TestImm { a, imm } => Inst::TestImm {
                a: f(a, false),
                imm,
            },
            Inst::Setcc { c, d } => Inst::Setcc { c, d: f(d, true) },
            Inst::Cmov { c, d, s } => Inst::Cmov {
                c,
                s: f(s, false),
                d: f(d, true),
            },
            Inst::Div { signed, s } => Inst::Div {
                signed,
                s: f(s, false),
            },
            Inst::MulWide { s } => Inst::MulWide { s: f(s, false) },
            Inst::Load { size, d, base, off } => Inst::Load {
                size,
                base: f(base, false),
                d: f(d, true),
                off,
            },
            Inst::Store { size, s, base, off } => Inst::Store {
                size,
                s: f(s, false),
                base: f(base, false),
                off,
            },
            Inst::Lea { d, base, off } => Inst::Lea {
                base: f(base, false),
                d: f(d, true),
                off,
            },
            Inst::LeaGlobal { d, global } => Inst::LeaGlobal {
                d: f(d, true),
                global,
            },
            Inst::LeaFunc { d, func } => Inst::LeaFunc {
                d: f(d, true),
                func,
            },
            Inst::CallInd { s, sig } => Inst::CallInd {
                s: f(s, false),
                sig,
            },
            Inst::ExnSet { s } => Inst::ExnSet { s: f(s, false) },
            Inst::ExnTake { d } => Inst::ExnTake { d: f(d, true) },
            i @ (Inst::Cqo
            | Inst::ExnTest
            | Inst::Call { .. }
            | Inst::CallRt(_)
            | Inst::Jmp { .. }
            | Inst::Jcc { .. }
            | Inst::Ret
            | Inst::Trap(_)) => i,
        }
    }

    /// The blocks the instruction may jump to.
    pub fn targets(self) -> impl Iterator<Item = u32> {
        let (a, b) = match self {
            Inst::Jmp { t } => (Some(t), None),
            Inst::Jcc { t, f, .. } => (Some(t), Some(f)),
            _ => (None, None),
        };
        a.into_iter().chain(b)
    }
}

/// The registers a call reads and writes under the calling convention.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CallShape {
    /// The argument registers, in order (a results area's address first, in `rdi`).
    pub args: Vec<Reg>,
    /// The result registers.
    pub rets: Vec<Reg>,
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
    pub sig_shapes: Vec<CallShape>,
    pub frame: Frame,
}

/// What the prologue and epilogue need to know about a function's stack frame.
///
/// ```text
///   rbp + 16 …   stack arguments
///   rbp + 8      return address
///   rbp          saved rbp
///   rbp - 8 …    saved callee-saved registers
///   …            padding, then (realigned when a local needs more than 16 bytes):
///   rsp + outgoing + locals …   spill slots
///   rsp + outgoing …            locals (`mem.stack` slots)
///   rsp …                       outgoing stack arguments
/// ```
#[derive(Clone, Copy, Debug, Default)]
pub struct Frame {
    /// The size of the outgoing-argument area at the bottom of the frame.
    pub outgoing: u32,
    /// The size of the locals, right above it.
    pub locals: u32,
    /// The largest alignment a local needs (at least 16).
    pub align: u32,
    /// The spill slots, 8 bytes each, right above the locals (set by the allocator).
    pub spills: u32,
    /// The callee-saved registers the code uses, by hardware number (set by the allocator).
    pub saved: u16,
}

/// The largest frame the backend lays out (locals, spills, and outgoing arguments): its
/// offsets from `rsp` must fit a signed 32-bit displacement with room to spare.
pub const FRAME_LIMIT: u64 = 1 << 30;

impl Frame {
    /// The callee-saved registers to save, in order.
    pub fn saved_regs(&self) -> impl Iterator<Item = u8> + '_ {
        CALLEE_SAVED
            .iter()
            .copied()
            .filter(|&r| self.saved & (1 << r) != 0)
    }

    /// Where the spill slots start above `rsp`.
    pub fn spill_base(&self) -> u32 {
        self.outgoing + self.locals
    }

    /// How far below the saved registers `rsp` goes: the spills, locals, and outgoing
    /// arguments, rounded so that `rsp` is 16-byte aligned (entry leaves it 8 off, the saved
    /// `rbp` makes it aligned, and each saved register moves it by 8).
    pub fn size(&self) -> u32 {
        let body = self.outgoing + self.locals + 8 * self.spills;
        let pushed = 8 * self.saved_regs().count() as u32;
        (body + pushed).div_ceil(16) * 16 - pushed
    }
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

/// A module's machine code.
#[derive(Clone, Debug, Default)]
pub struct MModule {
    pub funcs: Vec<MFunc>,
}
