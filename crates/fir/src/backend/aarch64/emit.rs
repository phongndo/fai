//! GNU-syntax AArch64 assembly from allocated machine code, for ELF (Linux) or Mach-O (macOS).
//!
//! Each LFIR instruction prints as one instruction, except the pseudo-instructions:
//! `aarch64.adrl` (`adrp` and `add`, or a GOT load for an external function's address),
//! `aarch64.trap.R` (the reason and location in `w0`…`w2`, then `bl __fir_trap`),
//! `aarch64.bl.alloc` (`bl malloc`, or `aligned_alloc` for alignments above 16), and
//! `aarch64.bl.free` (`bl free`), and the exception ops, which address the exception slot
//! `__fir_exn` through `x16` (decision: Exceptions at run time). A branch to the next block is
//! left out. Every output defines a weak `__fir_trap` that executes `brk #1000`; a program (or
//! the test harness) can define its own to report traps, which it receives as
//! `__fir_trap(reason, line, col)` with reason codes `div0` 0, `overflow` 1, `shift` 2, `oom` 3,
//! `bounds` 4, `tag` 5, and line and column `0xffffffff` for no location.
//!
//! **The exception slot.** `__fir_exn` is two 8-byte words, `{ flag, value }`, zero while no
//! exception is pending: in C, `struct { void *flag; void *value; } __fir_exn`. A pending
//! exception has a nonzero flag (the slot's own address) and its value in `value`.
//! `aarch64.exn.set xN` is `adrp`/`add x16` of the slot, `str xN, [x16, #8]`,
//! `str x16, [x16]`; `aarch64.exn.take xD` loads `value` into `xD` and stores `xzr` to the flag;
//! `aarch64.b.exn` loads the flag into `x16` and branches with `cbnz`. An output whose code uses
//! the slot defines it weakly, zeroed; a C program that calls FIR functions that may throw
//! defines or declares it, and after each call checks `flag` (and clears it to catch).

use std::fmt::Write;

use super::mir::{Inst, MFunc, MModule};
use crate::ir::*;

/// The object format and its assembler conventions.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Os {
    /// ELF: Linux.
    Linux,
    /// Mach-O: macOS (symbols get a leading `_`).
    Darwin,
}

impl Os {
    /// The host's, if it is AArch64 or not (the format of the system the binaries run on).
    pub fn host() -> Os {
        if cfg!(target_os = "macos") {
            Os::Darwin
        } else {
            Os::Linux
        }
    }
}

/// How to emit a module.
#[derive(Clone, Debug)]
pub struct Options {
    pub os: Os,
    /// Prepended to the module's own function and global names.
    pub prefix: String,
    /// Prepended to external functions' names (not to the runtime's: `malloc`, `free`,
    /// `aligned_alloc`, `__fir_trap`).
    pub extern_prefix: String,
    /// Write source lines for the assembler's DWARF line table (`fir compile -g`): `.file` for
    /// each function's source file, and before each instruction whose location differs from the
    /// last one's, `.loc FILE LINE COL`, the location its LFIR instruction carries (that of the
    /// FIR op it was selected for). Instructions without one (prologues, epilogues, spill code,
    /// the trap stub), the code of functions without a file, and FIR locations on line 0, get
    /// line 1 of a synthetic file,
    /// [`NO_SOURCE`], so they are never attributed to the op before them (DWARF's own "no
    /// source", line 0, is dropped by GNU as 2.46, which would leave them the previous line;
    /// LLVM's assembler keeps it). So a native address recovers
    /// the `line:col` of the ops it implements (a set: ops share locations), not one op.
    pub debug_lines: bool,
}

impl Default for Options {
    fn default() -> Options {
        Options {
            os: Os::host(),
            prefix: String::new(),
            extern_prefix: String::new(),
            debug_lines: false,
        }
    }
}

pub fn trap_code(r: TrapReason) -> u32 {
    match r {
        TrapReason::Div0 => 0,
        TrapReason::Overflow => 1,
        TrapReason::Shift => 2,
        TrapReason::Oom => 3,
        TrapReason::Bounds => 4,
        TrapReason::Tag => 5,
        TrapReason::Convert => 6,
    }
}

/// The `.file` that instructions without a source location are attributed to, with
/// [`Options::debug_lines`].
pub const NO_SOURCE: &str = "<fir: no source>";

struct Emitter<'a> {
    m: &'a Module,
    o: &'a Options,
    out: String,
    /// With [`Options::debug_lines`]: each source file's `.file` number, and the last `.loc`
    /// written (file, line, col), if any.
    files: Vec<String>,
    at: Option<(usize, u32, u32)>,
}

use crate::backend::data::quote;

const XREGS: [&str; 31] = [
    "x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14",
    "x15", "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27",
    "x28", "x29", "x30",
];
const WREGS: [&str; 31] = [
    "w0", "w1", "w2", "w3", "w4", "w5", "w6", "w7", "w8", "w9", "w10", "w11", "w12", "w13", "w14",
    "w15", "w16", "w17", "w18", "w19", "w20", "w21", "w22", "w23", "w24", "w25", "w26", "w27",
    "w28", "w29", "w30",
];

fn reg(r: Reg, sf: Sf) -> &'static str {
    match (r, sf) {
        (Reg::SP, Sf::X) => "sp",
        (Reg::SP, Sf::W) => "wsp",
        (Reg::XZR, Sf::X) => "xzr",
        (Reg::XZR, Sf::W) => "wzr",
        (r, _) if r.is_virtual() => panic!("virtual register {r} after allocation"),
        (Reg(n), Sf::X) => XREGS[n as usize],
        (Reg(n), Sf::W) => WREGS[n as usize],
    }
}

fn x(r: Reg) -> &'static str {
    reg(r, Sf::X)
}

/// An FP register at a format: `s3` or `d3`.
fn freg(r: Reg, fs: FSize) -> String {
    assert!(r.is_fpr(), "{r} is not an FP register after allocation");
    let c = match fs {
        FSize::S => 's',
        FSize::D => 'd',
    };
    format!("{c}{}", r.fpr_index())
}

/// A register of either class at the size of an `fs` value: `w`/`s` or `x`/`d`.
fn any_reg(r: Reg, fs: FSize) -> String {
    if r.is_fp() {
        freg(r, fs)
    } else {
        reg(r, if fs == FSize::S { Sf::W } else { Sf::X }).to_owned()
    }
}

/// The float an `fmov` immediate encodes, as the assembler reads it (`#1.5`).
fn fmov_imm_text(fs: FSize, imm: u8) -> String {
    let bits = super::machine_imm(fs, imm);
    match fs {
        FSize::S => format!("#{:?}", f32::from_bits(bits as u32)),
        FSize::D => format!("#{:?}", f64::from_bits(bits)),
    }
}

/// A block's label: `.LBB<f>_<b>` (ELF) or `LBB<f>_<b>` (Mach-O).
struct Label(bool, u32, u32);

impl std::fmt::Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}LBB{}_{}",
            if self.0 { "." } else { "" },
            self.1,
            self.2
        )
    }
}

fn alu_name(op: AluOp) -> &'static str {
    match op {
        AluOp::Add => "add",
        AluOp::Adds => "adds",
        AluOp::Sub => "sub",
        AluOp::Subs => "subs",
        AluOp::And => "and",
        AluOp::Ands => "ands",
        AluOp::Orr => "orr",
        AluOp::Eor => "eor",
        AluOp::Bic => "bic",
        AluOp::Lsl => "lsl",
        AluOp::Lsr => "lsr",
        AluOp::Asr => "asr",
        AluOp::Mul => "mul",
        AluOp::Sdiv => "sdiv",
        AluOp::Udiv => "udiv",
        AluOp::Smulh => "smulh",
        AluOp::Umulh => "umulh",
    }
}

impl Emitter<'_> {
    fn line(&mut self, s: &str) {
        self.out.push('\t');
        self.out.push_str(s);
        self.out.push('\n');
    }

    /// A line written straight into the output.
    fn linef(&mut self, a: std::fmt::Arguments<'_>) {
        self.out.push('\t');
        let _ = self.out.write_fmt(a);
        self.out.push('\n');
    }

    /// A symbol: the module's own (with the prefix), or a runtime one as it is; with `_` in
    /// front on Darwin.
    fn sym(&self, name: &str, own: bool) -> String {
        let base = if own {
            format!("{}{name}", self.o.prefix)
        } else {
            name.to_owned()
        };
        match self.o.os {
            Os::Linux => quote(&base),
            Os::Darwin => quote(&format!("_{base}")),
        }
    }

    /// The symbol of callee `f` (an index like the interpreter's) and whether it is external.
    fn func_sym(&self, f: u32) -> (String, bool) {
        let n = self.m.funcs.len();
        match self.m.funcs.get(f as usize) {
            Some(func) => (self.sym(&func.name, true), false),
            None => {
                let name = &self.m.externs[f as usize - n].name;
                (
                    self.sym(&format!("{}{name}", self.o.extern_prefix), false),
                    true,
                )
            }
        }
    }

    fn label(&self, f: u32, b: u32) -> Label {
        Label(self.o.os == Os::Linux, f, b)
    }

    /// `adrp` and `add` of a symbol's address.
    fn adrl(&mut self, d: Reg, s: &str, got: bool) {
        let d = x(d);
        match (self.o.os, got) {
            (Os::Linux, false) => {
                self.linef(format_args!("adrp {d}, {s}"));
                self.linef(format_args!("add {d}, {d}, :lo12:{s}"));
            }
            (Os::Linux, true) => {
                self.linef(format_args!("adrp {d}, :got:{s}"));
                self.linef(format_args!("ldr {d}, [{d}, :got_lo12:{s}]"));
            }
            (Os::Darwin, false) => {
                self.linef(format_args!("adrp {d}, {s}@PAGE"));
                self.linef(format_args!("add {d}, {d}, {s}@PAGEOFF"));
            }
            (Os::Darwin, true) => {
                self.linef(format_args!("adrp {d}, {s}@GOTPAGE"));
                self.linef(format_args!("ldr {d}, [{d}, {s}@GOTPAGEOFF]"));
            }
        }
    }

    /// Put a 32-bit constant in `wN`.
    fn mov32(&mut self, r: u32, v: u32) {
        if v == u32::MAX {
            self.linef(format_args!("movn w{r}, #0"));
            return;
        }
        self.linef(format_args!("movz w{r}, #{}", v & 0xffff));
        if v >> 16 != 0 {
            self.linef(format_args!("movk w{r}, #{}, lsl #16", v >> 16));
        }
    }

    fn mem(&mut self, load: bool, size: MemSize, r: Reg, base: Reg, off: i64) {
        let scaled = off >= 0 && off % i64::from(size.bytes()) == 0;
        let (stem, sf) = match size {
            MemSize::B => ("b", Sf::W),
            MemSize::H => ("h", Sf::W),
            MemSize::W => ("", Sf::W),
            MemSize::X => ("", Sf::X),
        };
        // An FP register's name says the size: `ldr s0`, `str d1`.
        let (stem, name) = if r.is_fp() {
            let c = match size {
                MemSize::B => 'b',
                MemSize::H => 'h',
                MemSize::W => 's',
                MemSize::X => 'd',
            };
            ("", format!("{c}{}", r.fpr_index()))
        } else {
            (stem, reg(r, sf).to_owned())
        };
        let op = match (load, scaled) {
            (true, true) => "ldr",
            (true, false) => "ldur",
            (false, true) => "str",
            (false, false) => "stur",
        };
        let addr = if off == 0 {
            format!("[{}]", x(base))
        } else {
            format!("[{}, #{off}]", x(base))
        };
        self.linef(format_args!("{op}{stem} {name}, {addr}"));
    }

    fn inst(&mut self, f: &MFunc, i: usize, next: Option<u32>) {
        let fi = f.index;
        match f.insts[i] {
            Inst::Alu { op, sf, d, n, m } => {
                self.linef(format_args!(
                    "{} {}, {}, {}",
                    alu_name(op),
                    reg(d, sf),
                    reg(n, sf),
                    reg(m, sf)
                ));
            }
            Inst::AluImm { op, sf, d, n, imm } => {
                let (name, logical) = match op {
                    AluImmOp::Add => ("add", false),
                    AluImmOp::Adds => ("adds", false),
                    AluImmOp::Sub => ("sub", false),
                    AluImmOp::Subs => ("subs", false),
                    AluImmOp::And => ("and", true),
                    AluImmOp::Ands => ("ands", true),
                    AluImmOp::Orr => ("orr", true),
                    AluImmOp::Eor => ("eor", true),
                };
                let imm = if logical {
                    let v = imm as u64;
                    let v = if sf == Sf::W { v & 0xffff_ffff } else { v };
                    format!("#{v:#x}")
                } else if imm >= 4096 {
                    format!("#{}, lsl #12", imm >> 12)
                } else {
                    format!("#{imm}")
                };
                self.linef(format_args!("{name} {}, {}, {imm}", reg(d, sf), reg(n, sf)));
            }
            Inst::ShiftImm {
                op,
                sf,
                d,
                n,
                amount,
            } => {
                let name = match op {
                    ShiftImmOp::Lsl => "lsl",
                    ShiftImmOp::Lsr => "lsr",
                    ShiftImmOp::Asr => "asr",
                };
                self.linef(format_args!(
                    "{name} {}, {}, #{amount}",
                    reg(d, sf),
                    reg(n, sf)
                ));
            }
            Inst::Ext {
                signed,
                sf,
                d,
                n,
                width,
            } => {
                let name = if signed { "sbfx" } else { "ubfx" };
                self.linef(format_args!(
                    "{name} {}, {}, #0, #{width}",
                    reg(d, sf),
                    reg(n, sf)
                ));
            }
            Inst::Mov { sf, d, n } => {
                if d != n {
                    self.linef(format_args!("mov {}, {}", reg(d, sf), reg(n, sf)));
                }
            }
            Inst::MovWide { op, sf, d, imm, hw } => {
                let name = match op {
                    MovOp::Movz => "movz",
                    MovOp::Movn => "movn",
                    MovOp::Movk => "movk",
                };
                self.linef(format_args!("{name} {}, #{imm}, lsl #{hw}", reg(d, sf)));
            }
            Inst::Csel { op, c, sf, d, n, m } => {
                let name = match op {
                    CselOp::Csel => "csel",
                    CselOp::Csinc => "csinc",
                    CselOp::Csinv => "csinv",
                    CselOp::Csneg => "csneg",
                };
                self.linef(format_args!(
                    "{name} {}, {}, {}, {}",
                    reg(d, sf),
                    reg(n, sf),
                    reg(m, sf),
                    c.name()
                ));
            }
            Inst::Ldr { size, d, base, off } => self.mem(true, size, d, base, off),
            Inst::Str { size, s, base, off } => self.mem(false, size, s, base, off),
            Inst::Adrl { d, global } => {
                let s = self.sym(self.m.globals.name(global as usize), true);
                self.adrl(d, &s, false);
            }
            Inst::AdrlFunc { d, func } => {
                let (s, ext) = self.func_sym(func);
                self.adrl(d, &s, ext);
            }
            Inst::B { t } => {
                if Some(t) != next {
                    self.linef(format_args!("b {}", self.label(fi, t)));
                }
            }
            Inst::BCond { c, t, f: e } => {
                if Some(e) == next {
                    self.linef(format_args!("b.{} {}", c.name(), self.label(fi, t)));
                } else if Some(t) == next {
                    self.linef(format_args!(
                        "b.{} {}",
                        c.invert().name(),
                        self.label(fi, e)
                    ));
                } else {
                    self.linef(format_args!("b.{} {}", c.name(), self.label(fi, t)));
                    self.linef(format_args!("b {}", self.label(fi, e)));
                }
            }
            Inst::Ret => self.line("ret"),
            Inst::Trap(r) => {
                let (line, col) = f.locs[i].map_or((u32::MAX, u32::MAX), |l| (l.line, l.col));
                self.mov32(0, trap_code(r));
                self.mov32(1, line);
                self.mov32(2, col);
                let s = self.sym("__fir_trap", false);
                self.linef(format_args!("bl {s}"));
            }
            Inst::Bl { func } => {
                let (s, _) = self.func_sym(func);
                self.linef(format_args!("bl {s}"));
            }
            Inst::Blr { n, .. } => self.linef(format_args!("blr {}", x(n))),
            Inst::BlAlloc { align, .. } => {
                if align <= 16 {
                    let s = self.sym("malloc", false);
                    self.linef(format_args!("bl {s}"));
                } else {
                    // aligned_alloc(align, size rounded up to a multiple of align)
                    let a = u64::from(align);
                    if a - 1 < 4096 {
                        self.linef(format_args!("add x0, x0, #{}", a - 1));
                    } else {
                        self.linef(format_args!("movz x1, #{}, lsl #{}", (a - 1) & 0xffff, 0));
                        if (a - 1) >> 16 != 0 {
                            self.linef(format_args!(
                                "movk x1, #{}, lsl #16",
                                ((a - 1) >> 16) & 0xffff
                            ));
                        }
                        self.line("add x0, x0, x1");
                    }
                    self.linef(format_args!("and x0, x0, #{:#x}", (!(a - 1))));
                    self.line("mov x1, x0");
                    self.mov32(0, align);
                    let s = self.sym("aligned_alloc", false);
                    self.linef(format_args!("bl {s}"));
                }
            }
            Inst::BlFree { .. } => {
                let s = self.sym("free", false);
                self.linef(format_args!("bl {s}"));
            }
            Inst::ExnSet { n } => {
                debug_assert!(n != Reg::x(16), "x16 addresses the exception slot");
                let s = self.sym("__fir_exn", false);
                self.adrl(Reg::x(16), &s, false);
                self.linef(format_args!("str {}, [x16, #8]", x(n)));
                self.line("str x16, [x16]");
            }
            Inst::ExnTake { d } => {
                debug_assert!(d != Reg::x(16), "x16 addresses the exception slot");
                let s = self.sym("__fir_exn", false);
                self.adrl(Reg::x(16), &s, false);
                self.linef(format_args!("ldr {}, [x16, #8]", x(d)));
                self.line("str xzr, [x16]");
            }
            Inst::Falu { op, fs, d, n, m } => {
                let name = match op {
                    FAluOp::Fadd => "fadd",
                    FAluOp::Fsub => "fsub",
                    FAluOp::Fmul => "fmul",
                    FAluOp::Fdiv => "fdiv",
                };
                self.linef(format_args!(
                    "{name} {}, {}, {}",
                    freg(d, fs),
                    freg(n, fs),
                    freg(m, fs)
                ));
            }
            Inst::Funary { op, fs, d, n } => {
                let name = match op {
                    FUnaryOp::Fmov => {
                        if d != n {
                            self.linef(format_args!("fmov {}, {}", any_reg(d, fs), any_reg(n, fs)));
                        }
                        return;
                    }
                    FUnaryOp::Fabs => "fabs",
                    FUnaryOp::Fneg => "fneg",
                    FUnaryOp::Fsqrt => "fsqrt",
                };
                self.linef(format_args!("{name} {}, {}", freg(d, fs), freg(n, fs)));
            }
            Inst::Fmadd { fs, d, n, m } => {
                let d = freg(d, fs);
                self.linef(format_args!(
                    "fmadd {d}, {}, {}, {d}",
                    freg(n, fs),
                    freg(m, fs)
                ));
            }
            Inst::FmovImm { fs, d, imm } => {
                self.linef(format_args!(
                    "fmov {}, {}",
                    freg(d, fs),
                    fmov_imm_text(fs, imm)
                ));
            }
            Inst::Fcmp { fs, n, m } => {
                self.linef(format_args!("fcmp {}, {}", freg(n, fs), freg(m, fs)));
            }
            Inst::Fcsel { c, fs, d, n, m } => {
                self.linef(format_args!(
                    "fcsel {}, {}, {}, {}",
                    freg(d, fs),
                    freg(n, fs),
                    freg(m, fs),
                    c.name()
                ));
            }
            Inst::Fcvt { dst, src, d, n } => {
                self.linef(format_args!("fcvt {}, {}", freg(d, dst), freg(n, src)));
            }
            Inst::Cvtf {
                signed,
                fs,
                sf,
                d,
                n,
            } => {
                let name = if signed { "scvtf" } else { "ucvtf" };
                self.linef(format_args!("{name} {}, {}", freg(d, fs), reg(n, sf)));
            }
            Inst::Fcvtz {
                signed,
                sf,
                fs,
                d,
                n,
            } => {
                let name = if signed { "fcvtzs" } else { "fcvtzu" };
                self.linef(format_args!("{name} {}, {}", reg(d, sf), freg(n, fs)));
            }
            Inst::BExn { t, f: e } => {
                let s = self.sym("__fir_exn", false);
                match self.o.os {
                    Os::Linux => {
                        self.linef(format_args!("adrp x16, {s}"));
                        self.linef(format_args!("ldr x16, [x16, :lo12:{s}]"));
                    }
                    Os::Darwin => {
                        self.linef(format_args!("adrp x16, {s}@PAGE"));
                        self.linef(format_args!("ldr x16, [x16, {s}@PAGEOFF]"));
                    }
                }
                if Some(t) == next {
                    self.linef(format_args!("cbz x16, {}", self.label(fi, e)));
                } else {
                    self.linef(format_args!("cbnz x16, {}", self.label(fi, t)));
                    if Some(e) != next {
                        self.linef(format_args!("b {}", self.label(fi, e)));
                    }
                }
            }
        }
    }

    /// With line info on: a `.loc` for the next instruction, at `loc` in this function's file
    /// (or [`NO_SOURCE`]'s line 1 without one), if it differs from the last.
    fn loc(&mut self, file: Option<&str>, loc: Option<crate::ir::Loc>) {
        if !self.o.debug_lines || self.files.is_empty() {
            return;
        }
        // The last `.file` is the synthetic one for code without a source line.
        let none = (self.files.len(), 1, 0);
        let want = match (
            file.and_then(|f| self.files.iter().position(|g| g == f)),
            loc,
        ) {
            // Line 0 is DWARF's "no source", which GNU as drops: it gets the synthetic file too.
            (Some(i), Some(l)) if i + 1 < self.files.len() && l.line != 0 => (i + 1, l.line, l.col),
            _ => none,
        };
        if self.at != Some(want) {
            self.linef(format_args!(".loc {} {} {}", want.0, want.1, want.2));
            self.at = Some(want);
        }
    }

    fn func(&mut self, f: &MFunc) {
        let func = &self.m.funcs[f.index as usize];
        let file = func.file.clone();
        let s = self.sym(&func.name, true);
        self.out.push('\n');
        self.linef(format_args!(".globl {s}"));
        self.line(".p2align 2");
        if self.o.os == Os::Linux {
            self.linef(format_args!(".type {s}, %function"));
        }
        let _ = writeln!(self.out, "{s}:");
        for b in 0..f.blocks.len() {
            if b > 0 {
                let l = self.label(f.index, b as u32);
                let _ = writeln!(self.out, "{l}:");
            }
            let r = f.block_range(b);
            let next = (b + 1 < f.blocks.len()).then_some(b as u32 + 1);
            for i in r {
                self.loc(file.as_deref(), f.locs[i]);
                self.inst(f, i, next);
            }
        }
        if self.o.os == Os::Linux {
            self.linef(format_args!(".size {s}, .-{s}"));
        }
    }

    fn globals(&mut self) {
        let darwin = self.o.os == Os::Darwin;
        let text = crate::backend::data::globals(
            self.m,
            &|name, own| self.sym(name, own),
            &self.o.extern_prefix,
            darwin,
        );
        self.out.push_str(&text);
    }
}

/// Assembly for a module whose functions are allocated.
pub fn emit(m: &Module, mm: &MModule, o: &Options) -> String {
    let mut e = Emitter {
        m,
        o,
        out: String::new(),
        files: Vec::new(),
        at: None,
    };
    e.out
        .push_str("// Generated by fir: AArch64 assembly.\n\t.text\n");
    if o.debug_lines {
        for f in &mm.funcs {
            if let Some(file) = &m.funcs[f.index as usize].file
                && !e.files.contains(file)
            {
                e.files.push(file.clone());
            }
        }
        e.files.push(NO_SOURCE.to_owned());
        for (i, file) in e.files.clone().iter().enumerate() {
            let text: String = file
                .chars()
                .flat_map(|c| match c {
                    '"' | '\\' => vec!['\\', c],
                    '\n' => vec!['\\', 'n'],
                    c => vec![c],
                })
                .collect();
            e.linef(format_args!(".file {} \"{text}\"", i + 1));
        }
    }
    for f in &mm.funcs {
        e.func(f);
    }
    // The trap handler a program gets unless it defines its own.
    let t = e.sym("__fir_trap", false);
    e.out.push('\n');
    e.loc(None, None);
    match o.os {
        Os::Linux => {
            e.line(&format!(".weak {t}"));
            e.line(".p2align 2");
            e.line(&format!(".type {t}, %function"));
        }
        Os::Darwin => {
            e.line(&format!(".globl {t}"));
            e.line(&format!(".weak_definition {t}"));
            e.line(".p2align 2");
        }
    }
    let _ = writeln!(e.out, "{t}:");
    e.line("brk #1000");
    // The exception slot, if the code uses it.
    let uses_exn = mm.funcs.iter().any(|f| {
        f.insts.iter().any(|i| {
            matches!(
                i,
                Inst::ExnSet { .. } | Inst::ExnTake { .. } | Inst::BExn { .. }
            )
        })
    });
    if uses_exn {
        let s = e.sym("__fir_exn", false);
        e.out.push('\n');
        match o.os {
            Os::Linux => {
                e.line(".data");
                e.line(&format!(".weak {s}"));
                e.line(".p2align 3");
                e.line(&format!(".type {s}, %object"));
                e.line(&format!(".size {s}, 16"));
            }
            Os::Darwin => {
                e.line(".data");
                e.line(&format!(".globl {s}"));
                e.line(&format!(".weak_definition {s}"));
                e.line(".p2align 3");
            }
        }
        let _ = writeln!(e.out, "{s}:");
        e.line(".quad 0, 0");
    }
    e.globals();
    if o.os == Os::Linux {
        e.out
            .push_str("\n\t.section .note.GNU-stack,\"\",%progbits\n");
    }
    e.out
}
