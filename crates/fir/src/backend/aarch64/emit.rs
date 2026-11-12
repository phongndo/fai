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
use crate::types::Shape;

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
}

impl Default for Options {
    fn default() -> Options {
        Options {
            os: Os::host(),
            prefix: String::new(),
            extern_prefix: String::new(),
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
    }
}

struct Emitter<'a> {
    m: &'a Module,
    o: &'a Options,
    out: String,
}

/// A symbol as the assembler writes it: quoted unless it is a plain identifier.
fn quote(s: &str) -> String {
    let plain = s
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && s.chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '$');
    if plain {
        s.to_owned()
    } else {
        format!("\"{s}\"")
    }
}

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
        self.linef(format_args!("{op}{stem} {}, {addr}", reg(r, sf)));
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

    fn func(&mut self, f: &MFunc) {
        let func = &self.m.funcs[f.index as usize];
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
                self.inst(f, i, next);
            }
        }
        if self.o.os == Os::Linux {
            self.linef(format_args!(".size {s}, .-{s}"));
        }
    }

    /// A global's bytes, and the symbols stored in it (offset, symbol).
    fn image(&self, t: Ty, init: Init, out: &mut Vec<u8>, relocs: &mut Vec<(usize, String)>) {
        let gs = &self.m.globals;
        let sp = &self.m.space;
        let size = gs.types.size(sp, t) as usize;
        let start = out.len();
        match (init, t) {
            (Init::Zero, _) | (Init::Null, _) => out.resize(start + size, 0),
            (Init::Int(i), Ty::Int(w) | Ty::Byte(w)) => {
                let n = gs.int(i);
                let m = num_bigint::BigInt::from(1) << w;
                let v = ((n % &m) + &m) % &m;
                let (_, mut bytes) = v.to_bytes_le();
                bytes.resize((w / 8) as usize, 0);
                out.extend_from_slice(&bytes);
            }
            (Init::Sym(r), Ty::Ptr) => {
                let name = gs.text(r);
                let s = if gs_has(gs, name) || self.m.funcs.iter().any(|f| f.name == name) {
                    self.sym(name, true)
                } else {
                    self.sym(&format!("{}{name}", self.o.extern_prefix), false)
                };
                relocs.push((start, s));
                out.resize(start + 8, 0);
            }
            (Init::Bytes(r), _) => out.extend_from_slice(gs.bytes(r)),
            (Init::List(r), Ty::Agg(id)) => {
                out.resize(start + size, 0);
                let items = gs.items(r);
                let mut part = Vec::new();
                let mut put = |off: usize,
                               ty: Ty,
                               item: Init,
                               out: &mut Vec<u8>,
                               relocs: &mut Vec<(usize, String)>| {
                    part.clear();
                    let mut rs = Vec::new();
                    self.image(ty, item, &mut part, &mut rs);
                    let off = start + off;
                    let n = part.len().min(out.len().saturating_sub(off));
                    out[off..off + n].copy_from_slice(&part[..n]);
                    relocs.extend(rs.into_iter().map(|(o, s)| (o + off, s)));
                };
                match gs.types.shape(id) {
                    Shape::Struct(p, fs) => {
                        let (offs, _, _) = gs.types.place(sp, p, fs);
                        for ((&f, &item), off) in fs.iter().zip(items).zip(offs) {
                            put(off as usize, f, item, out, relocs);
                        }
                    }
                    Shape::Array(n, e) => {
                        let stride = gs.types.stride(sp, e) as usize;
                        for (i, &item) in items.iter().take(n as usize).enumerate() {
                            put(i * stride, e, item, out, relocs);
                        }
                    }
                    Shape::Func(..) | Shape::Union(_) => {}
                }
            }
            _ => out.resize(start + size, 0),
        }
    }

    fn globals(&mut self) {
        let gs = &self.m.globals;
        for g in 0..gs.len() {
            let t = gs.ty(g);
            let align = gs.types.align(&self.m.space, t).max(u64::from(gs.align(g)));
            let mut bytes = Vec::new();
            let mut relocs = Vec::new();
            self.image(t, gs.init(g), &mut bytes, &mut relocs);
            if bytes.is_empty() {
                bytes.push(0);
            }
            let section = match (self.o.os, gs.is_const(g), relocs.is_empty()) {
                (Os::Linux, true, true) => ".section .rodata",
                (Os::Linux, true, false) => ".section .data.rel.ro,\"aw\"",
                (Os::Linux, false, _) => ".data",
                (Os::Darwin, true, true) => ".section __TEXT,__const",
                (Os::Darwin, true, false) => ".section __DATA,__const",
                (Os::Darwin, false, _) => ".data",
            };
            let s = self.sym(gs.name(g), true);
            self.out.push('\n');
            self.line(section);
            self.linef(format_args!(".globl {s}"));
            self.linef(format_args!(".p2align {}", align.trailing_zeros()));
            if self.o.os == Os::Linux {
                self.linef(format_args!(".type {s}, %object"));
                self.linef(format_args!(".size {s}, {}", bytes.len()));
            }
            let _ = writeln!(self.out, "{s}:");
            let mut i = 0;
            let mut ri = relocs.iter().peekable();
            while i < bytes.len() {
                if let Some((o, sym)) = ri.peek()
                    && *o == i
                {
                    self.linef(format_args!(".quad {sym}"));
                    i += 8;
                    ri.next();
                    continue;
                }
                let end = relocs
                    .iter()
                    .map(|r| r.0)
                    .find(|&o| o > i)
                    .unwrap_or(bytes.len())
                    .min(i + 16);
                let items: Vec<String> = bytes[i..end].iter().map(|b| b.to_string()).collect();
                self.linef(format_args!(".byte {}", items.join(", ")));
                i = end;
            }
        }
    }
}

fn gs_has(gs: &Globals, name: &str) -> bool {
    (0..gs.len()).any(|g| gs.name(g) == name)
}

/// Assembly for a module whose functions are allocated.
pub fn emit(m: &Module, mm: &MModule, o: &Options) -> String {
    let mut e = Emitter {
        m,
        o,
        out: String::new(),
    };
    e.out
        .push_str("// Generated by fir: AArch64 assembly.\n\t.text\n");
    for f in &mm.funcs {
        e.func(f);
    }
    // The trap handler a program gets unless it defines its own.
    let t = e.sym("__fir_trap", false);
    e.out.push('\n');
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
