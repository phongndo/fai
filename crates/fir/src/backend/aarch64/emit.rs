//! GNU-syntax AArch64 assembly from allocated machine code, for ELF (Linux) or Mach-O (macOS).
//!
//! Each LFIR instruction prints as one instruction, except the pseudo-instructions:
//! `aarch64.adrl` (`adrp` and `add`, or a GOT load for an external function's address),
//! `aarch64.trap.R` (the reason and location in `w0`…`w2`, then `bl __fir_trap`),
//! `aarch64.bl.alloc` (`bl malloc`, or `aligned_alloc` for alignments above 16), and
//! `aarch64.bl.free` (`bl free`). A branch to the next block is left out. Every output defines a
//! weak `__fir_trap` that executes `brk #1000`; a program (or the test harness) can define its
//! own to report traps, which it receives as `__fir_trap(reason, line, col)` with reason codes
//! `div0` 0, `overflow` 1, `shift` 2, `oom` 3, and line and column `0xffffffff` for no location.

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
    /// Prepended to the module's own function and global names (not to external functions).
    pub prefix: String,
}

impl Default for Options {
    fn default() -> Options {
        Options {
            os: Os::host(),
            prefix: String::new(),
        }
    }
}

pub fn trap_code(r: TrapReason) -> u32 {
    match r {
        TrapReason::Div0 => 0,
        TrapReason::Overflow => 1,
        TrapReason::Shift => 2,
        TrapReason::Oom => 3,
    }
}

struct Emitter<'a> {
    m: &'a Module,
    mm: &'a MModule,
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

fn reg(r: Reg, sf: Sf) -> String {
    match (r, sf) {
        (Reg::SP, Sf::X) => "sp".to_owned(),
        (Reg::SP, Sf::W) => "wsp".to_owned(),
        (Reg::XZR, Sf::X) => "xzr".to_owned(),
        (Reg::XZR, Sf::W) => "wzr".to_owned(),
        (r, _) if r.is_virtual() => panic!("virtual register {r} after allocation"),
        (Reg(n), Sf::X) => format!("x{n}"),
        (Reg(n), Sf::W) => format!("w{n}"),
    }
}

fn x(r: Reg) -> String {
    reg(r, Sf::X)
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

    /// A module symbol: a function or global of the module, with the prefix, or an external
    /// function as it is; with `_` in front on Darwin.
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
            None => (self.sym(&self.m.externs[f as usize - n].name, false), true),
        }
    }

    fn label(&self, f: u32, b: u32) -> String {
        match self.o.os {
            Os::Linux => format!(".LBB{f}_{b}"),
            Os::Darwin => format!("LBB{f}_{b}"),
        }
    }

    /// `adrp` and `add` of a symbol's address.
    fn adrl(&mut self, d: Reg, s: &str, got: bool) {
        let d = x(d);
        match (self.o.os, got) {
            (Os::Linux, false) => {
                self.line(&format!("adrp {d}, {s}"));
                self.line(&format!("add {d}, {d}, :lo12:{s}"));
            }
            (Os::Linux, true) => {
                self.line(&format!("adrp {d}, :got:{s}"));
                self.line(&format!("ldr {d}, [{d}, :got_lo12:{s}]"));
            }
            (Os::Darwin, false) => {
                self.line(&format!("adrp {d}, {s}@PAGE"));
                self.line(&format!("add {d}, {d}, {s}@PAGEOFF"));
            }
            (Os::Darwin, true) => {
                self.line(&format!("adrp {d}, {s}@GOTPAGE"));
                self.line(&format!("ldr {d}, [{d}, {s}@GOTPAGEOFF]"));
            }
        }
    }

    /// Put a 32-bit constant in `wN`.
    fn mov32(&mut self, r: u32, v: u32) {
        if v == u32::MAX {
            self.line(&format!("movn w{r}, #0"));
            return;
        }
        self.line(&format!("movz w{r}, #{}", v & 0xffff));
        if v >> 16 != 0 {
            self.line(&format!("movk w{r}, #{}, lsl #16", v >> 16));
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
        self.line(&format!("{op}{stem} {}, {addr}", reg(r, sf)));
    }

    fn inst(&mut self, f: &MFunc, i: usize, next: Option<u32>) {
        let fi = f.index;
        match f.insts[i] {
            Inst::Alu { op, sf, d, n, m } => {
                self.line(&format!(
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
                self.line(&format!("{name} {}, {}, {imm}", reg(d, sf), reg(n, sf)));
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
                self.line(&format!("{name} {}, {}, #{amount}", reg(d, sf), reg(n, sf)));
            }
            Inst::Ext {
                signed,
                sf,
                d,
                n,
                width,
            } => {
                let name = if signed { "sbfx" } else { "ubfx" };
                self.line(&format!(
                    "{name} {}, {}, #0, #{width}",
                    reg(d, sf),
                    reg(n, sf)
                ));
            }
            Inst::Mov { sf, d, n } => {
                if d != n {
                    self.line(&format!("mov {}, {}", reg(d, sf), reg(n, sf)));
                }
            }
            Inst::MovWide { op, sf, d, imm, hw } => {
                let name = match op {
                    MovOp::Movz => "movz",
                    MovOp::Movn => "movn",
                    MovOp::Movk => "movk",
                };
                self.line(&format!("{name} {}, #{imm}, lsl #{hw}", reg(d, sf)));
            }
            Inst::Csel { op, c, sf, d, n, m } => {
                let name = match op {
                    CselOp::Csel => "csel",
                    CselOp::Csinc => "csinc",
                    CselOp::Csinv => "csinv",
                    CselOp::Csneg => "csneg",
                };
                self.line(&format!(
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
                    self.line(&format!("b {}", self.label(fi, t)));
                }
            }
            Inst::BCond { c, t, f: e } => {
                if Some(e) == next {
                    self.line(&format!("b.{} {}", c.name(), self.label(fi, t)));
                } else if Some(t) == next {
                    self.line(&format!("b.{} {}", c.invert().name(), self.label(fi, e)));
                } else {
                    self.line(&format!("b.{} {}", c.name(), self.label(fi, t)));
                    self.line(&format!("b {}", self.label(fi, e)));
                }
            }
            Inst::Ret => self.line("ret"),
            Inst::Trap(r) => {
                let (line, col) = f.locs[i].map_or((u32::MAX, u32::MAX), |l| (l.line, l.col));
                self.mov32(0, trap_code(r));
                self.mov32(1, line);
                self.mov32(2, col);
                let s = self.sym("__fir_trap", false);
                self.line(&format!("bl {s}"));
            }
            Inst::Bl { func } => {
                let (s, _) = self.func_sym(func);
                self.line(&format!("bl {s}"));
            }
            Inst::Blr { n, .. } => self.line(&format!("blr {}", x(n))),
            Inst::BlAlloc { align, .. } => {
                if align <= 16 {
                    let s = self.sym("malloc", false);
                    self.line(&format!("bl {s}"));
                } else {
                    // aligned_alloc(align, size rounded up to a multiple of align)
                    let a = u64::from(align);
                    if a - 1 < 4096 {
                        self.line(&format!("add x0, x0, #{}", a - 1));
                    } else {
                        self.line(&format!("movz x1, #{}, lsl #{}", (a - 1) & 0xffff, 0));
                        if (a - 1) >> 16 != 0 {
                            self.line(&format!("movk x1, #{}, lsl #16", ((a - 1) >> 16) & 0xffff));
                        }
                        self.line("add x0, x0, x1");
                    }
                    self.line(&format!("and x0, x0, #{:#x}", (!(a - 1))));
                    self.line("mov x1, x0");
                    self.mov32(0, align);
                    let s = self.sym("aligned_alloc", false);
                    self.line(&format!("bl {s}"));
                }
            }
            Inst::BlFree { .. } => {
                let s = self.sym("free", false);
                self.line(&format!("bl {s}"));
            }
        }
    }

    fn func(&mut self, f: &MFunc) {
        let func = &self.m.funcs[f.index as usize];
        let s = self.sym(&func.name, true);
        self.out.push('\n');
        self.line(&format!(".globl {s}"));
        self.line(".p2align 2");
        if self.o.os == Os::Linux {
            self.line(&format!(".type {s}, %function"));
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
            self.line(&format!(".size {s}, .-{s}"));
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
                let s = if gs_has(gs, name) {
                    self.sym(name, true)
                } else {
                    match self.m.funcs.iter().position(|f| f.name == name) {
                        Some(_) => self.sym(name, true),
                        None => self.sym(name, false),
                    }
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
                    Shape::Func(..) => {}
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
            self.line(&format!(".globl {s}"));
            self.line(&format!(".p2align {}", align.trailing_zeros()));
            if self.o.os == Os::Linux {
                self.line(&format!(".type {s}, %object"));
                self.line(&format!(".size {s}, {}", bytes.len()));
            }
            let _ = writeln!(self.out, "{s}:");
            let mut i = 0;
            let mut ri = relocs.iter().peekable();
            while i < bytes.len() {
                if let Some((o, sym)) = ri.peek()
                    && *o == i
                {
                    self.line(&format!(".quad {sym}"));
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
                self.line(&format!(".byte {}", items.join(", ")));
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
        mm,
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
    e.globals();
    let _ = e.mm;
    if o.os == Os::Linux {
        e.out
            .push_str("\n\t.section .note.GNU-stack,\"\",%progbits\n");
    }
    e.out
}
