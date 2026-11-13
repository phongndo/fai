//! GNU-syntax (AT&T) x86-64 assembly for ELF (Linux) from allocated machine code.
//!
//! Each instruction prints as one instruction, except: `setcc` is followed by `movzbl` (the
//! result is a whole register); `ret` is the epilogue (`rsp` back to the saved registers, which
//! are popped, then `rbp`) and `ret`; a trap loads its reason and location into `edi`, `esi`, and
//! `edx` and calls `__fir_trap`; and the exception ops address the slot `__fir_exn` through its
//! GOT entry in `r11`. A function starts with the prologue: `rbp` pushed and set, the
//! callee-saved registers the allocation used pushed, `rsp` lowered by the frame's size, and
//! realigned when a local needs more than 16 bytes. A branch to the next block is left out.
//! Calls of external functions go through the PLT, and their addresses come from the GOT, so
//! the output links into position-independent executables. Every output defines a weak
//! `__fir_trap` that executes `ud2` (a program or the test harness defines its own, which gets
//! `__fir_trap(reason, line, col)` with the reason codes of
//! `crate::backend::aarch64::emit::trap_code`), and a weak, zeroed `__fir_exn` when its code uses
//! the exception slot.

use std::fmt::Write;

use super::mir::*;
use crate::backend::aarch64::emit::trap_code;
use crate::backend::data::quote;
use crate::ir::Module;

/// How to emit a module.
#[derive(Clone, Debug, Default)]
pub struct Options {
    /// Prepended to the module's own function and global names.
    pub prefix: String,
    /// Prepended to external functions' names (not to the runtime's: `malloc`, `free`,
    /// `aligned_alloc`, `memmove`, `__fir_trap`, `__fir_exn`).
    pub extern_prefix: String,
}

const R64: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];
const R32: [&str; 16] = [
    "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d",
    "r13d", "r14d", "r15d",
];
const R16: [&str; 16] = [
    "ax", "cx", "dx", "bx", "sp", "bp", "si", "di", "r8w", "r9w", "r10w", "r11w", "r12w", "r13w",
    "r14w", "r15w",
];
const R8: [&str; 16] = [
    "al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil", "r8b", "r9b", "r10b", "r11b", "r12b",
    "r13b", "r14b", "r15b",
];

/// A register's 64-bit name.
pub fn reg64(n: u8) -> &'static str {
    R64[n as usize]
}

/// `%name` of a physical register at a size in bytes.
fn r(reg: Reg, size: u8) -> String {
    let Reg::P(n) = reg else {
        // Virtual registers only print before allocation, in messages.
        return format!("%{reg}");
    };
    let n = n as usize;
    let name = match size {
        1 => R8[n],
        2 => R16[n],
        4 => R32[n],
        _ => R64[n],
    };
    format!("%{name}")
}

fn q(reg: Reg) -> String {
    r(reg, 8)
}

fn mem(base: Reg, off: i32) -> String {
    if off == 0 {
        format!("({})", q(base))
    } else {
        format!("{off}({})", q(base))
    }
}

fn alu_name(op: AluOp) -> &'static str {
    match op {
        AluOp::Add => "addq",
        AluOp::Sub => "subq",
        AluOp::And => "andq",
        AluOp::Or => "orq",
        AluOp::Xor => "xorq",
        AluOp::Imul => "imulq",
    }
}

fn shift_name(op: ShiftOp) -> &'static str {
    match op {
        ShiftOp::Shl => "shlq",
        ShiftOp::Shr => "shrq",
        ShiftOp::Sar => "sarq",
    }
}

struct Emitter<'a> {
    m: &'a Module,
    o: &'a Options,
    out: String,
}

impl Emitter<'_> {
    fn line(&mut self, a: std::fmt::Arguments<'_>) {
        self.out.push('\t');
        let _ = self.out.write_fmt(a);
        self.out.push('\n');
    }

    /// A symbol: the module's own (with the prefix), or a runtime one as it is.
    fn sym(&self, name: &str, own: bool) -> String {
        if own {
            quote(&format!("{}{name}", self.o.prefix))
        } else {
            quote(name)
        }
    }

    /// The symbol of callee `f` and whether it is external.
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

    fn label(f: &MFunc, b: u32) -> String {
        format!(".LF{}_{b}", f.index)
    }

    /// The exception slot's address in `r11`.
    fn exn_slot(&mut self) {
        let s = self.sym("__fir_exn", false);
        self.line(format_args!("movq {s}@GOTPCREL(%rip), %r11"));
    }

    fn epilogue(&mut self, f: &MFunc) {
        let saved: Vec<u8> = f.frame.saved_regs().collect();
        if saved.is_empty() {
            self.line(format_args!("movq %rbp, %rsp"));
        } else {
            self.line(format_args!("leaq -{}(%rbp), %rsp", 8 * saved.len()));
            for &s in saved.iter().rev() {
                self.line(format_args!("popq %{}", R64[s as usize]));
            }
        }
        self.line(format_args!("popq %rbp"));
        self.line(format_args!("ret"));
    }

    fn inst(&mut self, f: &MFunc, i: usize, next: Option<u32>) {
        let inst = f.insts[i];
        match inst {
            Inst::Mov { d, s } => {
                if d != s {
                    self.line(format_args!("movq {}, {}", q(s), q(d)));
                }
            }
            Inst::MovImm { d, imm } => {
                if imm <= u64::from(u32::MAX) {
                    self.line(format_args!("movl ${imm}, {}", r(d, 4)));
                } else if i32::try_from(imm as i64).is_ok() {
                    self.line(format_args!("movq ${}, {}", imm as i64, q(d)));
                } else {
                    self.line(format_args!("movabsq ${}, {}", imm as i64, q(d)));
                }
            }
            Inst::Alu { op, d, s } => {
                self.line(format_args!("{} {}, {}", alu_name(op), q(s), q(d)));
            }
            Inst::AluImm { op, d, imm } => match op {
                AluOp::Imul => self.line(format_args!("imulq ${imm}, {}, {}", q(d), q(d))),
                _ => self.line(format_args!("{} ${imm}, {}", alu_name(op), q(d))),
            },
            Inst::Neg { d } => self.line(format_args!("negq {}", q(d))),
            Inst::ShiftCl { op, d } => {
                self.line(format_args!("{} %cl, {}", shift_name(op), q(d)));
            }
            Inst::ShiftImm { op, d, amount } => {
                self.line(format_args!("{} ${amount}, {}", shift_name(op), q(d)));
            }
            Inst::Ext { signed, from, d, s } => match (signed, from) {
                (true, 8) => self.line(format_args!("movsbq {}, {}", r(s, 1), q(d))),
                (true, 16) => self.line(format_args!("movswq {}, {}", r(s, 2), q(d))),
                (true, _) => self.line(format_args!("movslq {}, {}", r(s, 4), q(d))),
                (false, 8) => self.line(format_args!("movzbl {}, {}", r(s, 1), r(d, 4))),
                (false, 16) => self.line(format_args!("movzwl {}, {}", r(s, 2), r(d, 4))),
                (false, _) => self.line(format_args!("movl {}, {}", r(s, 4), r(d, 4))),
            },
            Inst::Cmp { a, b } => self.line(format_args!("cmpq {}, {}", q(b), q(a))),
            Inst::CmpImm { a, imm } => self.line(format_args!("cmpq ${imm}, {}", q(a))),
            Inst::TestImm { a, imm } => self.line(format_args!("testq ${imm}, {}", q(a))),
            Inst::Setcc { c, d } => {
                self.line(format_args!("set{} {}", c.name(), r(d, 1)));
                self.line(format_args!("movzbl {}, {}", r(d, 1), r(d, 4)));
            }
            Inst::Cmov { c, d, s } => {
                self.line(format_args!("cmov{}q {}, {}", c.name(), q(s), q(d)));
            }
            Inst::Cqo => self.line(format_args!("cqto")),
            Inst::Div { signed, s } => {
                self.line(format_args!(
                    "{} {}",
                    if signed { "idivq" } else { "divq" },
                    q(s)
                ));
            }
            Inst::MulWide { s } => self.line(format_args!("mulq {}", q(s))),
            Inst::Load { size, d, base, off } => {
                let m = mem(base, off);
                match size {
                    1 => self.line(format_args!("movzbl {m}, {}", r(d, 4))),
                    2 => self.line(format_args!("movzwl {m}, {}", r(d, 4))),
                    4 => self.line(format_args!("movl {m}, {}", r(d, 4))),
                    _ => self.line(format_args!("movq {m}, {}", q(d))),
                }
            }
            Inst::Store { size, s, base, off } => {
                let m = mem(base, off);
                let op = match size {
                    1 => "movb",
                    2 => "movw",
                    4 => "movl",
                    _ => "movq",
                };
                self.line(format_args!("{op} {}, {m}", r(s, size)));
            }
            Inst::Lea { d, base, off } => {
                self.line(format_args!("leaq {}, {}", mem(base, off), q(d)));
            }
            Inst::LeaGlobal { d, global } => {
                let s = self.sym(self.m.globals.name(global as usize), true);
                self.line(format_args!("leaq {s}(%rip), {}", q(d)));
            }
            Inst::LeaFunc { d, func } => {
                let (s, ext) = self.func_sym(func);
                if ext {
                    self.line(format_args!("movq {s}@GOTPCREL(%rip), {}", q(d)));
                } else {
                    self.line(format_args!("leaq {s}(%rip), {}", q(d)));
                }
            }
            Inst::Call { func } => {
                let (s, ext) = self.func_sym(func);
                let plt = if ext { "@PLT" } else { "" };
                self.line(format_args!("call {s}{plt}"));
            }
            Inst::CallInd { s, .. } => self.line(format_args!("call *{}", q(s))),
            Inst::CallRt(rt) => {
                let s = self.sym(rt.name(), false);
                self.line(format_args!("call {s}@PLT"));
            }
            Inst::Jmp { t } => {
                if Some(t) != next {
                    self.line(format_args!("jmp {}", Self::label(f, t)));
                }
            }
            Inst::Jcc { c, t, f: e } => {
                if Some(t) == next {
                    self.line(format_args!("j{} {}", c.invert().name(), Self::label(f, e)));
                } else {
                    self.line(format_args!("j{} {}", c.name(), Self::label(f, t)));
                    if Some(e) != next {
                        self.line(format_args!("jmp {}", Self::label(f, e)));
                    }
                }
            }
            Inst::Ret => self.epilogue(f),
            Inst::Trap(reason) => {
                let (line, col) = f.locs[i].map_or((u32::MAX, u32::MAX), |l| (l.line, l.col));
                self.line(format_args!("movl ${}, %edi", trap_code(reason)));
                self.line(format_args!("movl ${line}, %esi"));
                self.line(format_args!("movl ${col}, %edx"));
                let s = self.sym("__fir_trap", false);
                self.line(format_args!("call {s}@PLT"));
                self.line(format_args!("ud2"));
            }
            Inst::ExnSet { s } => {
                self.exn_slot();
                self.line(format_args!("movq {}, 8(%r11)", q(s)));
                self.line(format_args!("movq %r11, (%r11)"));
            }
            Inst::ExnTake { d } => {
                self.exn_slot();
                self.line(format_args!("movq 8(%r11), {}", q(d)));
                self.line(format_args!("movq $0, (%r11)"));
            }
            Inst::ExnTest => {
                self.exn_slot();
                self.line(format_args!("cmpq $0, (%r11)"));
            }
        }
    }

    fn func(&mut self, f: &MFunc) {
        let func = &self.m.funcs[f.index as usize];
        let s = self.sym(&func.name, true);
        self.out.push('\n');
        self.line(format_args!(".globl {s}"));
        self.line(format_args!(".p2align 4"));
        self.line(format_args!(".type {s}, @function"));
        let _ = writeln!(self.out, "{s}:");
        self.line(format_args!("pushq %rbp"));
        self.line(format_args!("movq %rsp, %rbp"));
        for reg in f.frame.saved_regs() {
            self.line(format_args!("pushq %{}", R64[reg as usize]));
        }
        let size = f.frame.size();
        if size > 0 {
            self.line(format_args!("subq ${size}, %rsp"));
        }
        if f.frame.align > 16 {
            self.line(format_args!("andq $-{}, %rsp", f.frame.align));
        }
        for b in 0..f.blocks.len() {
            if b > 0 {
                let _ = writeln!(self.out, "{}:", Self::label(f, b as u32));
            }
            let next = (b + 1 < f.blocks.len()).then_some(b as u32 + 1);
            for i in f.block_range(b) {
                self.inst(f, i, next);
            }
        }
        self.line(format_args!(".size {s}, .-{s}"));
    }
}

/// Assembly for a module whose functions are allocated.
pub fn emit(m: &Module, mm: &MModule, o: &Options) -> String {
    let mut e = Emitter {
        m,
        o,
        out: String::new(),
    };
    e.out
        .push_str("# Generated by fir: x86-64 assembly.\n\t.text\n");
    for f in &mm.funcs {
        e.func(f);
    }
    // The trap handler a program gets unless it defines its own.
    let t = e.sym("__fir_trap", false);
    e.out.push('\n');
    e.line(format_args!(".weak {t}"));
    e.line(format_args!(".p2align 4"));
    e.line(format_args!(".type {t}, @function"));
    let _ = writeln!(e.out, "{t}:");
    e.line(format_args!("ud2"));
    let uses_exn = mm.funcs.iter().any(|f| {
        f.insts.iter().any(|i| {
            matches!(
                i,
                Inst::ExnSet { .. } | Inst::ExnTake { .. } | Inst::ExnTest
            )
        })
    });
    if uses_exn {
        let s = e.sym("__fir_exn", false);
        e.out.push('\n');
        e.line(format_args!(".data"));
        e.line(format_args!(".weak {s}"));
        e.line(format_args!(".p2align 3"));
        e.line(format_args!(".type {s}, @object"));
        e.line(format_args!(".size {s}, 16"));
        let _ = writeln!(e.out, "{s}:");
        e.line(format_args!(".quad 0, 0"));
    }
    let data =
        crate::backend::data::globals(m, &|name, own| e.sym(name, own), &o.extern_prefix, false);
    e.out.push_str(&data);
    e.out
        .push_str("\n\t.section .note.GNU-stack,\"\",@progbits\n");
    e.out
}
