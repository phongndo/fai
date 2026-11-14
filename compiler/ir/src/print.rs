//! Prints modules in canonical text, mirroring `spec/Fir/Print.lean` byte for byte. The parser
//! reads the output back unchanged.

use std::fmt::Write;

use crate::body::{Body, Int, OpId, Operand, OperandKind, RegionId, Succ, ValueId};
use crate::decl::{Field, FieldTy, Imm, Item, Layer};
use crate::ir::*;
use crate::types::{Shape, write_rets};
use rustc_hash::FxHashMap;

/// Append an integer stored in a body.
fn push_int(out: &mut String, n: Int<'_>) {
    match n {
        Int::Small(n) if n >= 0 => push_u64(out, n as u64),
        n => write!(out, "{n}").unwrap(),
    }
}

/// Append a fact on a value of `body`, as written in text.
pub(crate) fn push_fact(out: &mut String, body: &Body, f: TrustedFact) {
    match f.fact {
        Fact::RangeS(lo, hi) | Fact::RangeU(lo, hi) => {
            out.push_str(if matches!(f.fact, Fact::RangeS(..)) {
                "range.s("
            } else {
                "range.u("
            });
            push_int(out, body.int(lo));
            out.push_str(", ");
            push_int(out, body.int(hi));
            out.push(')');
        }
        Fact::NonNull => out.push_str("nonnull"),
        Fact::Align(n) => {
            out.push_str("align(");
            push_u64(out, n);
            out.push(')');
        }
        Fact::NoAlias => out.push_str("noalias"),
        Fact::ReadOnly => out.push_str("readonly"),
    }
    out.push(' ');
    out.push_str(f.trust.name());
}

struct Printer<'a> {
    body: &'a Body,
    show_locs: bool,
    out: &'a mut String,
    /// How many fixed parameters each variadic function of the module has, by name: where a
    /// direct call's `...` goes (Lean's `OpKind.vaMark`).
    va: &'a FxHashMap<&'a str, usize>,
}

/// Append a number's decimal digits.
fn push_u64(out: &mut String, mut n: u64) {
    let mut buf = [0u8; 20];
    let mut i = buf.len();
    loop {
        i -= 1;
        buf[i] = b'0' + (n % 10) as u8;
        n /= 10;
        if n == 0 {
            break;
        }
    }
    out.push_str(std::str::from_utf8(&buf[i..]).expect("ASCII digits"));
}

fn push_ty(out: &mut String, types: &Types, t: Ty) {
    match t {
        Ty::Int(w) => {
            out.push('i');
            push_u64(out, w.into());
        }
        Ty::Ptr => out.push_str("ptr"),
        Ty::Byte(w) => {
            out.push('b');
            push_u64(out, w.into());
        }
        Ty::Slice => out.push_str("slice"),
        Ty::Float(f) => out.push_str(f.name()),
        Ty::VaList => out.push_str("va_list"),
        Ty::Agg(_) => types.write(out, t),
    }
}

/// Whether the readable form can write the op's float constant, if it has one: as the float of
/// its one result's type, whose width the bits fit (Lean's `Op.floatShown`).
fn float_shown(b: &Body, op: OpId) -> Option<FloatTy> {
    let kind = b.kind(op);
    let decl = kind.decl();
    let Some(i) = decl.imms.iter().position(|f| f.ty == FieldTy::Float) else {
        return Some(FloatTy::F64);
    };
    let mut rs = b.results(op);
    match (rs.next(), rs.next(), kind.imm(i)) {
        (Some(r), None, Some(Imm::Nat(n))) => match b.ty(r) {
            Ty::Float(f) if crate::float::fits(f, n) => Some(f),
            _ => None,
        },
        _ => None,
    }
}

impl Printer<'_> {
    fn value(&mut self, v: ValueId) {
        let b = self.body;
        self.out.push('%');
        self.out.push_str(b.name(v));
        self.out.push_str(": ");
        push_ty(self.out, b.types(), b.ty(v));
        let facts = b.facts(v);
        if !facts.is_empty() {
            self.out.push_str(" [");
            for (i, f) in facts.iter().enumerate() {
                if i > 0 {
                    self.out.push_str(", ");
                }
                push_fact(self.out, b, *f);
            }
            self.out.push(']');
        }
    }

    fn values(&mut self, vs: impl Iterator<Item = ValueId>) {
        for (i, v) in vs.enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            self.value(v);
        }
    }

    fn operand(&mut self, o: &Operand) {
        match o.get() {
            OperandKind::Value(v) => {
                self.out.push('%');
                self.out.push_str(self.body.name(v));
            }
            OperandKind::Hole(h) => {
                self.out.push('?');
                self.out.push_str(self.body.hole_name(h));
                self.out.push_str(": ");
                push_ty(self.out, self.body.types(), self.body.hole_ty(h));
            }
        }
    }

    fn operand_list(&mut self, operands: &[Operand]) {
        for (i, o) in operands.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            self.operand(o);
        }
    }

    fn loc(&mut self, loc: Option<Loc>) {
        if let Some(l) = loc
            && self.show_locs
        {
            self.out.push_str(" @");
            push_u64(self.out, l.line.into());
            self.out.push(':');
            push_u64(self.out, l.col.into());
        }
    }

    fn indent(&mut self, depth: usize) {
        for _ in 0..depth {
            self.out.push_str("  ");
        }
    }

    fn region(&mut self, depth: usize, r: RegionId) {
        self.out.push_str("{\n");
        self.ops(depth + 1, r);
        self.indent(depth);
        self.out.push('}');
    }

    /// A region's ops, at `depth`. The one place ops are printed, so `op` can be inlined here.
    fn ops(&mut self, depth: usize, r: RegionId) {
        for op in self.body.ops(r) {
            self.op(depth, op);
        }
    }

    fn op(&mut self, depth: usize, op: OpId) {
        let b = self.body;
        self.indent(depth);
        if b.results(op).len() > 0 {
            self.values(b.results(op));
            self.out.push_str(" = ");
        }
        let kind = b.kind(op);
        let regions = b
            .regions(op)
            .iter()
            .map(|&r| (b.params(r).len(), b.label(r).is_some()));
        if kind
            .decl()
            .fits(b.operands(op).len(), || kind.succ_args(b), regions)
            && float_shown(b, op).is_some()
        {
            self.readable(depth, op);
        } else {
            self.generic(depth, op);
        }
        self.out.push('\n');
    }

    /// An immediate's value as text.
    fn imm(&mut self, f: Field, v: Imm) {
        match v {
            Imm::Int(n) => push_int(self.out, self.body.int(n)),
            Imm::Nat(n) => push_u64(self.out, n),
            Imm::Align(n) | Imm::Index(n) => push_u64(self.out, n.into()),
            Imm::Str(s) => {
                if matches!(f.ty, FieldTy::Func | FieldTy::Global) {
                    self.out.push('@');
                }
                self.out.push_str(self.body.str(s));
            }
            Imm::Ty(t) => push_ty(self.out, self.body.types(), t),
            Imm::Flag(b) => self.out.push_str(if b { "true" } else { "false" }),
            Imm::Reg(r) => {
                use std::fmt::Write;
                let _ = write!(self.out, "{r}");
            }
            Imm::Succ(s) => self.generic_succ(self.body.succ(s)),
            Imm::Cases(c) => {
                self.out.push('[');
                for (i, case) in self.body.cases(c).iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    push_int(self.out, self.body.int(case.key));
                    self.out.push_str(": ");
                    self.generic_succ(case.succ);
                }
                self.out.push(']');
            }
        }
    }

    /// A branch target in the generic form: `^b`, or `^b(n)` for `n` arguments.
    fn generic_succ(&mut self, s: Succ) {
        self.out.push('^');
        self.out.push_str(self.body.str(s.label));
        if s.nargs > 0 {
            self.out.push('(');
            push_u64(self.out, s.nargs.into());
            self.out.push(')');
        }
    }

    /// A branch target with its arguments, the operands from `next` on; returns where the
    /// next target's arguments start.
    fn succ(&mut self, s: Succ, operands: &[Operand], next: usize) -> usize {
        self.out.push('^');
        self.out.push_str(self.body.str(s.label));
        let end = (next + s.nargs as usize).min(operands.len());
        let mine = &operands[next.min(end)..end];
        if !mine.is_empty() {
            self.out.push('(');
            self.operand_list(mine);
            self.out.push(')');
        }
        next + s.nargs as usize
    }

    /// `cf.blocks`'s blocks, each label at the op's indentation and its ops one level in.
    #[inline(never)]
    fn blocks(&mut self, depth: usize, op: OpId) {
        let b = self.body;
        self.out.push_str(" {\n");
        for &r in b.regions(op) {
            self.indent(depth);
            self.out.push('^');
            if let Some(l) = b.label(r) {
                self.out.push_str(b.str(l));
            }
            if b.params(r).len() > 0 {
                self.out.push('(');
                self.values(b.params(r));
                self.out.push(')');
            }
            self.out.push_str(":\n");
            self.ops(depth + 1, r);
        }
        self.indent(depth);
        self.out.push('}');
    }

    /// The readable form, from the op's declared format.
    fn readable(&mut self, depth: usize, op: OpId) {
        let b = self.body;
        let kind = b.kind(op);
        let decl = kind.decl();
        self.out.push_str(kind.mnemonic());
        let operands = b.operands(op);
        let mut next = 0;
        for &item in decl.head() {
            match item {
                Item::Imm(i) => {
                    let f = decl.imms[usize::from(i)];
                    match kind.imm(i.into()) {
                        Some(Imm::Flag(set)) => {
                            if set {
                                self.out.push(' ');
                                self.out.push_str(f.name);
                            }
                        }
                        Some(Imm::Succ(s)) => {
                            self.out.push(' ');
                            next = self.succ(b.succ(s), operands, next);
                        }
                        Some(Imm::Cases(c)) => {
                            self.out.push_str(" [");
                            for (j, case) in b.cases(c).iter().enumerate() {
                                if j > 0 {
                                    self.out.push_str(", ");
                                }
                                push_int(self.out, b.int(case.key));
                                self.out.push_str(": ");
                                next = self.succ(case.succ, operands, next);
                            }
                            self.out.push(']');
                        }
                        Some(Imm::Nat(n)) if f.ty == FieldTy::Float => {
                            self.out.push(' ');
                            let t = float_shown(b, op).unwrap_or(FloatTy::F64);
                            self.out.push_str(&crate::float::render(t, n));
                        }
                        Some(v) => {
                            self.out.push(' ');
                            self.imm(f, v);
                        }
                        None => {}
                    }
                }
                Item::Operand => {
                    if let Some(o) = operands.get(next) {
                        self.out.push(' ');
                        self.operand(o);
                        next += 1;
                    }
                }
                Item::Comma => self.out.push(','),
                Item::Keyword(kw) => {
                    self.out.push(' ');
                    self.out.push_str(kw);
                }
                Item::Variadic => {
                    // Every operand but the branch targets' arguments, which come after.
                    let end = operands.len().saturating_sub(kind.succ_args(b)).max(next);
                    if next < end {
                        self.out.push(' ');
                        self.operand_list(&operands[next..end]);
                    }
                    next = end;
                }
                Item::Args => {
                    let end = operands.len().saturating_sub(kind.succ_args(b)).max(next);
                    let args = &operands[next.min(end)..end];
                    self.out.push('(');
                    match self.va_mark(kind).filter(|&k| k <= args.len()) {
                        None => self.operand_list(args),
                        Some(k) => {
                            self.operand_list(&args[..k]);
                            if k > 0 {
                                self.out.push_str(", ");
                            }
                            self.out.push_str("...");
                            if k < args.len() {
                                self.out.push(' ');
                                self.operand_list(&args[k..]);
                            }
                        }
                    }
                    self.out.push(')');
                    next = end;
                }
                Item::Iter => {
                    if let Some(&body) = b.regions(op).first()
                        && b.params(body).len() > 0
                    {
                        self.out.push_str(" iter(");
                        for (i, (p, a)) in b.params(body).zip(&operands[next..]).enumerate() {
                            if i > 0 {
                                self.out.push_str(", ");
                            }
                            self.value(p);
                            self.out.push_str(" = ");
                            self.operand(a);
                        }
                        self.out.push(')');
                    }
                    next = operands.len();
                }
                Item::Region(_) | Item::Blocks => {}
            }
        }
        self.loc(b.loc(op));
        for (kw, &r) in decl.regions().zip(b.regions(op)) {
            match kw {
                None => {
                    self.out.push(' ');
                    self.region(depth, r);
                }
                Some(kw) => {
                    if !b.is_empty(r) || b.params(r).len() > 0 {
                        self.out.push(' ');
                        self.out.push_str(kw);
                        if b.params(r).len() > 0 {
                            self.out.push('(');
                            self.values(b.params(r));
                            self.out.push(')');
                        }
                        self.out.push(' ');
                        self.region(depth, r);
                    }
                }
            }
        }
        if decl.has_blocks() {
            self.blocks(depth, op);
        }
    }

    /// Where a call's `...` goes: after as many arguments as the callee's signature has
    /// parameters, if it is variadic (Lean's `OpKind.vaMark`).
    fn va_mark(&self, kind: OpKind) -> Option<usize> {
        let b = self.body;
        match kind {
            OpKind::CallIndirect(sig) | OpKind::InvokeIndirect { sig, .. } => {
                match b.types().shape_of(sig) {
                    Some(Shape::Func(ps, _, true)) => Some(ps.len()),
                    _ => None,
                }
            }
            OpKind::Call { callee } | OpKind::Invoke { callee, .. } => {
                self.va.get(b.str(callee)).copied()
            }
            _ => None,
        }
    }

    /// The generic form: `"name"(operands) {attrs} @loc (regions)`.
    fn generic(&mut self, depth: usize, op: OpId) {
        let b = self.body;
        let kind = b.kind(op);
        let decl = kind.decl();
        self.out.push('"');
        self.out.push_str(kind.mnemonic());
        self.out.push_str("\"(");
        self.operand_list(b.operands(op));
        self.out.push(')');
        if !decl.imms.is_empty() {
            self.out.push_str(" {");
            for (i, &f) in decl.imms.iter().enumerate() {
                if i > 0 {
                    self.out.push_str(", ");
                }
                self.out.push_str(f.name);
                self.out.push_str(" = ");
                if let Some(v) = kind.imm(i) {
                    self.imm(f, v);
                }
            }
            self.out.push('}');
        }
        self.loc(b.loc(op));
        if !b.regions(op).is_empty() {
            self.out.push_str(" (");
            for (i, &r) in b.regions(op).iter().enumerate() {
                if i > 0 {
                    self.out.push_str(", ");
                }
                if let Some(l) = b.label(r) {
                    self.out.push('^');
                    self.out.push_str(b.str(l));
                }
                if b.params(r).len() > 0 {
                    self.out.push('(');
                    self.values(b.params(r));
                    self.out.push(')');
                }
                if b.label(r).is_some() || b.params(r).len() > 0 {
                    self.out.push(' ');
                }
                self.region(depth, r);
            }
            self.out.push(')');
        }
    }
}

impl Func {
    /// The function as text. Without its module, calls of variadic functions other than
    /// through a pointer don't show their `...`.
    pub fn render(&self, show_locs: bool) -> String {
        let mut out = String::new();
        self.render_into(&mut out, show_locs, &FxHashMap::default());
        out
    }

    fn render_into(&self, out: &mut String, show_locs: bool, va: &FxHashMap<&str, usize>) {
        let mut p = Printer {
            body: &self.body,
            show_locs,
            out,
            va,
        };
        let entry = self.body.entry();
        p.out.push_str("func @");
        p.out.push_str(&self.name);
        p.out.push('(');
        p.values(self.body.params(entry));
        if self.variadic {
            let fixed = self.body.params(entry).len() > 0;
            p.out.push_str(if fixed { ", ..." } else { "..." });
        }
        p.out.push(')');
        let types = self.body.types();
        write_rets(p.out, &self.rets, |out, t| push_ty(out, types, *t));
        if let Some(s) = &self.file
            && show_locs
        {
            p.out.push_str(" loc \"");
            p.out.push_str(s);
            p.out.push('"');
        }
        p.out.push(' ');
        p.region(0, entry);
        p.out.push('\n');
    }
}

/// An initializer as text (Lean's `Init.render`).
fn push_init(out: &mut String, g: &Globals, init: Init) {
    match init {
        Init::Zero => out.push_str("zero"),
        Init::Int(i) => write!(out, "{}", g.int(i)).unwrap(),
        Init::Float(f, i) => out.push_str(&crate::float::render(f, g.float(i))),
        Init::Null => out.push_str("null"),
        Init::Sym(r) => {
            out.push('@');
            out.push_str(g.text(r));
        }
        Init::SymOff(r, i) => write!(out, "offset(@{}, {})", g.text(r), g.int(i)).unwrap(),
        Init::Bytes(r) => {
            out.push_str("bytes \"");
            for b in g.bytes(r) {
                write!(out, "{b:02x}").unwrap();
            }
            out.push('"');
        }
        Init::List(r) => {
            out.push('{');
            for (i, &item) in g.items(r).iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                push_init(out, g, item);
            }
            out.push('}');
        }
    }
}

impl Module {
    /// Canonical text. With `show_locs` off, op locations and function files are left out.
    pub fn render(&self, show_locs: bool) -> String {
        let mut out = String::new();
        if self.layer != Layer::Hfir {
            writeln!(out, "layer {}", self.layer).unwrap();
        }
        let sp = &self.space;
        if *sp != SpaceCfg::default() {
            write!(
                out,
                "memspace default ptr {} addr {}",
                sp.ptr_bits, sp.addr_bits
            )
            .unwrap();
            if sp.ptr_align != SpaceCfg::natural_align(sp.ptr_bits) {
                write!(out, " align {}", sp.ptr_align).unwrap();
            }
            if sp.ints != DEFAULT_INTS {
                out.push_str(" int");
                for (w, a) in &sp.ints {
                    write!(out, " {w}:{a}").unwrap();
                }
            }
            if (sp.va_size, sp.va_align) != DEFAULT_VA_LIST {
                write!(out, " valist {}:{}", sp.va_size, sp.va_align).unwrap();
            }
            out.push('\n');
        }
        if !out.is_empty() {
            out.push('\n');
        }
        let g = &self.globals;
        for i in 0..g.len() {
            out.push_str("global ");
            if g.is_const(i) {
                out.push_str("const ");
            }
            out.push('@');
            out.push_str(g.name(i));
            out.push_str(": ");
            push_ty(&mut out, &g.types, g.ty(i));
            if g.align(i) != 1 {
                write!(out, " align {}", g.align(i)).unwrap();
            }
            out.push_str(" = ");
            push_init(&mut out, g, g.init(i));
            out.push('\n');
        }
        if !g.is_empty() {
            out.push('\n');
        }
        for x in &self.externs {
            out.push_str("extern func @");
            out.push_str(&x.name);
            out.push('(');
            for (i, &t) in x.params.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                push_ty(&mut out, &g.types, t);
            }
            if x.variadic {
                out.push_str(if x.params.is_empty() { "..." } else { ", ..." });
            }
            out.push(')');
            write_rets(&mut out, &x.rets, |out, t| push_ty(out, &g.types, *t));
            out.push_str(" effects[");
            for (i, e) in x.effects.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write!(out, "{e}").unwrap();
            }
            out.push_str("] ");
            out.push_str(x.trust.name());
            out.push('\n');
        }
        if !self.externs.is_empty() {
            out.push('\n');
        }
        // Where each direct call's `...` goes: after a variadic callee's parameters.
        let mut va = FxHashMap::default();
        for f in self.funcs.iter().filter(|f| f.variadic) {
            va.insert(f.name.as_str(), f.body.params(f.body.entry()).len());
        }
        for x in self.externs.iter().filter(|x| x.variadic) {
            va.entry(x.name.as_str()).or_insert(x.params.len());
        }
        for (i, f) in self.funcs.iter().enumerate() {
            if i > 0 {
                out.push('\n');
            }
            f.render_into(&mut out, show_locs, &va);
        }
        out
    }
}
