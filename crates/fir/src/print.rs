//! Prints modules in canonical text, mirroring `spec/Fir/Print.lean` byte for byte. The parser
//! reads the output back unchanged.

use std::fmt::Write;

use crate::body::{Body, Int, OpId, Operand, OperandKind, RegionId, ValueId};
use crate::ir::*;

impl Ovf {
    pub fn suffix(self) -> &'static str {
        match self {
            Ovf::Wrap => "wrap",
            Ovf::Nsw => "nsw",
            Ovf::Nuw => "nuw",
            Ovf::NswNuw => "nsw.nuw",
            Ovf::Trap(s) => {
                if s {
                    "s.trap"
                } else {
                    "u.trap"
                }
            }
            Ovf::Sat(s) => {
                if s {
                    "s.sat"
                } else {
                    "u.sat"
                }
            }
            Ovf::Ub(s) => {
                if s {
                    "s.ub"
                } else {
                    "u.ub"
                }
            }
        }
    }
}

impl Edge {
    pub fn name(self) -> &'static str {
        match self {
            Edge::Ub => "ub",
            Edge::Trap => "trap",
            Edge::Total => "total",
            Edge::Wrap => "wrap",
        }
    }
}

impl ShiftEdge {
    pub fn name(self) -> &'static str {
        match self {
            ShiftEdge::Ub => "ub",
            ShiftEdge::Trap => "trap",
            ShiftEdge::Mask => "mask",
            ShiftEdge::Total => "total",
        }
    }
}

impl Pred {
    pub fn name(self) -> &'static str {
        match self {
            Pred::Eq => "eq",
            Pred::Ne => "ne",
            Pred::Slt => "slt",
            Pred::Sle => "sle",
            Pred::Sgt => "sgt",
            Pred::Sge => "sge",
            Pred::Ult => "ult",
            Pred::Ule => "ule",
            Pred::Ugt => "ugt",
            Pred::Uge => "uge",
        }
    }
}

/// Whether one division modifier covers both edge cases.
fn div_one_modifier(signed: bool, zero: Edge, ovf: Edge) -> bool {
    !signed
        || (zero, ovf) == (Edge::Ub, Edge::Ub)
        || (zero, ovf) == (Edge::Trap, Edge::Trap)
        || (zero, ovf) == (Edge::Total, Edge::Wrap)
}

impl OpKind {
    /// The op's name with its modifiers, as written in text.
    pub fn name(&self) -> String {
        let mut s = String::new();
        self.write_name(&mut s);
        s
    }

    /// Append the op's name with its modifiers.
    pub fn write_name(&self, out: &mut String) {
        use OpKind::*;
        let mut push = |parts: &[&str]| {
            for p in parts {
                out.push_str(p);
            }
        };
        match self {
            Const(_) => push(&["int.const"]),
            Poison => push(&["poison"]),
            Freeze => push(&["freeze"]),
            Copy => push(&["copy"]),
            Select => push(&["select"]),
            Arith(op, o) => {
                let n = match op {
                    ArithOp::Add => "int.add.",
                    ArithOp::Sub => "int.sub.",
                    ArithOp::Mul => "int.mul.",
                };
                push(&[n, o.suffix()]);
            }
            Bit(op) => push(&[match op {
                BitOp::And => "int.and",
                BitOp::Or => "int.or",
                BitOp::Xor => "int.xor",
            }]),
            Div(op, z, o) => {
                let n = match op {
                    DivOp::DivS => "int.div.s.",
                    DivOp::DivU => "int.div.u.",
                    DivOp::RemS => "int.rem.s.",
                    DivOp::RemU => "int.rem.u.",
                };
                if div_one_modifier(op.signed(), *z, *o) {
                    push(&[n, z.name()]);
                } else {
                    push(&[n, z.name(), ".", o.name()]);
                }
            }
            Shift(op, e) => {
                let n = match op {
                    ShiftOp::Shl => "int.shl.",
                    ShiftOp::ShrU => "int.shr.u.",
                    ShiftOp::ShrS => "int.shr.s.",
                };
                push(&[n, e.name()]);
            }
            Cmp(p) => push(&["int.cmp.", p.name()]),
            Zext => push(&["int.zext"]),
            Sext => push(&["int.sext"]),
            Trunc(m) => push(&[match m {
                TruncMode::Wrap => "int.trunc.wrap",
                TruncMode::Nsw => "int.trunc.nsw",
                TruncMode::Nuw => "int.trunc.nuw",
            }]),
            If => push(&["cf.if"]),
            Loop { .. } => push(&["cf.loop"]),
            Yield => push(&["cf.yield"]),
            Break => push(&["cf.break"]),
            Continue => push(&["cf.continue"]),
            Ret => push(&["func.ret"]),
            MemStack { .. } => push(&["mem.stack"]),
            MemAlloc { fail, .. } => push(&[match fail {
                AllocFail::Null => "mem.alloc.null",
                AllocFail::Trap => "mem.alloc.trap",
            }]),
            MemFree { .. } => push(&["mem.free"]),
            Load { .. } => push(&["mem.load"]),
            Store { .. } => push(&["mem.store"]),
            PtrOffset { inbounds } => push(&[if *inbounds {
                "ptr.offset.inbounds"
            } else {
                "ptr.offset.wrap"
            }]),
            PtrAddr => push(&["ptr.addr"]),
            PtrExpose => push(&["ptr.expose"]),
            PtrFromExposed => push(&["ptr.from_exposed"]),
            PtrWithAddr => push(&["ptr.with_addr"]),
            PtrNull => push(&["ptr.null"]),
            PtrCmp(p) => push(&["ptr.cmp.", p.name()]),
            Call { .. } => push(&["func.call"]),
        }
    }
}

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

fn push_ty(out: &mut String, t: Ty) {
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
    }
}

impl Printer<'_> {
    fn value(&mut self, v: ValueId) {
        let b = self.body;
        self.out.push('%');
        self.out.push_str(b.name(v));
        self.out.push_str(": ");
        push_ty(self.out, b.ty(v));
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
                push_ty(self.out, self.body.hole_ty(h));
            }
        }
    }

    fn operands(&mut self, op: OpId) {
        for (i, o) in self.body.operands(op).iter().enumerate() {
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
        for op in self.body.ops(r) {
            self.op(depth + 1, op);
        }
        self.indent(depth);
        self.out.push('}');
    }

    fn op(&mut self, depth: usize, op: OpId) {
        let b = self.body;
        self.indent(depth);
        if b.results(op).len() > 0 {
            self.values(b.results(op));
            self.out.push_str(" = ");
        }
        let kind = b.kind(op);
        match (kind, b.regions(op)) {
            (OpKind::Const(n), _) => {
                self.out.push_str("int.const ");
                push_int(self.out, b.int(n));
                self.loc(b.loc(op));
            }
            (OpKind::If, &[thn, els]) => {
                self.out.push_str("cf.if ");
                self.operands(op);
                self.loc(b.loc(op));
                self.out.push(' ');
                self.region(depth, thn);
                if !b.is_empty(els) {
                    self.out.push_str(" else ");
                    self.region(depth, els);
                }
            }
            (OpKind::Loop { progress }, &[body]) => {
                self.out.push_str("cf.loop");
                if progress {
                    self.out.push_str(" progress");
                }
                if b.params(body).len() > 0 {
                    self.out.push_str(" iter(");
                    for (i, (p, a)) in b.params(body).zip(b.operands(op)).enumerate() {
                        if i > 0 {
                            self.out.push_str(", ");
                        }
                        self.value(p);
                        self.out.push_str(" = ");
                        self.operand(a);
                    }
                    self.out.push(')');
                }
                self.loc(b.loc(op));
                self.out.push(' ');
                self.region(depth, body);
            }
            (OpKind::MemStack { size, align }, _) => {
                self.out.push_str("mem.stack ");
                push_u64(self.out, size);
                self.out.push_str(", align ");
                push_u64(self.out, align.into());
                self.loc(b.loc(op));
            }
            (OpKind::MemAlloc { family, align, .. }, _) => {
                kind.write_name(self.out);
                self.out.push(' ');
                self.out.push_str(b.str(family));
                self.out.push(' ');
                self.operands(op);
                self.out.push_str(", align ");
                push_u64(self.out, align.into());
                self.loc(b.loc(op));
            }
            (OpKind::MemFree { family }, _) => {
                self.out.push_str("mem.free ");
                self.out.push_str(b.str(family));
                self.out.push(' ');
                self.operands(op);
                self.loc(b.loc(op));
            }
            (OpKind::Load { align }, _) => {
                self.out.push_str("mem.load ");
                self.operands(op);
                self.out.push_str(", align ");
                push_u64(self.out, align.into());
                self.loc(b.loc(op));
            }
            (OpKind::Store { ty, align }, _) => {
                self.out.push_str("mem.store ");
                push_ty(self.out, ty);
                self.out.push(' ');
                self.operands(op);
                self.out.push_str(", align ");
                push_u64(self.out, align.into());
                self.loc(b.loc(op));
            }
            (OpKind::Call { callee }, _) => {
                self.out.push_str("func.call @");
                self.out.push_str(b.str(callee));
                self.out.push('(');
                self.operands(op);
                self.out.push(')');
                self.loc(b.loc(op));
            }
            (k, _) => {
                k.write_name(self.out);
                if !b.operands(op).is_empty() {
                    self.out.push(' ');
                    self.operands(op);
                }
                self.loc(b.loc(op));
            }
        }
        self.out.push('\n');
    }
}

impl Func {
    pub fn render(&self, show_locs: bool) -> String {
        let mut out = String::new();
        self.render_into(&mut out, show_locs);
        out
    }

    fn render_into(&self, out: &mut String, show_locs: bool) {
        let mut p = Printer {
            body: &self.body,
            show_locs,
            out,
        };
        let entry = self.body.entry();
        p.out.push_str("func @");
        p.out.push_str(&self.name);
        p.out.push('(');
        p.values(self.body.params(entry));
        p.out.push(')');
        match self.rets.as_slice() {
            [] => {}
            [t] => {
                p.out.push_str(" -> ");
                push_ty(p.out, *t);
            }
            ts => {
                p.out.push_str(" -> (");
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 {
                        p.out.push_str(", ");
                    }
                    push_ty(p.out, *t);
                }
                p.out.push(')');
            }
        }
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

impl Module {
    /// Canonical text. With `show_locs` off, op locations and function files are left out.
    pub fn render(&self, show_locs: bool) -> String {
        let mut out = String::new();
        if self.space != SpaceCfg::default() {
            write!(
                out,
                "memspace default ptr {} addr {}\n\n",
                self.space.ptr_bits, self.space.addr_bits
            )
            .unwrap();
        }
        for (i, f) in self.funcs.iter().enumerate() {
            if i > 0 {
                out.push('\n');
            }
            f.render_into(&mut out, show_locs);
        }
        out
    }
}
