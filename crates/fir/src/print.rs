//! Prints modules in canonical text, mirroring `spec/Fir/Print.lean` byte for byte. The parser
//! reads the output back unchanged.

use std::fmt::Write;

use crate::body::{Body, OpId, Operand, RegionId, ValueId};
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

/// The division modifiers: one when it covers both edge cases, otherwise two.
fn div_suffix(signed: bool, zero: Edge, ovf: Edge) -> String {
    let one = !signed
        || (zero, ovf) == (Edge::Ub, Edge::Ub)
        || (zero, ovf) == (Edge::Trap, Edge::Trap)
        || (zero, ovf) == (Edge::Total, Edge::Wrap);
    if one {
        zero.name().into()
    } else {
        format!("{}.{}", zero.name(), ovf.name())
    }
}

impl OpKind {
    /// The op's name with its modifiers, as written in text.
    pub fn name(&self) -> String {
        use OpKind::*;
        match self {
            Const(_) => "int.const".into(),
            Poison => "poison".into(),
            Freeze => "freeze".into(),
            Copy => "copy".into(),
            Select => "select".into(),
            Arith(op, o) => {
                let n = match op {
                    ArithOp::Add => "add",
                    ArithOp::Sub => "sub",
                    ArithOp::Mul => "mul",
                };
                format!("int.{n}.{}", o.suffix())
            }
            Bit(op) => match op {
                BitOp::And => "int.and",
                BitOp::Or => "int.or",
                BitOp::Xor => "int.xor",
            }
            .into(),
            Div(op, z, o) => {
                let n = match op {
                    DivOp::DivS => "div.s",
                    DivOp::DivU => "div.u",
                    DivOp::RemS => "rem.s",
                    DivOp::RemU => "rem.u",
                };
                format!("int.{n}.{}", div_suffix(op.signed(), *z, *o))
            }
            Shift(op, e) => {
                let n = match op {
                    ShiftOp::Shl => "shl",
                    ShiftOp::ShrU => "shr.u",
                    ShiftOp::ShrS => "shr.s",
                };
                format!("int.{n}.{}", e.name())
            }
            Cmp(p) => format!("int.cmp.{}", p.name()),
            Zext => "int.zext".into(),
            Sext => "int.sext".into(),
            Trunc(m) => format!(
                "int.trunc.{}",
                match m {
                    TruncMode::Wrap => "wrap",
                    TruncMode::Nsw => "nsw",
                    TruncMode::Nuw => "nuw",
                }
            ),
            If => "cf.if".into(),
            Loop { .. } => "cf.loop".into(),
            Yield => "cf.yield".into(),
            Break => "cf.break".into(),
            Continue => "cf.continue".into(),
            Ret => "func.ret".into(),
            MemStack { .. } => "mem.stack".into(),
            MemAlloc { fail, .. } => match fail {
                AllocFail::Null => "mem.alloc.null",
                AllocFail::Trap => "mem.alloc.trap",
            }
            .into(),
            MemFree { .. } => "mem.free".into(),
            Load { .. } => "mem.load".into(),
            Store { .. } => "mem.store".into(),
            PtrOffset { inbounds } => if *inbounds {
                "ptr.offset.inbounds"
            } else {
                "ptr.offset.wrap"
            }
            .into(),
            PtrAddr => "ptr.addr".into(),
            PtrExpose => "ptr.expose".into(),
            PtrFromExposed => "ptr.from_exposed".into(),
            PtrWithAddr => "ptr.with_addr".into(),
            PtrNull => "ptr.null".into(),
            PtrCmp(p) => format!("ptr.cmp.{}", p.name()),
            Call { .. } => "func.call".into(),
        }
    }
}

impl std::fmt::Display for TrustedFact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.fact {
            Fact::RangeS(lo, hi) => write!(f, "range.s({lo}, {hi})"),
            Fact::RangeU(lo, hi) => write!(f, "range.u({lo}, {hi})"),
            Fact::NonNull => f.write_str("nonnull"),
            Fact::Align(n) => write!(f, "align({n})"),
            Fact::NoAlias => f.write_str("noalias"),
            Fact::ReadOnly => f.write_str("readonly"),
        }?;
        write!(f, " {}", self.trust.name())
    }
}

struct Printer<'a> {
    body: &'a Body,
    show_locs: bool,
    out: String,
}

fn commas(items: impl IntoIterator<Item = String>) -> String {
    items.into_iter().collect::<Vec<_>>().join(", ")
}

impl Printer<'_> {
    fn value(&self, v: ValueId) -> String {
        let b = self.body;
        let facts = b.facts(v);
        let facts = if facts.is_empty() {
            String::new()
        } else {
            format!(" [{}]", commas(facts.iter().map(|f| f.to_string())))
        };
        format!("%{}: {}{facts}", b.name(v), b.ty(v))
    }

    fn operand(&self, o: &Operand) -> String {
        match o {
            Operand::Value(v) => format!("%{}", self.body.name(*v)),
            Operand::Hole { name, ty } => format!("?{name}: {ty}"),
        }
    }

    fn loc(&self, loc: Option<Loc>) -> String {
        match loc {
            Some(l) if self.show_locs => format!(" @{}:{}", l.line, l.col),
            _ => String::new(),
        }
    }

    fn region(&mut self, indent: &str, r: RegionId) {
        self.out.push_str("{\n");
        let inner = format!("{indent}  ");
        for op in self.body.ops(r) {
            self.op(&inner, op);
        }
        self.out.push_str(indent);
        self.out.push('}');
    }

    fn op(&mut self, indent: &str, op: OpId) {
        let b = self.body;
        self.out.push_str(indent);
        if b.results(op).len() > 0 {
            let rs = commas(b.results(op).map(|v| self.value(v)));
            write!(self.out, "{rs} = ").unwrap();
        }
        let loc = self.loc(b.loc(op));
        let args = commas(b.operands(op).iter().map(|o| self.operand(o)));
        let kind = b.kind(op);
        match (kind, b.regions(op)) {
            (OpKind::Const(n), _) => write!(self.out, "int.const {n}{loc}").unwrap(),
            (OpKind::If, &[thn, els]) => {
                write!(self.out, "cf.if {args}{loc} ").unwrap();
                self.region(indent, thn);
                if !b.is_empty(els) {
                    self.out.push_str(" else ");
                    self.region(indent, els);
                }
            }
            (OpKind::Loop { progress }, &[body]) => {
                let prog = if *progress { " progress" } else { "" };
                let iter = if b.params(body).len() == 0 {
                    String::new()
                } else {
                    let items = b
                        .params(body)
                        .zip(b.operands(op))
                        .map(|(p, a)| format!("{} = {}", self.value(p), self.operand(a)));
                    format!(" iter({})", commas(items))
                };
                write!(self.out, "cf.loop{prog}{iter}{loc} ").unwrap();
                self.region(indent, body);
            }
            (OpKind::MemStack { size, align }, _) => {
                write!(self.out, "mem.stack {size}, align {align}{loc}").unwrap()
            }
            (OpKind::MemAlloc { family, align, .. }, _) => write!(
                self.out,
                "{} {family} {args}, align {align}{loc}",
                kind.name()
            )
            .unwrap(),
            (OpKind::MemFree { family }, _) => {
                write!(self.out, "mem.free {family} {args}{loc}").unwrap()
            }
            (OpKind::Load { align }, _) => {
                write!(self.out, "mem.load {args}, align {align}{loc}").unwrap()
            }
            (OpKind::Store { ty, align }, _) => {
                write!(self.out, "mem.store {ty} {args}, align {align}{loc}").unwrap()
            }
            (OpKind::Call { callee }, _) => {
                write!(self.out, "func.call @{callee}({args}){loc}").unwrap()
            }
            (k, _) => {
                let sep = if args.is_empty() { "" } else { " " };
                write!(self.out, "{}{sep}{args}{loc}", k.name()).unwrap()
            }
        }
        self.out.push('\n');
    }
}

impl Func {
    pub fn render(&self, show_locs: bool) -> String {
        let mut p = Printer {
            body: &self.body,
            show_locs,
            out: String::new(),
        };
        let entry = self.body.entry();
        let params = commas(self.body.params(entry).map(|v| p.value(v)));
        let rets = match self.rets.as_slice() {
            [] => String::new(),
            [t] => format!(" -> {t}"),
            ts => format!(" -> ({})", commas(ts.iter().map(|t| t.to_string()))),
        };
        let file = match &self.file {
            Some(s) if show_locs => format!(" loc \"{s}\""),
            _ => String::new(),
        };
        write!(p.out, "func @{}({params}){rets}{file} ", self.name).unwrap();
        p.region("", entry);
        p.out.push('\n');
        p.out
    }
}

impl Module {
    /// Canonical text. With `show_locs` off, op locations and function files are left out.
    pub fn render(&self, show_locs: bool) -> String {
        let header = if self.space == SpaceCfg::default() {
            String::new()
        } else {
            format!(
                "memspace default ptr {} addr {}\n\n",
                self.space.ptr_bits, self.space.addr_bits
            )
        };
        header
            + &self
                .funcs
                .iter()
                .map(|f| f.render(show_locs))
                .collect::<Vec<_>>()
                .join("\n")
    }
}
