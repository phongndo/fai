//! Parses FIR text into a [`Module`], mirroring `spec/Fir/Parse.lean`.
//!
//! The Lean parser keeps value names as text and leaves scoping to its verifier. This parser
//! builds the arena directly, so it resolves each use to its definition as it goes, with the
//! verifier's rules and messages: a value is defined once per function, and visible after its
//! definition in the same region or a nested one.

use std::collections::{HashMap, HashSet};

use num_bigint::{BigInt, Sign};

use crate::body::{Body, Operand, RegionId, ValueId, ValueSpec};
use crate::ir::*;
use crate::lex::{Tok, Token, lex};

pub fn parse_module(input: &str) -> Result<Module, String> {
    let toks = lex(input)?;
    Parser {
        toks,
        pos: 0,
        scopes: Vec::new(),
        defined: HashSet::new(),
    }
    .module()
}

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    /// Visible values, one frame per enclosing region.
    scopes: Vec<HashMap<String, ValueId>>,
    /// Every name defined so far in the current function.
    defined: HashSet<String>,
}

type PResult<T> = Result<T, String>;

impl Parser {
    fn peek_token(&self) -> &Token {
        &self.toks[self.pos.min(self.toks.len() - 1)]
    }

    fn peek(&self) -> &Tok {
        &self.peek_token().tok
    }

    fn next(&mut self) -> Tok {
        let t = self.peek().clone();
        self.pos += 1;
        t
    }

    fn fail<T>(&self, msg: impl std::fmt::Display) -> PResult<T> {
        let t = self.peek_token();
        Err(format!("{}:{}: {msg}", t.line, t.col))
    }

    fn expect_sym(&mut self, sym: &str) -> PResult<()> {
        if *self.peek() == Tok::Sym(sym_static(sym)) {
            self.next();
            Ok(())
        } else {
            self.fail(format!(
                "expected '{sym}' but found {}",
                self.peek().describe()
            ))
        }
    }

    fn try_sym(&mut self, sym: &str) -> bool {
        let hit = *self.peek() == Tok::Sym(sym_static(sym));
        if hit {
            self.next();
        }
        hit
    }

    fn try_ident(&mut self, name: &str) -> bool {
        let hit = matches!(self.peek(), Tok::Ident(s) if s == name);
        if hit {
            self.next();
        }
        hit
    }

    fn ident(&mut self) -> PResult<String> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                self.next();
                Ok(s)
            }
            t => self.fail(format!("expected a name but found {}", t.describe())),
        }
    }

    fn value_name(&mut self) -> PResult<String> {
        match self.peek().clone() {
            Tok::Value(s) => {
                self.next();
                Ok(s)
            }
            t => self.fail(format!("expected a %value but found {}", t.describe())),
        }
    }

    fn int(&mut self) -> PResult<BigInt> {
        match self.peek().clone() {
            Tok::Int(n) => {
                self.next();
                Ok(n)
            }
            t => self.fail(format!("expected an integer but found {}", t.describe())),
        }
    }

    /// A non-negative integer that fits in `N`. Lean's naturals are unbounded; here sizes and
    /// alignments are 64-bit, and widths and memory-space sizes 32-bit.
    fn nat<N: for<'a> TryFrom<&'a BigInt>>(&mut self) -> PResult<N> {
        let n = self.int()?;
        if n.sign() == Sign::Minus {
            return self.fail("expected a non-negative integer");
        }
        N::try_from(&n).or_else(|_| self.fail(format!("{n} is too large")))
    }

    /// One or more comma-separated items.
    fn sep_by1<T>(&mut self, p: impl Fn(&mut Self) -> PResult<T>) -> PResult<Vec<T>> {
        let mut items = vec![p(self)?];
        while self.try_sym(",") {
            items.push(p(self)?);
        }
        Ok(items)
    }

    /// Comma-separated items, possibly none, ended by `close`.
    fn sep_by<T>(&mut self, p: impl Fn(&mut Self) -> PResult<T>, close: &str) -> PResult<Vec<T>> {
        if self.try_sym(close) {
            return Ok(Vec::new());
        }
        let items = self.sep_by1(p)?;
        self.expect_sym(close)?;
        Ok(items)
    }

    fn ty(&mut self) -> PResult<Ty> {
        let s = self.ident()?;
        if s == "ptr" {
            return Ok(Ty::Ptr);
        }
        let width = |rest: &str| {
            rest.parse::<u32>()
                .ok()
                .filter(|_| rest.bytes().all(|b| b.is_ascii_digit()))
        };
        match (s.chars().next(), width(s.get(1..).unwrap_or(""))) {
            (Some('i'), Some(w)) => Ok(Ty::Int(w)),
            (Some('b'), Some(w)) => Ok(Ty::Byte(w)),
            _ => self.fail(format!("unknown type '{s}'")),
        }
    }

    fn trust(&mut self) -> PResult<Trust> {
        match self.ident()?.as_str() {
            "assume" => Ok(Trust::Assume),
            "check" => Ok(Trust::Check),
            "proved" => Ok(Trust::Proved),
            s => self.fail(format!("expected assume, check, or proved but found '{s}'")),
        }
    }

    fn range(&mut self) -> PResult<(BigInt, BigInt)> {
        self.expect_sym("(")?;
        let lo = self.int()?;
        self.expect_sym(",")?;
        let hi = self.int()?;
        self.expect_sym(")")?;
        Ok((lo, hi))
    }

    fn fact(&mut self) -> PResult<TrustedFact> {
        let name = self.ident()?;
        let fact = match name.as_str() {
            "range.s" => {
                let (lo, hi) = self.range()?;
                Fact::RangeS(lo, hi)
            }
            "range.u" => {
                let (lo, hi) = self.range()?;
                Fact::RangeU(lo, hi)
            }
            "nonnull" => Fact::NonNull,
            "noalias" => Fact::NoAlias,
            "readonly" => Fact::ReadOnly,
            "align" => {
                self.expect_sym("(")?;
                let n = self.nat()?;
                self.expect_sym(")")?;
                Fact::Align(n)
            }
            _ => return self.fail(format!("unknown fact '{name}'")),
        };
        Ok(TrustedFact {
            fact,
            trust: self.trust()?,
        })
    }

    fn result(&mut self) -> PResult<ValueSpec> {
        let name = self.value_name()?;
        self.expect_sym(":")?;
        let ty = self.ty()?;
        let facts = if self.try_sym("[") {
            self.sep_by(Self::fact, "]")?
        } else {
            Vec::new()
        };
        Ok(ValueSpec { name, ty, facts })
    }

    fn operand(&mut self) -> PResult<Operand> {
        match self.peek().clone() {
            Tok::Value(name) => {
                let found = self.scopes.iter().rev().find_map(|s| s.get(&name).copied());
                match found {
                    Some(v) => {
                        self.next();
                        Ok(Operand::Value(v))
                    }
                    None => self.fail(format!("%{name} is not defined here")),
                }
            }
            Tok::Hole(name) => {
                self.next();
                self.expect_sym(":")?;
                Ok(Operand::Hole {
                    name,
                    ty: self.ty()?,
                })
            }
            t => self.fail(format!("expected an operand but found {}", t.describe())),
        }
    }

    /// Exactly `n` comma-separated operands.
    fn operands(&mut self, n: usize) -> PResult<Vec<Operand>> {
        let mut acc = Vec::with_capacity(n);
        for i in 0..n {
            if i > 0 {
                self.expect_sym(",")?;
            }
            acc.push(self.operand()?);
        }
        Ok(acc)
    }

    /// Zero or more comma-separated operands (for terminators).
    fn variadic(&mut self) -> PResult<Vec<Operand>> {
        match self.peek() {
            Tok::Value(_) | Tok::Hole(_) => self.sep_by1(Self::operand),
            _ => Ok(Vec::new()),
        }
    }

    /// `, align N`
    fn align_arg(&mut self) -> PResult<u64> {
        self.expect_sym(",")?;
        if !self.try_ident("align") {
            return self.fail("expected 'align'");
        }
        self.nat()
    }

    fn opt_loc(&mut self) -> Option<Loc> {
        match *self.peek() {
            Tok::Loc(line, col) => {
                self.next();
                Some(Loc { line, col })
            }
            _ => None,
        }
    }

    /// Make values visible in the innermost scope.
    fn define(&mut self, body: &Body, values: impl Iterator<Item = ValueId>) -> PResult<()> {
        for v in values {
            let name = body.name(v);
            if !self.defined.insert(name.to_owned()) {
                return self.fail(format!("%{name} is defined more than once"));
            }
            self.scopes
                .last_mut()
                .expect("inside a region")
                .insert(name.to_owned(), v);
        }
        Ok(())
    }

    /// Parse `{ ops }` into `region`, in a new scope that first defines its parameters.
    fn region(&mut self, body: &mut Body, region: RegionId) -> PResult<()> {
        self.expect_sym("{")?;
        self.scopes.push(HashMap::new());
        self.define(body, body.params(region))?;
        while !self.try_sym("}") {
            if *self.peek() == Tok::Eof {
                return self.fail("expected '}'");
            }
            self.op(body, region)?;
        }
        self.scopes.pop();
        Ok(())
    }

    fn op(&mut self, body: &mut Body, region: RegionId) -> PResult<()> {
        let results = match self.peek() {
            Tok::Value(_) => {
                let rs = self.sep_by1(Self::result)?;
                self.expect_sym("=")?;
                rs
            }
            _ => Vec::new(),
        };
        let name = self.ident()?;
        let Some(kind) = op_kind(&name) else {
            return self.fail(format!("unknown op '{name}'"));
        };
        let op = match kind {
            OpKind::Const(_) => {
                let n = self.int()?;
                let loc = self.opt_loc();
                body.append_op(region, OpKind::Const(n), [], results, [], loc)
            }
            OpKind::MemStack { .. } => {
                let size = self.nat()?;
                let align = self.align_arg()?;
                let loc = self.opt_loc();
                body.append_op(
                    region,
                    OpKind::MemStack { size, align },
                    [],
                    results,
                    [],
                    loc,
                )
            }
            OpKind::MemAlloc { fail, .. } => {
                let family = self.ident()?;
                let n = self.operand()?;
                let align = self.align_arg()?;
                let loc = self.opt_loc();
                body.append_op(
                    region,
                    OpKind::MemAlloc {
                        fail,
                        family,
                        align,
                    },
                    [n],
                    results,
                    [],
                    loc,
                )
            }
            OpKind::MemFree { .. } => {
                let family = self.ident()?;
                let p = self.operand()?;
                let loc = self.opt_loc();
                body.append_op(region, OpKind::MemFree { family }, [p], results, [], loc)
            }
            OpKind::Load { .. } => {
                let p = self.operand()?;
                let align = self.align_arg()?;
                let loc = self.opt_loc();
                body.append_op(region, OpKind::Load { align }, [p], results, [], loc)
            }
            OpKind::Store { .. } => {
                let ty = self.ty()?;
                let v = self.operand()?;
                self.expect_sym(",")?;
                let p = self.operand()?;
                let align = self.align_arg()?;
                let loc = self.opt_loc();
                body.append_op(
                    region,
                    OpKind::Store { ty, align },
                    [v, p],
                    results,
                    [],
                    loc,
                )
            }
            OpKind::Call { .. } => {
                let callee = match self.next() {
                    Tok::Global(s) => s,
                    t => {
                        self.pos -= 1;
                        return self.fail(format!(
                            "expected a function name like @f but found {}",
                            t.describe()
                        ));
                    }
                };
                self.expect_sym("(")?;
                let args = self.sep_by(Self::operand, ")")?;
                let loc = self.opt_loc();
                body.append_op(region, OpKind::Call { callee }, args, results, [], loc)
            }
            OpKind::If => {
                let c = self.operand()?;
                let loc = self.opt_loc();
                let op = body.append_op(region, OpKind::If, [c], results, [vec![], vec![]], loc);
                let (thn, els) = (body.regions(op)[0], body.regions(op)[1]);
                self.region(body, thn)?;
                if self.try_ident("else") {
                    self.region(body, els)?;
                }
                op
            }
            OpKind::Loop { .. } => {
                let progress = self.try_ident("progress");
                let iter = if self.try_ident("iter") {
                    self.expect_sym("(")?;
                    self.sep_by(Self::iter_arg, ")")?
                } else {
                    Vec::new()
                };
                let loc = self.opt_loc();
                let (params, inits): (Vec<_>, Vec<_>) = iter.into_iter().unzip();
                let op = body.append_op(
                    region,
                    OpKind::Loop { progress },
                    inits,
                    results,
                    [params],
                    loc,
                );
                let inner = body.regions(op)[0];
                self.region(body, inner)?;
                op
            }
            k => {
                let args = match arity(&k) {
                    Some(n) => self.operands(n)?,
                    None => self.variadic()?,
                };
                let loc = self.opt_loc();
                body.append_op(region, k, args, results, [], loc)
            }
        };
        self.define(body, body.results(op))
    }

    /// `%name: type = %init`
    fn iter_arg(&mut self) -> PResult<(ValueSpec, Operand)> {
        let r = self.result()?;
        self.expect_sym("=")?;
        Ok((r, self.operand()?))
    }

    fn func(&mut self) -> PResult<Func> {
        if !self.try_ident("func") {
            return self.fail("expected 'func'");
        }
        let name = match self.next() {
            Tok::Global(s) => s,
            t => {
                self.pos -= 1;
                return self.fail(format!(
                    "expected a function name like @main but found {}",
                    t.describe()
                ));
            }
        };
        self.expect_sym("(")?;
        let params = self.sep_by(Self::result, ")")?;
        let rets = if self.try_sym("->") {
            if self.try_sym("(") {
                self.sep_by(Self::ty, ")")?
            } else {
                vec![self.ty()?]
            }
        } else {
            Vec::new()
        };
        let file = if self.try_ident("loc") {
            match self.next() {
                Tok::Str(s) => Some(s),
                t => {
                    self.pos -= 1;
                    return self.fail(format!(
                        "expected a file name string but found {}",
                        t.describe()
                    ));
                }
            }
        } else {
            None
        };
        let mut body = Body::new(params);
        self.defined.clear();
        let entry = body.entry();
        self.region(&mut body, entry)?;
        Ok(Func {
            name,
            rets,
            file,
            body,
        })
    }

    /// `memspace default ptr 64 addr 64`
    fn memspace(&mut self) -> PResult<SpaceCfg> {
        let name = self.ident()?;
        if name != "default" {
            return self.fail("only the default memory space can be declared for now");
        }
        if !self.try_ident("ptr") {
            return self.fail("expected 'ptr'");
        }
        let ptr_bits = self.nat()?;
        if !self.try_ident("addr") {
            return self.fail("expected 'addr'");
        }
        Ok(SpaceCfg {
            ptr_bits,
            addr_bits: self.nat()?,
        })
    }

    fn module(mut self) -> PResult<Module> {
        let mut m = Module::default();
        while *self.peek() != Tok::Eof {
            if self.try_ident("memspace") {
                m.space = self.memspace()?;
            } else {
                m.funcs.push(self.func()?);
            }
        }
        Ok(m)
    }
}

/// The lexer's interned spelling of a symbol, so tokens compare by value.
fn sym_static(sym: &str) -> &'static str {
    ["(", ")", "{", "}", "[", "]", ",", ":", "=", "->"]
        .into_iter()
        .find(|s| *s == sym)
        .expect("a known symbol")
}

fn ovf(m: &[&str]) -> Option<Ovf> {
    Some(match m {
        ["wrap"] => Ovf::Wrap,
        ["nsw"] => Ovf::Nsw,
        ["nuw"] => Ovf::Nuw,
        ["nsw", "nuw"] => Ovf::NswNuw,
        ["s", "trap"] => Ovf::Trap(true),
        ["u", "trap"] => Ovf::Trap(false),
        ["s", "sat"] => Ovf::Sat(true),
        ["u", "sat"] => Ovf::Sat(false),
        ["s", "ub"] => Ovf::Ub(true),
        ["u", "ub"] => Ovf::Ub(false),
        _ => return None,
    })
}

fn zero_edge(s: &str) -> Option<Edge> {
    Some(match s {
        "ub" => Edge::Ub,
        "trap" => Edge::Trap,
        "total" => Edge::Total,
        _ => return None,
    })
}

fn ovf_edge(s: &str) -> Option<Edge> {
    Some(match s {
        "ub" => Edge::Ub,
        "trap" => Edge::Trap,
        "wrap" => Edge::Wrap,
        _ => return None,
    })
}

/// `(zero, overflow)` edges. One modifier covers both cases.
fn div_edges(signed: bool, m: &[&str]) -> Option<(Edge, Edge)> {
    match m {
        [z] => {
            let z = zero_edge(z)?;
            Some((z, if z == Edge::Total { Edge::Wrap } else { z }))
        }
        [z, o] if signed => Some((zero_edge(z)?, ovf_edge(o)?)),
        _ => None,
    }
}

fn shift_edge(m: &[&str]) -> Option<ShiftEdge> {
    Some(match m {
        ["ub"] => ShiftEdge::Ub,
        ["trap"] => ShiftEdge::Trap,
        ["mask"] => ShiftEdge::Mask,
        ["total"] => ShiftEdge::Total,
        _ => return None,
    })
}

fn pred(s: &str) -> Option<Pred> {
    Some(match s {
        "eq" => Pred::Eq,
        "ne" => Pred::Ne,
        "slt" => Pred::Slt,
        "sle" => Pred::Sle,
        "sgt" => Pred::Sgt,
        "sge" => Pred::Sge,
        "ult" => Pred::Ult,
        "ule" => Pred::Ule,
        "ugt" => Pred::Ugt,
        "uge" => Pred::Uge,
        _ => return None,
    })
}

/// Decode an op name with its modifiers. Ops with immediates get placeholders the parser fills.
pub fn op_kind(name: &str) -> Option<OpKind> {
    use OpKind::*;
    let parts: Vec<&str> = name.split('.').collect();
    Some(match parts.as_slice() {
        ["int", "const"] => Const(BigInt::ZERO),
        ["poison"] => Poison,
        ["freeze"] => Freeze,
        ["copy"] => Copy,
        ["select"] => Select,
        ["int", "add", m @ ..] => Arith(ArithOp::Add, ovf(m)?),
        ["int", "sub", m @ ..] => Arith(ArithOp::Sub, ovf(m)?),
        ["int", "mul", m @ ..] => Arith(ArithOp::Mul, ovf(m)?),
        ["int", "and"] => Bit(BitOp::And),
        ["int", "or"] => Bit(BitOp::Or),
        ["int", "xor"] => Bit(BitOp::Xor),
        ["int", "div", "s", m @ ..] => div(DivOp::DivS, m)?,
        ["int", "div", "u", m @ ..] => div(DivOp::DivU, m)?,
        ["int", "rem", "s", m @ ..] => div(DivOp::RemS, m)?,
        ["int", "rem", "u", m @ ..] => div(DivOp::RemU, m)?,
        ["int", "shl", m @ ..] => Shift(ShiftOp::Shl, shift_edge(m)?),
        ["int", "shr", "u", m @ ..] => Shift(ShiftOp::ShrU, shift_edge(m)?),
        ["int", "shr", "s", m @ ..] => Shift(ShiftOp::ShrS, shift_edge(m)?),
        ["int", "cmp", p] => Cmp(pred(p)?),
        ["int", "zext"] => Zext,
        ["int", "sext"] => Sext,
        ["int", "trunc", "wrap"] => Trunc(TruncMode::Wrap),
        ["int", "trunc", "nsw"] => Trunc(TruncMode::Nsw),
        ["int", "trunc", "nuw"] => Trunc(TruncMode::Nuw),
        ["cf", "if"] => If,
        ["cf", "loop"] => Loop { progress: false },
        ["cf", "yield"] => Yield,
        ["cf", "break"] => Break,
        ["cf", "continue"] => Continue,
        ["func", "ret"] => Ret,
        ["ptr", "offset", "inbounds"] => PtrOffset { inbounds: true },
        ["ptr", "offset", "wrap"] => PtrOffset { inbounds: false },
        ["ptr", "addr"] => PtrAddr,
        ["ptr", "expose"] => PtrExpose,
        ["ptr", "from_exposed"] => PtrFromExposed,
        ["ptr", "with_addr"] => PtrWithAddr,
        ["ptr", "null"] => PtrNull,
        ["ptr", "cmp", p] => PtrCmp(pred(p)?),
        ["mem", "stack"] => MemStack { size: 0, align: 1 },
        ["mem", "alloc", "null"] => MemAlloc {
            fail: AllocFail::Null,
            family: String::new(),
            align: 1,
        },
        ["mem", "alloc", "trap"] => MemAlloc {
            fail: AllocFail::Trap,
            family: String::new(),
            align: 1,
        },
        ["mem", "free"] => MemFree {
            family: String::new(),
        },
        ["mem", "load"] => Load { align: 1 },
        ["mem", "store"] => Store {
            ty: Ty::Ptr,
            align: 1,
        },
        ["func", "call"] => Call {
            callee: String::new(),
        },
        _ => return None,
    })
}

fn div(op: DivOp, m: &[&str]) -> Option<OpKind> {
    let (z, o) = div_edges(op.signed(), m)?;
    Some(OpKind::Div(op, z, o))
}

/// How many operands an op without regions takes, or `None` if variadic.
fn arity(k: &OpKind) -> Option<usize> {
    use OpKind::*;
    match k {
        Const(_) | Poison | PtrNull => Some(0),
        Freeze | Copy | Zext | Sext | Trunc(_) | PtrAddr | PtrExpose | PtrFromExposed => Some(1),
        Select => Some(3),
        Yield | Break | Continue | Ret => None,
        _ => Some(2),
    }
}
