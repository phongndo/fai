//! Parses FIR text into a [`Module`], mirroring `spec/Fir/Parse.lean`.
//!
//! The Lean parser keeps value names as text and leaves scoping to its verifier. This parser
//! builds the arena directly, so it resolves each use to its definition as it goes, with the
//! verifier's rules and messages: a value is defined once per function, and visible after its
//! definition in the same region or a nested one.

use num_bigint::Sign;
use rustc_hash::FxHashMap;

use crate::body::{Body, IntId, Operand, RegionId, StrId, ValueId, ValueSpec};
use crate::ir::*;
use crate::lex::{Lexer, Sym, Tok, Token, int_value};

pub fn parse_module(input: &str) -> Result<Module, String> {
    let mut p = Parser::new(input, true)?;
    match p.module() {
        // Lean resolves names only after parsing, so a syntax error anywhere comes first.
        Err(e) if p.name_error => match Parser::new(input, false)?.module() {
            Err(syntax) => Err(syntax),
            Ok(_) => Err(e),
        },
        r => r,
    }
}

struct Parser<'a> {
    lexer: Lexer<'a>,
    /// Whether to resolve names. Off only to look for a syntax error after a name error.
    resolve: bool,
    /// Whether parsing stopped at a name error.
    name_error: bool,
    /// The body of the function being parsed.
    body: Body,
    /// The next token.
    cur: Token<'a>,
    /// Every name defined so far in the current function, with its value and whether it is
    /// visible here.
    names: FxHashMap<&'a str, (ValueId, bool)>,
    /// The visible names, in definition order, so a region's names can be hidden when it ends.
    undo: Vec<&'a str>,
    /// Names of results waiting to be defined once their op is parsed (a stack, since ops with
    /// regions nest).
    pending: Vec<&'a str>,
    /// Scratch buffers for the op being parsed.
    operands: Vec<Operand>,
    results: Vec<ValueSpec<'a>>,
}

type PResult<T> = Result<T, String>;

/// Bodies with fewer ops than this are copied out of the parser's reusable builder.
const SMALL_BODY: usize = 1 << 12;

impl<'a> Parser<'a> {
    fn new(input: &'a str, resolve: bool) -> PResult<Parser<'a>> {
        let mut lexer = Lexer::new(input);
        let cur = lexer.next_token()?;
        Ok(Parser {
            lexer,
            resolve,
            name_error: false,
            body: Body::new(),
            cur,
            names: FxHashMap::default(),
            undo: Vec::new(),
            pending: Vec::new(),
            operands: Vec::new(),
            results: Vec::new(),
        })
    }

    /// Fail with a name error, which a syntax error later in the input outranks.
    fn fail_name<T>(&mut self, msg: impl std::fmt::Display) -> PResult<T> {
        self.name_error = true;
        self.fail(msg)
    }

    fn peek(&self) -> Tok<'a> {
        self.cur.tok
    }

    fn bump(&mut self) -> PResult<()> {
        self.cur = self.lexer.next_token()?;
        Ok(())
    }

    /// Fail at the next token. A lexing error later in the input wins, as in Lean, which lexes
    /// the whole input before parsing.
    fn fail<T>(&self, msg: impl std::fmt::Display) -> PResult<T> {
        if let Some(e) = self.lexer.clone().first_error() {
            return Err(e);
        }
        Err(format!("{}:{}: {msg}", self.cur.line, self.cur.col))
    }

    fn expect_sym(&mut self, sym: Sym) -> PResult<()> {
        if self.peek() == Tok::Sym(sym) {
            self.bump()
        } else {
            let found = self.peek().describe();
            self.fail(format!("expected '{}' but found {found}", sym.text()))
        }
    }

    fn try_sym(&mut self, sym: Sym) -> PResult<bool> {
        let hit = self.peek() == Tok::Sym(sym);
        if hit {
            self.bump()?;
        }
        Ok(hit)
    }

    fn try_ident(&mut self, name: &str) -> PResult<bool> {
        let hit = matches!(self.peek(), Tok::Ident(s) if s == name);
        if hit {
            self.bump()?;
        }
        Ok(hit)
    }

    fn ident(&mut self) -> PResult<&'a str> {
        match self.peek() {
            Tok::Ident(s) => {
                self.bump()?;
                Ok(s)
            }
            t => self.fail(format!("expected a name but found {}", t.describe())),
        }
    }

    fn value_name(&mut self) -> PResult<&'a str> {
        match self.peek() {
            Tok::Value(s) => {
                self.bump()?;
                Ok(s)
            }
            t => self.fail(format!("expected a %value but found {}", t.describe())),
        }
    }

    fn int_text(&mut self) -> PResult<&'a str> {
        match self.peek() {
            Tok::Int(s) => {
                self.bump()?;
                Ok(s)
            }
            t => self.fail(format!("expected an integer but found {}", t.describe())),
        }
    }

    /// An integer literal, stored in the body.
    fn int(&mut self) -> PResult<IntId> {
        let text = self.int_text()?;
        Ok(match text.parse::<i64>() {
            Ok(n) => self.body.add_small_int(n),
            Err(_) => self.body.add_int(int_value(text)),
        })
    }

    /// A non-negative integer that fits in `N`. Lean's naturals are unbounded; here sizes are
    /// 64-bit, and alignments, widths, and memory-space sizes 32-bit.
    fn nat<N: TryFrom<u64>>(&mut self) -> PResult<N> {
        let Tok::Int(text) = self.peek() else {
            return self.int_text().map(|_| unreachable!());
        };
        self.bump()?;
        if let Some(n) = text.parse::<u64>().ok().and_then(|n| N::try_from(n).ok()) {
            return Ok(n);
        }
        let n = int_value(text);
        if n.sign() == Sign::Minus {
            return self.fail("expected a non-negative integer");
        }
        match u64::try_from(&n).ok().and_then(|n| N::try_from(n).ok()) {
            Some(n) => Ok(n),
            None => self.fail(format!("{n} is too large")),
        }
    }

    /// One or more comma-separated items.
    fn sep_by1<T>(&mut self, p: impl Fn(&mut Self) -> PResult<T>) -> PResult<Vec<T>> {
        let mut items = vec![p(self)?];
        while self.try_sym(Sym::Comma)? {
            items.push(p(self)?);
        }
        Ok(items)
    }

    /// Comma-separated items, possibly none, ended by `close`.
    fn sep_by<T>(&mut self, p: impl Fn(&mut Self) -> PResult<T>, close: Sym) -> PResult<Vec<T>> {
        if self.try_sym(close)? {
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
        let rest = s.get(1..).unwrap_or("");
        let width = if !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()) {
            rest.parse::<u32>().ok()
        } else {
            None
        };
        match (s.as_bytes()[0], width) {
            (b'i', Some(w)) => Ok(Ty::Int(w)),
            (b'b', Some(w)) => Ok(Ty::Byte(w)),
            _ => self.fail(format!("unknown type '{s}'")),
        }
    }

    fn trust(&mut self) -> PResult<Trust> {
        match self.ident()? {
            "assume" => Ok(Trust::Assume),
            "check" => Ok(Trust::Check),
            "proved" => Ok(Trust::Proved),
            s => self.fail(format!("expected assume, check, or proved but found '{s}'")),
        }
    }

    fn range(&mut self) -> PResult<(IntId, IntId)> {
        self.expect_sym(Sym::LParen)?;
        let lo = self.int()?;
        self.expect_sym(Sym::Comma)?;
        let hi = self.int()?;
        self.expect_sym(Sym::RParen)?;
        Ok((lo, hi))
    }

    fn fact(&mut self) -> PResult<TrustedFact> {
        let name = self.ident()?;
        let fact = match name {
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
                self.expect_sym(Sym::LParen)?;
                let n = self.nat()?;
                self.expect_sym(Sym::RParen)?;
                Fact::Align(n)
            }
            _ => return self.fail(format!("unknown fact '{name}'")),
        };
        Ok(TrustedFact {
            fact,
            trust: self.trust()?,
        })
    }

    fn result(&mut self) -> PResult<ValueSpec<'a>> {
        let name = self.value_name()?;
        self.expect_sym(Sym::Colon)?;
        let ty = self.ty()?;
        let facts = if self.try_sym(Sym::LBracket)? {
            self.sep_by(Self::fact, Sym::RBracket)?
        } else {
            Vec::new()
        };
        Ok(ValueSpec { name, ty, facts })
    }

    fn operand(&mut self) -> PResult<Operand> {
        match self.peek() {
            Tok::Value(name) => match self.names.get(name) {
                Some(&(v, true)) => {
                    self.bump()?;
                    Ok(Operand::value(v))
                }
                _ if !self.resolve => {
                    self.bump()?;
                    Ok(Operand::value(ValueId::PLACEHOLDER))
                }
                _ => self.fail_name(format!("%{name} is not defined here")),
            },
            Tok::Hole(name) => {
                self.bump()?;
                self.expect_sym(Sym::Colon)?;
                let ty = self.ty()?;
                Ok(self.body.add_hole(name, ty))
            }
            t => self.fail(format!("expected an operand but found {}", t.describe())),
        }
    }

    /// Exactly `n` comma-separated operands, into the scratch buffer.
    fn operands(&mut self, n: usize) -> PResult<()> {
        for i in 0..n {
            if i > 0 {
                self.expect_sym(Sym::Comma)?;
            }
            let o = self.operand()?;
            self.operands.push(o);
        }
        Ok(())
    }

    /// Zero or more comma-separated operands (for terminators), into the scratch buffer.
    fn variadic(&mut self) -> PResult<()> {
        if matches!(self.peek(), Tok::Value(_) | Tok::Hole(_)) {
            loop {
                let o = self.operand()?;
                self.operands.push(o);
                if !self.try_sym(Sym::Comma)? {
                    break;
                }
            }
        }
        Ok(())
    }

    /// `, align N`
    fn align_arg(&mut self) -> PResult<u32> {
        self.expect_sym(Sym::Comma)?;
        if !self.try_ident("align")? {
            return self.fail("expected 'align'");
        }
        self.nat()
    }

    fn opt_loc(&mut self) -> PResult<Option<Loc>> {
        match self.peek() {
            Tok::Loc(line, col) => {
                self.bump()?;
                Ok(Some(Loc { line, col }))
            }
            _ => Ok(None),
        }
    }

    /// Make values visible, under the given names, until their region ends.
    fn define(&mut self, names: &[&'a str], values: impl Iterator<Item = ValueId>) -> PResult<()> {
        if !self.resolve {
            return Ok(());
        }
        for (&name, v) in names.iter().zip(values) {
            if self.names.insert(name, (v, true)).is_some() {
                return self.fail_name(format!("%{name} is defined more than once"));
            }
            self.undo.push(name);
        }
        Ok(())
    }

    /// Parse `{ ops }` into `region`, whose parameters are named `params`. Names defined inside
    /// are hidden again at the end.
    fn region(&mut self, region: RegionId, params: &[&'a str]) -> PResult<()> {
        self.expect_sym(Sym::LBrace)?;
        let mark = self.undo.len();
        self.define(params, self.body.params(region))?;
        while !self.try_sym(Sym::RBrace)? {
            if self.peek() == Tok::Eof {
                return self.fail("expected '}'");
            }
            self.op(region)?;
        }
        for name in self.undo.drain(mark..) {
            if let Some(e) = self.names.get_mut(name) {
                e.1 = false;
            }
        }
        Ok(())
    }

    fn op(&mut self, region: RegionId) -> PResult<()> {
        let pending = self.pending.len();
        self.results.clear();
        if let Tok::Value(_) = self.peek() {
            loop {
                let r = self.result()?;
                self.pending.push(r.name);
                self.results.push(r);
                if !self.try_sym(Sym::Comma)? {
                    break;
                }
            }
            self.expect_sym(Sym::Eq)?;
        }
        let name = self.ident()?;
        let Some(kind) = op_kind(name) else {
            return self.fail(format!("unknown op '{name}'"));
        };
        self.operands.clear();
        let op = match kind {
            OpKind::Const(_) => {
                let n = self.int()?;
                let loc = self.opt_loc()?;
                self.append(region, OpKind::Const(n), loc)
            }
            OpKind::MemStack { .. } => {
                let size = self.nat()?;
                let align = self.align_arg()?;
                let loc = self.opt_loc()?;
                self.append(region, OpKind::MemStack { size, align }, loc)
            }
            OpKind::MemAlloc { fail, .. } => {
                let family = self.ident()?;
                let family = self.body.add_str(family);
                self.operands(1)?;
                let align = self.align_arg()?;
                let loc = self.opt_loc()?;
                let kind = OpKind::MemAlloc {
                    fail,
                    family,
                    align,
                };
                self.append(region, kind, loc)
            }
            OpKind::MemFree { .. } => {
                let family = self.ident()?;
                let family = self.body.add_str(family);
                self.operands(1)?;
                let loc = self.opt_loc()?;
                self.append(region, OpKind::MemFree { family }, loc)
            }
            OpKind::Load { .. } => {
                self.operands(1)?;
                let align = self.align_arg()?;
                let loc = self.opt_loc()?;
                self.append(region, OpKind::Load { align }, loc)
            }
            OpKind::Store { .. } => {
                let ty = self.ty()?;
                self.operands(2)?;
                let align = self.align_arg()?;
                let loc = self.opt_loc()?;
                self.append(region, OpKind::Store { ty, align }, loc)
            }
            OpKind::Call { .. } => {
                let callee = match self.peek() {
                    Tok::Global(s) => {
                        self.bump()?;
                        self.body.add_str(s)
                    }
                    t => {
                        return self.fail(format!(
                            "expected a function name like @f but found {}",
                            t.describe()
                        ));
                    }
                };
                self.expect_sym(Sym::LParen)?;
                if !self.try_sym(Sym::RParen)? {
                    self.variadic_until_close()?;
                }
                let loc = self.opt_loc()?;
                self.append(region, OpKind::Call { callee }, loc)
            }
            OpKind::If => {
                self.operands(1)?;
                let loc = self.opt_loc()?;
                let op = self.body.append_op(
                    region,
                    OpKind::If,
                    self.operands.drain(..),
                    self.results.drain(..),
                    [vec![], vec![]],
                    loc,
                );
                let (thn, els) = (self.body.regions(op)[0], self.body.regions(op)[1]);
                self.region(thn, &[])?;
                if self.try_ident("else")? {
                    self.region(els, &[])?;
                }
                op
            }
            OpKind::Loop { .. } => {
                let progress = self.try_ident("progress")?;
                let iter = if self.try_ident("iter")? {
                    self.expect_sym(Sym::LParen)?;
                    self.sep_by(Self::iter_arg, Sym::RParen)?
                } else {
                    Vec::new()
                };
                let loc = self.opt_loc()?;
                let names: Vec<&'a str> = iter.iter().map(|(p, _)| p.name).collect();
                let (params, inits): (Vec<_>, Vec<_>) = iter.into_iter().unzip();
                let op = self.body.append_op(
                    region,
                    OpKind::Loop { progress },
                    inits,
                    self.results.drain(..),
                    [params],
                    loc,
                );
                let inner = self.body.regions(op)[0];
                self.region(inner, &names)?;
                op
            }
            k => {
                match arity(&k) {
                    Some(n) => self.operands(n)?,
                    None => self.variadic()?,
                }
                let loc = self.opt_loc()?;
                self.append(region, k, loc)
            }
        };
        // Define the results, whose names wait on the `pending` stack.
        for (i, v) in self.body.results(op).enumerate() {
            let name = self.pending[pending + i];
            if !self.resolve {
                break;
            }
            if self.names.insert(name, (v, true)).is_some() {
                return self.fail_name(format!("%{name} is defined more than once"));
            }
            self.undo.push(name);
        }
        self.pending.truncate(pending);
        Ok(())
    }

    /// Operands up to and including `)`, after at least one.
    fn variadic_until_close(&mut self) -> PResult<()> {
        loop {
            let o = self.operand()?;
            self.operands.push(o);
            if !self.try_sym(Sym::Comma)? {
                break;
            }
        }
        self.expect_sym(Sym::RParen)
    }

    /// Append an op without regions, with the operands and results in the scratch buffers.
    fn append(&mut self, region: RegionId, kind: OpKind, loc: Option<Loc>) -> crate::OpId {
        self.body.append_op(
            region,
            kind,
            self.operands.drain(..),
            self.results.drain(..),
            [],
            loc,
        )
    }

    /// `%name: type = %init`
    fn iter_arg(&mut self) -> PResult<(ValueSpec<'a>, Operand)> {
        let r = self.result()?;
        self.expect_sym(Sym::Eq)?;
        Ok((r, self.operand()?))
    }

    fn func(&mut self) -> PResult<Func> {
        if !self.try_ident("func")? {
            return self.fail("expected 'func'");
        }
        let name = match self.peek() {
            Tok::Global(s) => {
                self.bump()?;
                s.to_owned()
            }
            t => {
                return self.fail(format!(
                    "expected a function name like @main but found {}",
                    t.describe()
                ));
            }
        };
        self.expect_sym(Sym::LParen)?;
        self.body.clear();
        let params = self.sep_by(Self::result, Sym::RParen)?;
        let rets = if self.try_sym(Sym::Arrow)? {
            if self.try_sym(Sym::LParen)? {
                self.sep_by(Self::ty, Sym::RParen)?
            } else {
                vec![self.ty()?]
            }
        } else {
            Vec::new()
        };
        let file = if self.try_ident("loc")? {
            match self.peek() {
                Tok::Str(s) => {
                    self.bump()?;
                    Some(s.to_owned())
                }
                t => {
                    return self.fail(format!(
                        "expected a file name string but found {}",
                        t.describe()
                    ));
                }
            }
        } else {
            None
        };
        let param_names: Vec<&'a str> = params.iter().map(|p| p.name).collect();
        let entry = self.body.entry();
        self.body.set_params(entry, params);
        self.names.clear();
        self.region(entry, &param_names)?;
        // A small body is cloned (exactly sized), and the builder keeps its capacity for the
        // next function. A large one is handed over, so it isn't held twice.
        let body = if self.body.num_ops() < SMALL_BODY {
            self.body.clone()
        } else {
            let mut body = std::mem::take(&mut self.body);
            body.shrink_to_fit();
            body
        };
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
        if !self.try_ident("ptr")? {
            return self.fail("expected 'ptr'");
        }
        let ptr_bits = self.nat()?;
        if !self.try_ident("addr")? {
            return self.fail("expected 'addr'");
        }
        Ok(SpaceCfg {
            ptr_bits,
            addr_bits: self.nat()?,
        })
    }

    fn module(&mut self) -> PResult<Module> {
        let mut m = Module::default();
        while self.peek() != Tok::Eof {
            if self.try_ident("memspace")? {
                m.space = self.memspace()?;
            } else {
                m.funcs.push(self.func()?);
            }
        }
        Ok(m)
    }
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

/// Decode an op name with its modifiers. Ops with immediates get placeholders (such as
/// `align 1`, or string and integer ids that point nowhere) that the parser fills.
pub fn op_kind(name: &str) -> Option<OpKind> {
    use OpKind::*;
    let mut parts = [""; 6];
    let mut n = 0;
    for p in name.split('.') {
        if n == parts.len() {
            return None;
        }
        parts[n] = p;
        n += 1;
    }
    Some(match &parts[..n] {
        ["int", "const"] => Const(IntId::PLACEHOLDER),
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
            family: StrId::PLACEHOLDER,
            align: 1,
        },
        ["mem", "alloc", "trap"] => MemAlloc {
            fail: AllocFail::Trap,
            family: StrId::PLACEHOLDER,
            align: 1,
        },
        ["mem", "free"] => MemFree {
            family: StrId::PLACEHOLDER,
        },
        ["mem", "load"] => Load { align: 1 },
        ["mem", "store"] => Store {
            ty: Ty::Ptr,
            align: 1,
        },
        ["func", "call"] => Call {
            callee: StrId::PLACEHOLDER,
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
