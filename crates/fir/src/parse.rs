//! Parses FIR text into a [`Module`], mirroring `spec/Fir/Parse.lean`.
//!
//! The Lean parser keeps value names as text and leaves scoping to its verifier. This parser
//! builds the arena directly, so it resolves each use to its definition as it goes, with the
//! verifier's rules and messages: a value is defined once per function, and visible after its
//! definition in the same region or a nested one (a block of `cf.blocks` is a region). Block
//! labels are kept as text; the verifier resolves them.

use num_bigint::Sign;
use rustc_hash::FxHashMap;

use crate::body::{
    Body, Case, CasesId, IntId, OpId, Operand, RegionId, StrId, Succ, ValueId, ValueSpec,
};
use crate::decl::{Field, FieldTy, Imm, Item, Layer};
use crate::ir::*;
use crate::lex::{Lexer, Sym, Tok, Token, int_value};
use crate::ops::{TARGETS, op_kind};
use crate::types::Types;

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
    /// The module's globals so far.
    globals: Globals,
    /// Whether types go to the globals' table (or the current body's).
    in_globals: bool,
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
            globals: Globals::default(),
            in_globals: false,
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

    /// A target register: `x0`…`x30`, `sp`, `xzr`, or `v` and a number.
    fn reg(&mut self) -> PResult<Reg> {
        match self.peek() {
            Tok::Ident(s) => match Reg::parse(s) {
                Some(r) => {
                    self.bump()?;
                    Ok(r)
                }
                None => self.fail(format!("expected a register like x0 or v1 but found '{s}'")),
            },
            t => self.fail(format!(
                "expected a register like x0 or v1 but found {}",
                t.describe()
            )),
        }
    }

    fn label(&mut self) -> PResult<&'a str> {
        match self.peek() {
            Tok::Label(s) => {
                self.bump()?;
                Ok(s)
            }
            t => self.fail(format!(
                "expected a block label like ^b but found {}",
                t.describe()
            )),
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

    /// The table types are parsed into.
    fn types(&mut self) -> &mut Types {
        if self.in_globals {
            &mut self.globals.types
        } else {
            self.body.types_mut()
        }
    }

    /// A type: `i32`, `ptr`, `b8`, `struct<C>{i32, ptr}`, `array<4 x i32>`, or
    /// `func<(i32, ptr) -> i32>`.
    fn ty(&mut self) -> PResult<Ty> {
        let s = self.ident()?;
        // `iN` and `bN` first: they are most of the types.
        let rest = s.get(1..).unwrap_or("");
        let width = if !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()) {
            rest.parse::<u32>().ok()
        } else {
            None
        };
        match (s.as_bytes()[0], width) {
            (b'i', Some(w)) => return Ok(Ty::Int(w)),
            (b'b', Some(w)) => return Ok(Ty::Byte(w)),
            _ => {}
        }
        match s {
            "ptr" => Ok(Ty::Ptr),
            "struct" => {
                self.expect_sym(Sym::Lt)?;
                let policy = match self.ident()? {
                    "C" => Policy::C,
                    "packed" => Policy::Packed,
                    "auto" => Policy::Auto,
                    p => return self.fail(format!("unknown struct layout '{p}'")),
                };
                self.expect_sym(Sym::Gt)?;
                self.expect_sym(Sym::LBrace)?;
                let fields = self.sep_by(Self::ty, Sym::RBrace)?;
                Ok(self.types().structure(policy, &fields))
            }
            "array" => {
                self.expect_sym(Sym::Lt)?;
                let n = self.nat()?;
                if !self.try_ident("x")? {
                    return self.fail("expected 'x'");
                }
                let elem = self.ty()?;
                self.expect_sym(Sym::Gt)?;
                Ok(self.types().array(n, elem))
            }
            "func" => {
                self.expect_sym(Sym::Lt)?;
                self.expect_sym(Sym::LParen)?;
                let params = self.sep_by(Self::ty, Sym::RParen)?;
                let rets = if self.try_sym(Sym::Arrow)? {
                    if self.try_sym(Sym::LParen)? {
                        self.sep_by(Self::ty, Sym::RParen)?
                    } else {
                        vec![self.ty()?]
                    }
                } else {
                    Vec::new()
                };
                self.expect_sym(Sym::Gt)?;
                Ok(self.types().func(&params, &rets))
            }
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

    /// Zero or more comma-separated operands, into the scratch buffer.
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
        self.ops(region, false)?;
        self.bump()?;
        self.hide(mark);
        Ok(())
    }

    /// Ops into `region`, up to the `}` that closes it (left for the caller), or for a block of
    /// `cf.blocks`, up to the next label too. The one place ops are parsed, so `op` can be
    /// inlined here.
    fn ops(&mut self, region: RegionId, block: bool) -> PResult<()> {
        loop {
            match self.peek() {
                Tok::Sym(Sym::RBrace) => return Ok(()),
                Tok::Label(_) if block => return Ok(()),
                Tok::Eof => return self.fail("expected '}'"),
                _ => self.op(region)?,
            }
        }
    }

    /// Hide the names defined since `undo` had `mark` entries.
    fn hide(&mut self, mark: usize) {
        for name in self.undo.drain(mark..) {
            if let Some(e) = self.names.get_mut(name) {
                e.1 = false;
            }
        }
    }

    /// `cf.blocks`'s blocks, `{ ^a: ops ^b(%x: T): ops … }`, into `op`. A block's ops run up to
    /// the next label or the closing `}`; its names are hidden at its end.
    #[inline(never)]
    fn blocks(&mut self, op: OpId) -> PResult<()> {
        self.expect_sym(Sym::LBrace)?;
        let mut blocks = Vec::new();
        while !self.try_sym(Sym::RBrace)? {
            let label = self.label()?;
            let params = if self.try_sym(Sym::LParen)? {
                self.sep_by(Self::result, Sym::RParen)?
            } else {
                Vec::new()
            };
            self.expect_sym(Sym::Colon)?;
            let names: Vec<&'a str> = params.iter().map(|p| p.name).collect();
            let label = self.body.add_str(label);
            let r = self.body.new_block(op, label, params);
            blocks.push(r);
            let mark = self.undo.len();
            self.define(&names, self.body.params(r))?;
            self.ops(r, true)?;
            self.hide(mark);
        }
        self.body.set_regions(op, &blocks);
        Ok(())
    }

    /// A branch target in the readable form, `^b` or `^b(%x, …)`; its arguments go on the
    /// scratch operands.
    #[inline(never)]
    fn succ(&mut self) -> PResult<Succ> {
        let label = self.label()?;
        let start = self.operands.len();
        if self.try_sym(Sym::LParen)? && !self.try_sym(Sym::RParen)? {
            self.variadic_until_close()?;
        }
        Ok(Succ {
            label: self.body.add_str(label),
            nargs: (self.operands.len() - start) as u32,
        })
    }

    /// A branch target in the generic form: `^b`, or `^b(n)` for `n` arguments.
    #[inline(never)]
    fn generic_succ(&mut self) -> PResult<Succ> {
        let label = self.label()?;
        let nargs = if self.try_sym(Sym::LParen)? {
            let n = self.nat()?;
            self.expect_sym(Sym::RParen)?;
            n
        } else {
            0
        };
        Ok(Succ {
            label: self.body.add_str(label),
            nargs,
        })
    }

    /// `cf.switch`'s cases, `[k: target, …]`, with targets in the readable or generic form.
    #[inline(never)]
    fn cases(&mut self, generic: bool) -> PResult<CasesId> {
        self.expect_sym(Sym::LBracket)?;
        let mut cases = Vec::new();
        if !self.try_sym(Sym::RBracket)? {
            loop {
                let key = self.int()?;
                self.expect_sym(Sym::Colon)?;
                let succ = if generic {
                    self.generic_succ()?
                } else {
                    self.succ()?
                };
                cases.push(Case { key, succ });
                if !self.try_sym(Sym::Comma)? {
                    break;
                }
            }
            self.expect_sym(Sym::RBracket)?;
        }
        Ok(self.body.add_cases(cases))
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
        self.operands.clear();
        let op = match self.peek() {
            Tok::Str(name) => {
                self.bump()?;
                self.generic_op(region, name)?
            }
            _ => {
                let name = self.ident()?;
                let Some(kind) = op_kind(name) else {
                    return self.fail(format!("unknown op '{name}'"));
                };
                self.readable_op(region, kind)?
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

    /// `@name`, for a global.
    fn global_name(&mut self) -> PResult<&'a str> {
        match self.peek() {
            Tok::Global(s) => {
                self.bump()?;
                Ok(s)
            }
            t => self.fail(format!(
                "expected a global name like @g but found {}",
                t.describe()
            )),
        }
    }

    /// `@name`
    fn func_name(&mut self) -> PResult<StrId> {
        match self.peek() {
            Tok::Global(s) => {
                self.bump()?;
                Ok(self.body.add_str(s))
            }
            t => self.fail(format!(
                "expected a function name like @f but found {}",
                t.describe()
            )),
        }
    }

    /// An immediate, as the readable form writes it. A flag is a keyword named after its field.
    /// Branch targets are read here as the generic form writes them; the readable form's go with
    /// their operands (`readable_op`).
    fn imm(&mut self, f: Field) -> PResult<Imm> {
        Ok(match f.ty {
            FieldTy::Int => Imm::Int(self.int()?),
            FieldTy::Nat => Imm::Nat(self.nat()?),
            FieldTy::Align => Imm::Align(self.nat()?),
            FieldTy::Index => Imm::Index(self.nat()?),
            FieldTy::Symbol => {
                let s = self.ident()?;
                Imm::Str(self.body.add_str(s))
            }
            FieldTy::Func => Imm::Str(self.func_name()?),
            FieldTy::Global => {
                let s = self.global_name()?;
                Imm::Str(self.body.add_str(s))
            }
            FieldTy::Ty => Imm::Ty(self.ty()?),
            FieldTy::Flag => Imm::Flag(self.try_ident(f.name)?),
            FieldTy::Succ => {
                let s = self.generic_succ()?;
                Imm::Succ(self.body.add_succ(s))
            }
            FieldTy::Cases => Imm::Cases(self.cases(true)?),
            FieldTy::Reg => Imm::Reg(self.reg()?),
        })
    }

    /// An op in its readable form, after its name, as its declaration's format says. The
    /// results are in the scratch buffer.
    fn readable_op(&mut self, region: RegionId, mut kind: OpKind) -> PResult<OpId> {
        let decl = kind.decl();
        let mut iter = Vec::new();
        for &item in decl.head() {
            match item {
                Item::Imm(i) => {
                    let f = decl.imms[usize::from(i)];
                    let v = match f.ty {
                        FieldTy::Succ => {
                            let s = self.succ()?;
                            Imm::Succ(self.body.add_succ(s))
                        }
                        FieldTy::Cases => Imm::Cases(self.cases(false)?),
                        _ => self.imm(f)?,
                    };
                    kind.set_imm(i.into(), v);
                }
                Item::Operand => {
                    let o = self.operand()?;
                    self.operands.push(o);
                }
                Item::Comma => self.expect_sym(Sym::Comma)?,
                Item::Keyword(kw) => {
                    if !self.try_ident(kw)? {
                        return self.fail(format!("expected '{kw}'"));
                    }
                }
                Item::Variadic => self.variadic()?,
                Item::Args => {
                    self.expect_sym(Sym::LParen)?;
                    if !self.try_sym(Sym::RParen)? {
                        self.variadic_until_close()?;
                    }
                }
                Item::Iter => {
                    if self.try_ident("iter")? {
                        self.expect_sym(Sym::LParen)?;
                        iter = self.sep_by(Self::iter_arg, Sym::RParen)?;
                    }
                }
                Item::Region(_) | Item::Blocks => {}
            }
        }
        let loc = self.opt_loc()?;
        // `%iter` gives the operands, and the first region's parameters.
        let names: Vec<&'a str> = iter.iter().map(|(p, _)| p.name).collect();
        let (params, inits): (Vec<_>, Vec<_>) = iter.into_iter().unzip();
        self.operands.extend(inits);
        let mut params = Some(params);
        let op = self.body.append_op(
            region,
            kind,
            self.operands.drain(..),
            self.results.drain(..),
            decl.regions().map(|_| params.take().unwrap_or_default()),
            loc,
        );
        for (i, kw) in decl.regions().enumerate() {
            let r = self.body.regions(op)[i];
            match kw {
                None => self.region(r, if i == 0 { &names } else { &[] })?,
                Some(kw) => {
                    if self.try_ident(kw)? {
                        self.region(r, &[])?;
                    }
                }
            }
        }
        if decl.has_blocks() {
            self.blocks(op)?;
        }
        Ok(op)
    }

    /// A generic-form attribute value: as in the readable form, except that a flag is `true`
    /// or `false`.
    fn attr_value(&mut self, f: Field) -> PResult<Imm> {
        if f.ty != FieldTy::Flag {
            return self.imm(f);
        }
        let b = match self.peek() {
            Tok::Ident("true") => true,
            Tok::Ident("false") => false,
            t => {
                return self.fail(format!("expected true or false but found {}", t.describe()));
            }
        };
        self.bump()?;
        Ok(Imm::Flag(b))
    }

    /// An op in the generic form, after its name `"name"` (see `spec/Fir/Parse.lean`). The
    /// results are in the scratch buffer.
    fn generic_op(&mut self, region: RegionId, name: &'a str) -> PResult<OpId> {
        let Some(mut kind) = op_kind(name) else {
            return self.fail(format!("unknown op '{name}'"));
        };
        let decl = kind.decl();
        self.expect_sym(Sym::LParen)?;
        if !self.try_sym(Sym::RParen)? {
            self.variadic_until_close()?;
        }
        // `{key = value, ...}`: every immediate, each once, in any order.
        let mut seen = vec![false; decl.imms.len()];
        if self.try_sym(Sym::LBrace)? && !self.try_sym(Sym::RBrace)? {
            loop {
                let key = match self.peek() {
                    Tok::Ident(key) => key,
                    t => return self.fail(format!("expected a name but found {}", t.describe())),
                };
                let Some(i) = decl.imms.iter().position(|f| f.name == key) else {
                    return self.fail(format!("{name} has no attribute '{key}'"));
                };
                if seen[i] {
                    return self.fail(format!("attribute '{key}' is given twice"));
                }
                self.bump()?;
                self.expect_sym(Sym::Eq)?;
                let v = self.attr_value(decl.imms[i])?;
                kind.set_imm(i, v);
                seen[i] = true;
                if !self.try_sym(Sym::Comma)? {
                    break;
                }
            }
            self.expect_sym(Sym::RBrace)?;
        }
        if let Some(i) = seen.iter().position(|s| !s) {
            return self.fail(format!(
                "{name} needs the attribute '{}'",
                decl.imms[i].name
            ));
        }
        let loc = self.opt_loc()?;
        let n = if self.peek() == Tok::Sym(Sym::LParen) {
            self.count_regions()
        } else {
            0
        };
        let op = self.body.append_op(
            region,
            kind,
            self.operands.drain(..),
            self.results.drain(..),
            (0..n).map(|_| Vec::new()),
            loc,
        );
        // `(^b(%x: T, ...) { ... }, ...)`, the label and parameters optional.
        if self.try_sym(Sym::LParen)? && !self.try_sym(Sym::RParen)? {
            let mut i = 0;
            loop {
                let label = match self.peek() {
                    Tok::Label(l) => {
                        self.bump()?;
                        Some(l)
                    }
                    _ => None,
                };
                let params = if self.try_sym(Sym::LParen)? {
                    self.sep_by(Self::result, Sym::RParen)?
                } else {
                    Vec::new()
                };
                // The count covers every region whose `{` follows; for one without it, this
                // reports the missing `{`.
                let Some(&r) = self.body.regions(op).get(i) else {
                    self.expect_sym(Sym::LBrace)?;
                    return self.fail("expected '{'");
                };
                let names: Vec<&'a str> = params.iter().map(|p| p.name).collect();
                self.body.set_params(r, params);
                if let Some(l) = label {
                    let l = self.body.add_str(l);
                    self.body.set_label(r, l);
                }
                self.region(r, &names)?;
                i += 1;
                if !self.try_sym(Sym::Comma)? {
                    break;
                }
            }
            self.expect_sym(Sym::RParen)?;
        }
        Ok(op)
    }

    /// How many regions a generic op's region list holds, read ahead from its `(`: the `{`s
    /// at its top level, up to the matching `)`. An op's regions are made with it, before their
    /// contents are parsed. Every region the parser reaches with its `{` next is counted; if the
    /// list is malformed otherwise, parsing it fails before the count matters.
    fn count_regions(&self) -> usize {
        let mut lexer = self.lexer.clone();
        let (mut parens, mut braces, mut n) = (0usize, 0usize, 0);
        while let Ok(t) = lexer.next_token() {
            match t.tok {
                Tok::Eof => break,
                Tok::Sym(Sym::LBrace) => {
                    if braces == 0 && parens == 0 {
                        n += 1;
                    }
                    braces += 1;
                }
                Tok::Sym(Sym::RBrace) => match braces.checked_sub(1) {
                    Some(b) => braces = b,
                    None => break,
                },
                Tok::Sym(Sym::LParen) if braces == 0 => parens += 1,
                Tok::Sym(Sym::RParen) if braces == 0 => match parens.checked_sub(1) {
                    Some(p) => parens = p,
                    None => break,
                },
                _ => {}
            }
        }
        n
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

    /// `memspace default ptr 64 addr 64 [align 8] [int 8:1 16:2 …]`
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
        let addr_bits = self.nat()?;
        let ptr_align = if self.try_ident("align")? {
            self.nat()?
        } else {
            SpaceCfg::natural_align(ptr_bits)
        };
        let mut ints = DEFAULT_INTS.to_vec();
        if self.try_ident("int")? {
            ints.clear();
            loop {
                let w = self.nat()?;
                self.expect_sym(Sym::Colon)?;
                ints.push((w, self.nat()?));
                if !matches!(self.peek(), Tok::Int(_)) {
                    break;
                }
            }
        }
        Ok(SpaceCfg {
            ptr_bits,
            addr_bits,
            ptr_align,
            ints,
        })
    }

    /// `zero`, an integer, `null`, `@name`, `bytes "00ff"`, or `{init, …}`.
    fn init(&mut self) -> PResult<Init> {
        Ok(match self.peek() {
            Tok::Ident("zero") => {
                self.bump()?;
                Init::Zero
            }
            Tok::Ident("null") => {
                self.bump()?;
                Init::Null
            }
            Tok::Ident("bytes") => {
                self.bump()?;
                let Tok::Str(s) = self.peek() else {
                    let found = self.peek().describe();
                    return self.fail(format!("expected a string of hex digits but found {found}"));
                };
                let Some(bs) = hex_bytes(s) else {
                    return self.fail("expected two lowercase hex digits per byte");
                };
                self.bump()?;
                self.globals.bytes_init(bs)
            }
            Tok::Int(text) => {
                self.bump()?;
                self.globals.int_init(int_value(text))
            }
            Tok::Global(name) => {
                self.bump()?;
                self.globals.sym_init(name)
            }
            Tok::Sym(Sym::LBrace) => {
                self.bump()?;
                let items = self.sep_by(Self::init, Sym::RBrace)?;
                self.globals.list_init(items)
            }
            t => {
                return self.fail(format!(
                    "expected an initializer but found {}",
                    t.describe()
                ));
            }
        })
    }

    /// `global [const] @name: T [align N] = INIT`, after `global`.
    fn global(&mut self) -> PResult<()> {
        let constant = self.try_ident("const")?;
        let name = self.global_name()?;
        self.expect_sym(Sym::Colon)?;
        self.in_globals = true;
        let ty = self.ty();
        self.in_globals = false;
        let ty = ty?;
        let align = if self.try_ident("align")? {
            self.nat()?
        } else {
            1
        };
        self.expect_sym(Sym::Eq)?;
        let init = self.init()?;
        self.globals.push(name, ty, constant, align, init);
        Ok(())
    }

    /// `args`, `exposed`, or `globals`.
    fn mem_class(&mut self) -> PResult<MemClass> {
        match self.ident()? {
            "args" => Ok(MemClass::Args),
            "exposed" => Ok(MemClass::Exposed),
            "globals" => Ok(MemClass::Globals),
            s => self.fail(format!(
                "expected args, exposed, or globals but found '{s}'"
            )),
        }
    }

    /// `read(args)`, `write(exposed)`, `alloc`, `free`, `trap`, `diverge`, or `unwind`.
    fn ext_effect(&mut self) -> PResult<ExtEffect> {
        let name = self.ident()?;
        Ok(match name {
            "read" | "write" => {
                self.expect_sym(Sym::LParen)?;
                let m = self.mem_class()?;
                self.expect_sym(Sym::RParen)?;
                if name == "read" {
                    ExtEffect::Read(m)
                } else {
                    ExtEffect::Write(m)
                }
            }
            "alloc" => ExtEffect::Alloc,
            "free" => ExtEffect::Free,
            "trap" => ExtEffect::Trap,
            "diverge" => ExtEffect::Diverge,
            "unwind" => ExtEffect::Unwind,
            s => return self.fail(format!("unknown effect '{s}'")),
        })
    }

    /// `extern func @name(T, …) [-> T | -> (T, …)] effects[E, …] TRUST`, after `extern`. The
    /// types go in the module's table.
    fn extern_decl(&mut self) -> PResult<Extern> {
        if !self.try_ident("func")? {
            return self.fail("expected 'func' after 'extern'");
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
        self.in_globals = true;
        let sig = self.extern_sig();
        self.in_globals = false;
        let (params, rets) = sig?;
        if !self.try_ident("effects")? {
            return self.fail("expected 'effects' after an external function's signature");
        }
        self.expect_sym(Sym::LBracket)?;
        let effects = self.sep_by(Self::ext_effect, Sym::RBracket)?;
        let trust = self.trust()?;
        Ok(Extern {
            name,
            params,
            rets,
            effects,
            trust,
        })
    }

    /// `(T, …) [-> T | -> (T, …)]`
    fn extern_sig(&mut self) -> PResult<(Vec<Ty>, Vec<Ty>)> {
        self.expect_sym(Sym::LParen)?;
        let params = self.sep_by(Self::ty, Sym::RParen)?;
        let rets = if self.try_sym(Sym::Arrow)? {
            if self.try_sym(Sym::LParen)? {
                self.sep_by(Self::ty, Sym::RParen)?
            } else {
                vec![self.ty()?]
            }
        } else {
            Vec::new()
        };
        Ok((params, rets))
    }

    /// `hfir`, `mfir`, or `lfir TARGET`, after `layer`.
    fn layer(&mut self) -> PResult<Layer> {
        match self.peek() {
            Tok::Ident("hfir") => {
                self.bump()?;
                Ok(Layer::Hfir)
            }
            Tok::Ident("mfir") => {
                self.bump()?;
                Ok(Layer::Mfir)
            }
            Tok::Ident("lfir") => {
                self.bump()?;
                match self.peek() {
                    Tok::Ident(t) => {
                        let Some(t) = Layer::target(t) else {
                            return self.fail(format!(
                                "unknown target '{t}': expected {}",
                                TARGETS.join(", ")
                            ));
                        };
                        self.bump()?;
                        Ok(Layer::Lfir(t))
                    }
                    t => self.fail(format!(
                        "expected a target after lfir but found {}",
                        t.describe()
                    )),
                }
            }
            Tok::Ident(s) => {
                self.fail(format!("unknown layer '{s}': expected hfir, mfir, or lfir"))
            }
            t => self.fail(format!("expected a layer but found {}", t.describe())),
        }
    }

    fn module(&mut self) -> PResult<Module> {
        let mut m = Module::default();
        let mut layer = None;
        while self.peek() != Tok::Eof {
            if self.peek() == Tok::Ident("layer") {
                if layer.is_some() {
                    return self.fail("the module's layer is declared more than once");
                }
                self.bump()?;
                layer = Some(self.layer()?);
            } else if self.try_ident("memspace")? {
                m.space = self.memspace()?;
            } else if self.try_ident("global")? {
                self.global()?;
            } else if self.try_ident("extern")? {
                let x = self.extern_decl()?;
                m.externs.push(x);
            } else {
                m.funcs.push(self.func()?);
            }
        }
        m.globals = std::mem::take(&mut self.globals);
        m.layer = layer.unwrap_or_default();
        Ok(m)
    }
}

/// Hex digits, two per byte, lowercase (Lean's `hexBytes`).
fn hex_bytes(s: &str) -> Option<Vec<u8>> {
    let digit = |c: u8| match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        _ => None,
    };
    let b = s.as_bytes();
    if !b.len().is_multiple_of(2) {
        return None;
    }
    b.chunks(2)
        .map(|p| Some(digit(p[0])? * 16 + digit(p[1])?))
        .collect()
}
