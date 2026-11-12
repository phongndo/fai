//! Splits FIR text into tokens, mirroring `spec/Fir/Lex.lean`. Comments start with `//` and run
//! to the end of the line. Columns count characters, as in Lean.

use num_bigint::BigInt;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Tok {
    /// `%name`
    Value(String),
    /// `@name`
    Global(String),
    /// `@line:col`
    Loc(u32, u32),
    /// `?name`
    Hole(String),
    Ident(String),
    Int(BigInt),
    Str(String),
    /// One of `( ) { } [ ] , : = ->`
    Sym(&'static str),
    Eof,
}

impl Tok {
    pub fn describe(&self) -> String {
        match self {
            Tok::Value(s) => format!("%{s}"),
            Tok::Global(s) => format!("@{s}"),
            Tok::Loc(l, c) => format!("@{l}:{c}"),
            Tok::Hole(s) => format!("?{s}"),
            Tok::Ident(s) => format!("'{s}'"),
            Tok::Int(n) => n.to_string(),
            Tok::Str(s) => format!("\"{s}\""),
            Tok::Sym(s) => format!("'{s}'"),
            Tok::Eof => "end of input".into(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub line: u32,
    pub col: u32,
}

fn is_name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '.'
}

/// Lean's `Char.isWhitespace`.
fn is_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\r' | '\n')
}

const SYMS: [&str; 9] = ["(", ")", "{", "}", "[", "]", ",", ":", "="];

struct Lexer<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    line: u32,
    col: u32,
}

impl Lexer<'_> {
    fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    fn peek2(&self) -> Option<char> {
        let mut it = self.chars.clone();
        it.next();
        it.next()
    }

    fn advance(&mut self) {
        match self.chars.next() {
            Some('\n') => {
                self.line += 1;
                self.col = 1;
            }
            Some(_) => self.col += 1,
            None => {}
        }
    }

    fn take_while(&mut self, p: impl Fn(char) -> bool) -> String {
        let mut s = String::new();
        while let Some(c) = self.peek().filter(|&c| p(c)) {
            s.push(c);
            self.advance();
        }
        s
    }
}

pub fn lex(input: &str) -> Result<Vec<Token>, String> {
    let mut lx = Lexer {
        chars: input.chars().peekable(),
        line: 1,
        col: 1,
    };
    let mut toks = Vec::new();
    loop {
        let (line, col) = (lx.line, lx.col);
        let fail = |msg: String| Err(format!("{line}:{col}: {msg}"));
        let Some(c) = lx.peek() else {
            toks.push(Token {
                tok: Tok::Eof,
                line,
                col,
            });
            return Ok(toks);
        };
        let next = lx.peek2();
        let tok = if is_space(c) {
            lx.advance();
            continue;
        } else if c == '/' && next == Some('/') {
            lx.take_while(|c| c != '\n');
            continue;
        } else if c == '-' && next == Some('>') {
            lx.advance();
            lx.advance();
            Tok::Sym("->")
        } else if let Some(sym) = SYMS.iter().find(|s| s.starts_with(c)) {
            lx.advance();
            Tok::Sym(sym)
        } else if c == '%' || c == '?' {
            lx.advance();
            let name = lx.take_while(is_name_char);
            if name.is_empty() {
                return fail(format!("expected a name after '{c}'"));
            }
            if c == '%' {
                Tok::Value(name)
            } else {
                Tok::Hole(name)
            }
        } else if c == '@' {
            lx.advance();
            if lx.peek().is_some_and(|c| c.is_ascii_digit()) {
                let l = lx.take_while(|c| c.is_ascii_digit());
                if lx.peek() != Some(':') {
                    return fail("expected ':' in a location".into());
                }
                lx.advance();
                let c = lx.take_while(|c| c.is_ascii_digit());
                Tok::Loc(number(&l, line, col)?, number(&c, line, col)?)
            } else {
                let name = lx.take_while(is_name_char);
                if name.is_empty() {
                    return fail("expected a name after '@'".into());
                }
                Tok::Global(name)
            }
        } else if c.is_ascii_digit() || (c == '-' && next.is_some_and(|c| c.is_ascii_digit())) {
            let neg = c == '-';
            if neg {
                lx.advance();
            }
            let digits = lx.take_while(|c| c.is_ascii_digit());
            let text = if neg { format!("-{digits}") } else { digits };
            Tok::Int(text.parse().expect("decimal digits"))
        } else if c == '"' {
            lx.advance();
            let body = lx.take_while(|c| c != '"');
            if lx.peek().is_none() {
                return fail("unterminated string".into());
            }
            lx.advance();
            Tok::Str(body)
        } else if c.is_ascii_alphabetic() || c == '_' {
            Tok::Ident(lx.take_while(is_name_char))
        } else {
            return fail(format!("unexpected character '{c}'"));
        };
        toks.push(Token { tok, line, col });
    }
}

/// A location component. Lean's `toNat!` gives 0 for an empty string.
fn number(s: &str, line: u32, col: u32) -> Result<u32, String> {
    if s.is_empty() {
        return Ok(0);
    }
    s.parse()
        .map_err(|_| format!("{line}:{col}: location {s} is too large"))
}
