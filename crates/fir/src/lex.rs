//! Splits FIR text into tokens, mirroring `spec/Fir/Lex.lean`. Comments start with `//` and run
//! to the end of the line. Columns count characters, as in Lean.
//!
//! Tokens are produced on demand and borrow their text from the input, so lexing allocates
//! nothing. Lean lexes the whole file before parsing; the parser keeps that behavior by checking
//! the rest of the input for a lexing error before it reports one of its own (see
//! [`Lexer::first_error`]).

use num_bigint::BigInt;

/// A punctuation token.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Sym {
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Colon,
    Eq,
    Arrow,
}

impl Sym {
    pub fn text(self) -> &'static str {
        match self {
            Sym::LParen => "(",
            Sym::RParen => ")",
            Sym::LBrace => "{",
            Sym::RBrace => "}",
            Sym::LBracket => "[",
            Sym::RBracket => "]",
            Sym::Comma => ",",
            Sym::Colon => ":",
            Sym::Eq => "=",
            Sym::Arrow => "->",
        }
    }

    fn of_byte(b: u8) -> Option<Sym> {
        Some(match b {
            b'(' => Sym::LParen,
            b')' => Sym::RParen,
            b'{' => Sym::LBrace,
            b'}' => Sym::RBrace,
            b'[' => Sym::LBracket,
            b']' => Sym::RBracket,
            b',' => Sym::Comma,
            b':' => Sym::Colon,
            b'=' => Sym::Eq,
            _ => return None,
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Tok<'a> {
    /// `%name`
    Value(&'a str),
    /// `@name`
    Global(&'a str),
    /// `@line:col`
    Loc(u32, u32),
    /// `?name`
    Hole(&'a str),
    /// `^name`, a block label
    Label(&'a str),
    Ident(&'a str),
    /// An integer literal: an optional `-` and decimal digits.
    Int(&'a str),
    Str(&'a str),
    Sym(Sym),
    Eof,
}

/// The value of an integer literal. Small ones skip the general decimal conversion.
pub fn int_value(text: &str) -> BigInt {
    match text.parse::<i64>() {
        Ok(n) => BigInt::from(n),
        Err(_) => text.parse().expect("an integer literal"),
    }
}

impl Tok<'_> {
    pub fn describe(&self) -> String {
        match self {
            Tok::Value(s) => format!("%{s}"),
            Tok::Global(s) => format!("@{s}"),
            Tok::Loc(l, c) => format!("@{l}:{c}"),
            Tok::Hole(s) => format!("?{s}"),
            Tok::Label(s) => format!("^{s}"),
            Tok::Ident(s) => format!("'{s}'"),
            Tok::Int(s) => int_value(s).to_string(),
            Tok::Str(s) => format!("\"{s}\""),
            Tok::Sym(s) => format!("'{}'", s.text()),
            Tok::Eof => "end of input".into(),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Token<'a> {
    pub tok: Tok<'a>,
    pub line: u32,
    pub col: u32,
}

fn is_name_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'.'
}

#[derive(Clone)]
pub struct Lexer<'a> {
    text: &'a str,
    pos: usize,
    line: u32,
    col: u32,
}

impl<'a> Lexer<'a> {
    pub fn new(text: &'a str) -> Lexer<'a> {
        Lexer {
            text,
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    fn byte(&self, at: usize) -> Option<u8> {
        self.text.as_bytes().get(at).copied()
    }

    /// Skip ASCII bytes matching `p`; they are one column each.
    fn skip_ascii(&mut self, p: impl Fn(u8) -> bool) -> &'a str {
        let start = self.pos;
        let bytes = self.text.as_bytes();
        while self.pos < bytes.len() && p(bytes[self.pos]) {
            self.pos += 1;
        }
        self.col += (self.pos - start) as u32;
        &self.text[start..self.pos]
    }

    /// Skip to `stop` (exclusive), counting characters and line breaks.
    fn skip_until(&mut self, stop: u8) -> &'a str {
        let start = self.pos;
        let bytes = self.text.as_bytes();
        while self.pos < bytes.len() && bytes[self.pos] != stop {
            let b = bytes[self.pos];
            if b == b'\n' {
                self.line += 1;
                self.col = 1;
            } else if b & 0xC0 != 0x80 {
                self.col += 1;
            }
            self.pos += 1;
        }
        &self.text[start..self.pos]
    }

    pub fn next_token(&mut self) -> Result<Token<'a>, String> {
        loop {
            match self.byte(self.pos) {
                Some(b' ' | b'\t' | b'\r') => {
                    self.pos += 1;
                    self.col += 1;
                }
                Some(b'\n') => {
                    self.pos += 1;
                    self.line += 1;
                    self.col = 1;
                }
                Some(b'/') if self.byte(self.pos + 1) == Some(b'/') => {
                    self.skip_until(b'\n');
                }
                _ => break,
            }
        }
        let (line, col) = (self.line, self.col);
        let fail = |msg: String| Err(format!("{line}:{col}: {msg}"));
        let Some(c) = self.byte(self.pos) else {
            return Ok(Token {
                tok: Tok::Eof,
                line,
                col,
            });
        };
        let next = self.byte(self.pos + 1);
        let tok = if c == b'-' && next == Some(b'>') {
            self.pos += 2;
            self.col += 2;
            Tok::Sym(Sym::Arrow)
        } else if let Some(sym) = Sym::of_byte(c) {
            self.pos += 1;
            self.col += 1;
            Tok::Sym(sym)
        } else if c == b'%' || c == b'?' {
            self.pos += 1;
            self.col += 1;
            let name = self.skip_ascii(is_name_byte);
            if name.is_empty() {
                return fail(format!("expected a name after '{}'", c as char));
            }
            if c == b'%' {
                Tok::Value(name)
            } else {
                Tok::Hole(name)
            }
        } else if c == b'@' {
            self.pos += 1;
            self.col += 1;
            if next.is_some_and(|b| b.is_ascii_digit()) {
                let l = self.skip_ascii(|b| b.is_ascii_digit());
                if self.byte(self.pos) != Some(b':') {
                    return fail("expected ':' in a location".into());
                }
                self.pos += 1;
                self.col += 1;
                let c = self.skip_ascii(|b| b.is_ascii_digit());
                if c.is_empty() {
                    return fail("expected a column number in a location".into());
                }
                Tok::Loc(number(l, line, col)?, number(c, line, col)?)
            } else {
                let name = self.skip_ascii(is_name_byte);
                if name.is_empty() {
                    return fail("expected a name after '@'".into());
                }
                Tok::Global(name)
            }
        } else if c.is_ascii_digit() || (c == b'-' && next.is_some_and(|b| b.is_ascii_digit())) {
            let start = self.pos;
            if c == b'-' {
                self.pos += 1;
                self.col += 1;
            }
            self.skip_ascii(|b| b.is_ascii_digit());
            Tok::Int(&self.text[start..self.pos])
        } else if c == b'"' {
            self.pos += 1;
            self.col += 1;
            let body = self.skip_until(b'"');
            if self.pos >= self.text.len() {
                return fail("unterminated string".into());
            }
            self.pos += 1;
            self.col += 1;
            Tok::Str(body)
        } else if c.is_ascii_alphabetic() || c == b'_' {
            Tok::Ident(self.skip_ascii(is_name_byte))
        } else if c == b'^' {
            // Last, and out of line: labels are rare.
            return self.label(line, col);
        } else {
            let ch = self.text[self.pos..].chars().next().expect("a character");
            return fail(format!("unexpected character '{ch}'"));
        };
        Ok(Token { tok, line, col })
    }

    /// `^name`, a block label.
    #[cold]
    #[inline(never)]
    fn label(&mut self, line: u32, col: u32) -> Result<Token<'a>, String> {
        self.pos += 1;
        self.col += 1;
        let name = self.skip_ascii(is_name_byte);
        if name.is_empty() {
            return Err(format!("{line}:{col}: expected a name after '^'"));
        }
        Ok(Token {
            tok: Tok::Label(name),
            line,
            col,
        })
    }

    /// The first lexing error from here to the end of the input, if any.
    pub fn first_error(mut self) -> Option<String> {
        loop {
            match self.next_token() {
                Err(e) => return Some(e),
                Ok(Token { tok: Tok::Eof, .. }) => return None,
                Ok(_) => {}
            }
        }
    }
}

/// A location component.
fn number(s: &str, line: u32, col: u32) -> Result<u32, String> {
    s.parse()
        .map_err(|_| format!("{line}:{col}: location {s} is too large"))
}
