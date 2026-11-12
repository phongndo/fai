/-!
# Lexer

Splits FIR text into tokens. Comments start with `//` and run to the end of the line. Integers
are decimal or hexadecimal (`0x1f`), with an optional `-`; a decimal with a fraction (`.` and
digits) or an exponent (`e` or `E`, an optional sign, and digits) is a float literal. A `-`
followed by a letter starts a name, so that `-inf` and `-nan` are names.
-/

namespace Fir

inductive Tok where
  /-- `%name` -/
  | value (s : String)
  /-- `@name` -/
  | global (s : String)
  /-- `@line:col` -/
  | loc (line col : Nat)
  /-- `?name` -/
  | hole (s : String)
  /-- `^name`, a block label -/
  | label (s : String)
  | ident (s : String)
  | int (n : Int)
  /-- A decimal with a fraction or an exponent, `1.5` or `-2e-3`, as written. -/
  | float (s : String)
  | str (s : String)
  /-- One of `( ) { } [ ] < > , : = ->` -/
  | sym (s : String)
  | eof
  deriving BEq, Repr, Inhabited

def Tok.describe : Tok → String
  | .value s => s!"%{s}"
  | .global s => s!"@{s}"
  | .loc l c => s!"@{l}:{c}"
  | .hole s => s!"?{s}"
  | .label s => s!"^{s}"
  | .ident s => s!"'{s}'"
  | .int n => s!"{n}"
  | .float s => s
  | .str s => s!"\"{s}\""
  | .sym s => s!"'{s}'"
  | .eof => "end of input"

structure Token where
  tok : Tok
  line : Nat
  col : Nat
  deriving Inhabited

private def isNameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.'

private def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

private structure LexState where
  chars : List Char
  line : Nat := 1
  col : Nat := 1

private def LexState.advance (s : LexState) : LexState :=
  match s.chars with
  | '\n' :: cs => { chars := cs, line := s.line + 1, col := 1 }
  | _ :: cs => { s with chars := cs, col := s.col + 1 }
  | [] => s

private def LexState.takeWhile (s : LexState) (p : Char → Bool) : String × LexState :=
  let cs := s.chars.takeWhile p
  (String.ofList cs, cs.foldl (fun st _ => st.advance) s)

partial def lex (input : String) : Except String (Array Token) :=
  go { chars := input.toList } #[]
where
  go (s : LexState) (acc : Array Token) : Except String (Array Token) :=
    let emit (t : Tok) (s' : LexState) := go s' (acc.push { tok := t, line := s.line, col := s.col })
    let fail {α} (msg : String) : Except String α := .error s!"{s.line}:{s.col}: {msg}"
    match s.chars with
    | [] => .ok (acc.push { tok := .eof, line := s.line, col := s.col })
    | c :: cs =>
      if c.isWhitespace then go s.advance acc
      else if c == '/' && cs.head? == some '/' then
        go (s.takeWhile (· != '\n')).2 acc
      else if c == '-' && cs.head? == some '>' then emit (.sym "->") s.advance.advance
      else if "(){}[]<>,:=".contains c then emit (.sym c.toString) s.advance
      else if c == '%' || c == '?' || c == '^' then
        let (name, s') := s.advance.takeWhile isNameChar
        if name.isEmpty then fail s!"expected a name after '{c}'"
        else
          let t := if c == '%' then .value name else if c == '?' then .hole name else .label name
          emit t s'
      else if c == '@' then
        let s1 := s.advance
        if s1.chars.head?.any Char.isDigit then
          let (l, s2) := s1.takeWhile Char.isDigit
          if s2.chars.head? != some ':' then fail "expected ':' in a location"
          else
            let (c', s3) := s2.advance.takeWhile Char.isDigit
            if c'.isEmpty then fail "expected a column number in a location"
            else emit (.loc l.toNat! c'.toNat!) s3
        else
          let (name, s') := s1.takeWhile isNameChar
          if name.isEmpty then fail "expected a name after '@'"
          else emit (.global name) s'
      else if c.isDigit || (c == '-' && cs.head?.any Char.isDigit) then
        let neg := c == '-'
        let s1 := if neg then s.advance else s
        match s1.chars with
        | '0' :: x :: h :: _ =>
          if (x == 'x' || x == 'X') && h.isHexDigit then
            let (hs, s') := s1.advance.advance.takeWhile Char.isHexDigit
            let n : Int := hs.toList.foldl (fun n c => n * 16 + hexDigit c) 0
            emit (.int (if neg then -n else n)) s'
          else number s acc neg s1
        | _ => number s acc neg s1
      else if c == '"' then
        let (body, s') := s.advance.takeWhile (· != '"')
        if s'.chars.isEmpty then fail "unterminated string"
        else emit (.str body) s'.advance
      else if c.isAlpha || c == '_' then
        let (name, s') := s.takeWhile isNameChar
        emit (.ident name) s'
      else if c == '-' && cs.head?.any Char.isAlpha then
        let (name, s') := s.advance.takeWhile isNameChar
        emit (.ident ("-" ++ name)) s'
      else fail s!"unexpected character '{c}'"
  /-- A decimal number after its sign: an integer, or a float literal with a fraction or an
  exponent. -/
  number (s : LexState) (acc : Array Token) (neg : Bool) (s1 : LexState) :
      Except String (Array Token) :=
    let (digits, s2) := s1.takeWhile Char.isDigit
    let (frac, s3) := match s2.chars with
      | '.' :: d :: _ => if d.isDigit then
          let (f, s3) := s2.advance.takeWhile Char.isDigit
          ("." ++ f, s3)
        else ("", s2)
      | _ => ("", s2)
    let (exp, s4) := match s3.chars with
      | e :: d :: rest =>
        if e == 'e' || e == 'E' then
          if d.isDigit then
            let (x, s4) := s3.advance.takeWhile Char.isDigit
            ("e" ++ x, s4)
          else if (d == '-' || d == '+') && rest.head?.any Char.isDigit then
            let (x, s4) := s3.advance.advance.takeWhile Char.isDigit
            ("e" ++ d.toString ++ x, s4)
          else ("", s3)
        else ("", s3)
      | _ => ("", s3)
    let sign := if neg then "-" else ""
    let t : Tok := if frac.isEmpty && exp.isEmpty then
        let n : Int := digits.toNat!
        .int (if neg then -n else n)
      else .float (sign ++ digits ++ frac ++ exp)
    go s4 (acc.push { tok := t, line := s.line, col := s.col })

end Fir
