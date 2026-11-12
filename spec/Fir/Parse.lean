import Fir.Syntax
import Fir.Lex

/-!
# Parser

Parses FIR-0 text:

```
func @sum(%n: i32) -> i32 loc "sum.c" {
  %zero: i32 = int.const 0 @1:3
  %r: i32 = cf.loop progress iter(%i: i32 = %zero, %acc: i32 = %zero) @2:3 {
    %done: i1 = int.cmp.sge %i, %n
    cf.if %done {
      cf.break %acc
    }
    %one: i32 = int.const 1
    %acc2: i32 [range.s(0, 1000) assume] = int.add.nsw %acc, %i
    %i2: i32 = int.add.nsw %i, %one
    cf.continue %i2, %acc2
  }
  func.ret %r
}
```

An op's location goes after its operands and before its regions. Op names carry their modifiers
(`int.add.nsw`, `int.div.s.trap.wrap`). Each op's readable form is declared with the op (see
`Fir.OpDSL` and the declarations in `Fir.Syntax`); this parser reads it from the op table.

Every op also has a generic form, the same for all ops:

```
op       ::= [result, … "="] STRING "(" [operand, …] ")" [attrs] [LOC] [regions]
attrs    ::= "{" [IDENT "=" value, …] "}"
regions  ::= "(" [region, …] ")"
region   ::= ["(" [result, …] ")"] "{" op* "}"
```

`%s: i32 = "int.add.nsw"(%a, %b)`, `"mem.store"(%v, %p) {ty = i32, align = 4} @3:5`,
`%r: i32 = "cf.loop"(%z) {progress = false} ((%i: i32) { … })`. The string is the op's name with
its modifiers. The attributes are the op's immediates, named after its fields, each given once in
any order; their values are written as in the readable form, except that a flag is `true` or
`false`. Operand and region counts aren't checked here; the verifier checks them. The printer
uses the readable form whenever the op's shape fits it, and the generic form otherwise.
-/

namespace Fir

structure PState where
  toks : Array Token
  pos : Nat := 0

abbrev P := StateT PState (Except String)

instance : Inhabited (P α) := ⟨throw "unreachable"⟩

namespace P

def peekToken : P Token := do
  let s ← get
  pure (s.toks[s.pos]?.getD default)

def peek : P Tok := return (← peekToken).tok

def next : P Tok := do
  let t ← peek
  modify fun s => { s with pos := s.pos + 1 }
  pure t

def fail (msg : String) : P α := do
  let t ← peekToken
  throw s!"{t.line}:{t.col}: {msg}"

def expectSym (sym : String) : P Unit := do
  let t ← peek
  if t == .sym sym then discard next
  else fail s!"expected '{sym}' but found {t.describe}"

def trySym (sym : String) : P Bool := do
  if (← peek) == .sym sym then discard next; pure true else pure false

def tryIdent (name : String) : P Bool := do
  if (← peek) == .ident name then discard next; pure true else pure false

def ident : P String := do
  match ← peek with
  | .ident s => discard next; pure s
  | t => fail s!"expected a name but found {t.describe}"

def value : P String := do
  match ← peek with
  | .value s => discard next; pure s
  | t => fail s!"expected a %value but found {t.describe}"

def int : P Int := do
  match ← peek with
  | .int n => discard next; pure n
  | t => fail s!"expected an integer but found {t.describe}"

/-- More `, item`s after the ones already parsed. -/
partial def commaTail (p : P α) (acc : Array α) : P (List α) := do
  if ← trySym "," then commaTail p (acc.push (← p)) else pure acc.toList

/-- One or more comma-separated items. -/
def sepBy1 (p : P α) : P (List α) := do commaTail p #[← p]

/-- Comma-separated items, possibly none, ended by `close`. -/
def sepBy (p : P α) (close : String) : P (List α) := do
  if ← trySym close then return []
  let items ← sepBy1 p
  expectSym close
  pure items

def ty : P Ty := do
  let s ← ident
  match s.toList with
  | ['p', 't', 'r'] => pure .ptr
  | c :: digits =>
    -- Plain digits only: `toNat?` would also accept `_` separators.
    let width := if !digits.isEmpty && digits.all Char.isDigit then (String.ofList digits).toNat? else none
    match c, width with
    | 'i', some w => pure (.int w)
    | 'b', some w => pure (.byte w)
    | _, _ => fail s!"unknown type '{s}'"
  | _ => fail s!"unknown type '{s}'"

def trust : P Trust := do
  match ← ident with
  | "assume" => pure .assume
  | "check" => pure .check
  | "proved" => pure .proved
  | s => fail s!"expected assume, check, or proved but found '{s}'"

def nat : P Nat := do
  let n ← int
  if n < 0 then fail "expected a non-negative integer" else pure n.toNat

def range : P (Int × Int) := do
  expectSym "("
  let lo ← int
  expectSym ","
  let hi ← int
  expectSym ")"
  pure (lo, hi)

def fact : P TrustedFact := do
  let name ← ident
  let f ← match name with
    | "range.s" => do let (lo, hi) ← range; pure (Fact.rangeS lo hi)
    | "range.u" => do let (lo, hi) ← range; pure (Fact.rangeU lo hi)
    | "nonnull" => pure .nonnull
    | "noalias" => pure .noalias
    | "readonly" => pure .readonly
    | "align" => do expectSym "("; let n ← nat; expectSym ")"; pure (.align n)
    | _ => fail s!"unknown fact '{name}'"
  pure ⟨f, ← trust⟩

def result : P Result := do
  let name ← value
  expectSym ":"
  let t ← ty
  let facts ← if ← trySym "[" then sepBy fact "]" else pure []
  pure { name, ty := t, facts }

def operand : P Operand := do
  match ← peek with
  | .value s => discard next; pure (.var s)
  | .hole s => discard next; expectSym ":"; pure (.hole s (← ty))
  | t => fail s!"expected an operand but found {t.describe}"

/-- Zero or more comma-separated operands. -/
def variadic : P (List Operand) := do
  match ← peek with
  | .value _ | .hole _ => sepBy1 operand
  | _ => pure []

def optLoc : P (Option Loc) := do
  match ← peek with
  | .loc l c => discard next; pure (some ⟨l, c⟩)
  | _ => pure none

/-- The kind an op name spells, with its immediates reset (see `opNames`). -/
def opKind (name : String) : Option OpKind :=
  (opNames.find? fun s => s.parses && s.text == name).map (·.value)

/-- `@name` -/
def funcName : P String := do
  match ← peek with
  | .global s => discard next; pure s
  | t => fail s!"expected a function name like @f but found {t.describe}"

/-- An immediate, as the readable form writes it. A flag is a keyword named after its field. -/
def imm (f : Field) : P Imm :=
  match f.ty with
  | .int => .int <$> int
  | .nat | .align => .nat <$> nat
  | .symbol => .str <$> ident
  | .func => .str <$> funcName
  | .ty => .ty <$> ty
  | .flag | .mod _ => .flag <$> tryIdent f.name

/-- `%name: type = %init` -/
def iterArg : P (Result × Operand) := do
  let r ← result
  expectSym "="
  pure (r, ← operand)

/-- The readable form after the op name, up to its location: the kind with its immediates, the
operands, and the parameters `%iter` gives the first region. -/
def head (kind : OpKind) (d : OpDecl) : P (OpKind × List Operand × List Result) := do
  let mut kind := kind
  let mut args := []
  let mut params := []
  for item in d.head do
    match item with
    | .imm f => kind := kind.setImm f (← imm ((d.field? f).getD default))
    | .operand => args := args ++ [← operand]
    | .comma => expectSym ","
    | .keyword kw => unless ← tryIdent kw do fail s!"expected '{kw}'"
    | .variadic => args := args ++ (← variadic)
    | .args => expectSym "("; args := args ++ (← sepBy operand ")")
    | .iter =>
      if ← tryIdent "iter" then
        expectSym "("
        let iter ← sepBy iterArg ")"
        params := iter.map (·.1)
        args := args ++ iter.map (·.2)
    | .region _ => pure ()
  pure (kind, args, params)

/-- A generic-form attribute value: as in the readable form, except that a flag is `true` or
`false`. -/
def attrValue (f : Field) : P Imm :=
  match f.ty with
  | .flag => do
    match ← peek with
    | .ident "true" => discard next; pure (.flag true)
    | .ident "false" => discard next; pure (.flag false)
    | t => fail s!"expected true or false but found {t.describe}"
  | _ => imm f

/-- `key = value`, for the op `name`, whose attributes `seen` are already given. -/
def attr (d : OpDecl) (name : String) (seen : List String) : P (String × Imm) := do
  let key ← match ← peek with
    | .ident key => pure key
    | t => fail s!"expected a name but found {t.describe}"
  let some f := d.imms.find? (·.name == key) | fail s!"{name} has no attribute '{key}'"
  if seen.contains key then fail s!"attribute '{key}' is given twice"
  discard next
  expectSym "="
  pure (key, ← attrValue f)

/-- `{key = value, …}`: every immediate of the op `name`, each once, in any order. -/
def attrs (kind : OpKind) (name : String) : P OpKind := do
  let d := kind.decl
  let mut kind := kind
  let mut seen := []
  if ← trySym "{" then
    if !(← trySym "}") then
      repeat
        let (key, v) ← attr d name seen
        kind := kind.setImm key v
        seen := key :: seen
        if !(← trySym ",") then break
      expectSym "}"
  for f in d.imms do
    unless seen.contains f.name do fail s!"{name} needs the attribute '{f.name}'"
  pure kind

mutual
  partial def region (params : List Result) : P Region := do
    expectSym "{"
    let mut ops := #[]
    while !(← trySym "}") do
      if (← peek) == .eof then fail "expected '}'"
      ops := ops.push (← op)
    pure (.mk params ops.toList)

  /-- A region in the generic form: `(%x: T, …) { … }`, the parameters optional. -/
  partial def genericRegion : P Region := do
    let params ← if ← trySym "(" then sepBy result ")" else pure []
    region params

  partial def op : P Op := do
    let results ←
      match ← peek with
      | .value _ =>
        let rs ← sepBy1 result
        expectSym "="
        pure rs
      | _ => pure []
    match ← peek with
    | .str name =>
      -- The generic form.
      discard next
      let some kind := opKind name | fail s!"unknown op '{name}'"
      expectSym "("
      let args ← sepBy operand ")"
      let kind ← attrs kind name
      let loc ← optLoc
      let regions ← if ← trySym "(" then sepBy genericRegion ")" else pure []
      pure (.mk kind results args regions loc)
    | _ =>
      let name ← ident
      let some kind := opKind name | fail s!"unknown op '{name}'"
      let d := kind.decl
      let (kind, args, params) ← head kind d
      let loc ← optLoc
      let mut regions := #[]
      for kw in d.regions do
        let r ← match kw with
          | none => region (if regions.isEmpty then params else [])
          | some kw => if ← tryIdent kw then region [] else pure (.mk [] [])
        regions := regions.push r
      pure (.mk kind results args regions.toList loc)
end

def func : P Func := do
  unless ← tryIdent "func" do fail "expected 'func'"
  let name ← match ← peek with
    | .global s => discard next; pure s
    | t => fail s!"expected a function name like @main but found {t.describe}"
  expectSym "("
  let params ← sepBy result ")"
  let rets ← if ← trySym "->" then do
      if ← trySym "(" then sepBy ty ")" else pure [← ty]
    else pure []
  let file ← if ← tryIdent "loc" then do
      match ← peek with
      | .str s => discard next; pure (some s)
      | t => fail s!"expected a file name string but found {t.describe}"
    else pure none
  let body ← region params
  pure { name, rets, file, body }

/-- `memspace default ptr 64 addr 64` -/
def memspace : P SpaceCfg := do
  let name ← ident
  unless name == "default" do fail "only the default memory space can be declared for now"
  unless ← tryIdent "ptr" do fail "expected 'ptr'"
  let ptrBits ← nat
  unless ← tryIdent "addr" do fail "expected 'addr'"
  pure { ptrBits, addrBits := ← nat }

def module : P Module := do
  let mut funcs := #[]
  let mut space : SpaceCfg := {}
  while (← peek) != .eof do
    if ← tryIdent "memspace" then space ← memspace
    else funcs := funcs.push (← func)
  pure { space, funcs := funcs.toList }

end P

def parseModule (input : String) : Except String Module := do
  let toks ← lex input
  let (m, _) ← P.module.run { toks }
  pure m

end Fir
