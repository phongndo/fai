import Fir.Syntax
import Fir.Lex
import Fir.FloatText

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
`false`, and a branch target is its label and argument count (`^b(2)`, or `^b` for none), its
arguments being among the operands. Operand and region counts aren't checked here; the verifier
checks them. The printer uses the readable form whenever the op's shape fits it, and the generic
form otherwise.

## Modules

A module is a sequence of `layer`, `memspace`, `global`, `extern`, and `func` declarations. `layer
hfir`, `layer mfir`, or `layer lfir aarch64` names its layer (decision: Layers), at most once;
without it the module is HFIR. An LFIR target must be one of `targets`.

## Blocks

`cf.blocks` holds labeled blocks, and branches name them:

```
%r: i32 = cf.blocks {
^entry:
  cf.br ^loop(%zero)
^loop(%i: i32):
  %done: i1 = int.cmp.sge %i, %n
  cf.cond_br %done, ^exit, ^loop(%i2)
^exit:
  cf.yield %i
}
```

A block is a label, its parameters in parentheses (left out when there are none), `:`, and its
ops, up to the next label or the closing `}`. A branch target is a label with its arguments in
parentheses (left out when there are none); `cf.switch` writes its cases as
`[1: ^a, -1: ^b(%x)]`. In the generic form, a region may start with a label:
`"cf.blocks"() {progress = false} (^entry { … }, ^loop(%i: i32) { … })`.
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

/-- A target register: `x0`…`x30`, `sp`, `xzr`, or `v` and a number. -/
def reg : P Reg := do
  match ← peek with
  | .ident s =>
    match Reg.ofString? s with
    | some r => discard next; pure r
    | none => fail s!"expected a register like x0 or v1 but found '{s}'"
  | t => fail s!"expected a register like x0 or v1 but found {t.describe}"

def labelName : P String := do
  match ← peek with
  | .label s => discard next; pure s
  | t => fail s!"expected a block label like ^b but found {t.describe}"

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

def nat : P Nat := do
  let n ← int
  if n < 0 then fail "expected a non-negative integer" else pure n.toNat

/-- A type: `i32`, `ptr`, `b8`, `f32`, `f64`, `struct<C>{i32, ptr}`, `array<4 x i32>`,
`func<(i32, ptr) -> i32>`, `union<i32, ptr>`, or `slice`. -/
partial def ty : P Ty := do
  let s ← ident
  match s with
  | "ptr" => pure .ptr
  | "struct" =>
    expectSym "<"
    let p ← match ← ident with
      | "C" => pure Policy.c
      | "packed" => pure .packed
      | "auto" => pure .auto
      | p => fail s!"unknown struct layout '{p}'"
    expectSym ">"
    expectSym "{"
    pure (.struct p (← sepBy ty "}"))
  | "array" =>
    expectSym "<"
    let n ← nat
    unless ← tryIdent "x" do fail "expected 'x'"
    let t ← ty
    expectSym ">"
    pure (.array n t)
  | "slice" => pure .slice
  | "f32" => pure (.float .f32)
  | "f64" => pure (.float .f64)
  | "union" =>
    expectSym "<"
    pure (.union (← sepBy ty ">"))
  | "func" =>
    expectSym "<"
    expectSym "("
    let ps ← sepBy ty ")"
    let rs ← if ← trySym "->" then do
        if ← trySym "(" then sepBy ty ")" else pure [← ty]
      else pure []
    expectSym ">"
    pure (.func ps rs)
  | _ =>
  match s.toList with
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

/-- A branch target in the readable form: `^b` or `^b(%x, …)`, with its arguments. -/
def succ : P (Succ × List Operand) := do
  let label ← labelName
  let args ← if ← trySym "(" then sepBy operand ")" else pure []
  pure ({ label, nargs := args.length }, args)

/-- `[k: target, …]`, with the targets' arguments in order. -/
def cases (target : P (Succ × List Operand)) : P (Cases × List Operand) := do
  expectSym "["
  let items ← sepBy (do
    let k ← int
    expectSym ":"
    let (s, args) ← target
    pure ((k, s), args)) "]"
  pure (items.map (·.1), items.flatMap (·.2))

/-- A branch target in the generic form: `^b` or `^b(n)`, for `n` arguments. -/
def genericSucc : P (Succ × List Operand) := do
  let label ← labelName
  let nargs ← if ← trySym "(" then do let n ← nat; expectSym ")"; pure n else pure 0
  pure ({ label, nargs }, [])

/-- `@name` -/
def globalName : P String := do
  match ← peek with
  | .global s => discard next; pure s
  | t => fail s!"expected a global name like @g but found {t.describe}"

/-- An immediate, as the readable form writes it. A flag is a keyword named after its field.
Branch targets are read here as the generic form writes them; the readable form's go with
their operands (`head`). -/
def imm (f : Field) : P Imm :=
  match f.ty with
  | .int => .int <$> int
  | .nat | .align | .index => .nat <$> nat
  | .symbol => .str <$> ident
  | .func => .str <$> funcName
  | .global => .str <$> globalName
  | .ty => .ty <$> ty
  | .succ => (.succ ·.1) <$> genericSucc
  | .cases => (.cases ·.1) <$> cases genericSucc
  | .reg => .reg <$> reg
  -- A float constant's bits, in the generic form.
  | .float => .nat <$> nat
  | .flag | .mod _ => .flag <$> tryIdent f.name

/-- A float literal (`Fir.FloatText`): a decimal, an integer, `inf`, `-inf`, `nan`, `-nan`, or
`nan(0x…)`. -/
def floatLit : P Float.Lit := do
  let lit? : Option Float.Lit ← match ← peek with
    | .float s => discard next; pure (Float.parseLit s)
    | .int n => discard next; pure (some (.dec (decide (n < 0)) n.natAbs 0))
    | .ident s =>
      match s with
      | "inf" | "-inf" | "nan" | "-nan" =>
        discard next
        let neg := s.startsWith "-"
        if s.endsWith "inf" then pure (some (.inf neg))
        else if ← trySym "(" then
          let p ← nat
          expectSym ")"
          pure (some (.nan neg (some p)))
        else pure (some (.nan neg none))
      | _ => pure none
    | _ => pure none
  match lit? with
  | some l => pure l
  | none => fail s!"expected a float like 1.5, inf, or nan but found {(← peek).describe}"

/-- A float constant's bits, read as the float of the op's one result type. -/
def floatBits (results : List Result) : P Nat := do
  let lit ← floatLit
  match results with
  | [{ ty := .float t, .. }] =>
    match lit.toBits t.fmt with
    | some b => pure b.toNat
    | none => fail s!"the NaN payload doesn't fit {t.name}"
  | _ => fail "a float constant needs one float result"

/-- `%name: type = %init` -/
def iterArg : P (Result × Operand) := do
  let r ← result
  expectSym "="
  pure (r, ← operand)

/-- The readable form after the op name, up to its location: the kind with its immediates, the
operands, and the parameters `%iter` gives the first region. -/
def head (kind : OpKind) (d : OpDecl) (results : List Result) :
    P (OpKind × List Operand × List Result) := do
  let mut kind := kind
  let mut args := []
  let mut params := []
  for item in d.head do
    match item with
    | .imm f =>
      let field := (d.field? f).getD default
      match field.ty with
      | .succ =>
        let (s, ops) ← succ
        kind := kind.setImm f (.succ s)
        args := args ++ ops
      | .cases =>
        let (cs, ops) ← cases succ
        kind := kind.setImm f (.cases cs)
        args := args ++ ops
      | .float => kind := kind.setImm f (.nat (← floatBits results))
      | _ => kind := kind.setImm f (← imm field)
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
    | .region _ | .blocks => pure ()
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
  partial def region (params : List Result) (label : Option String := none) : P Region := do
    expectSym "{"
    let mut ops := #[]
    while !(← trySym "}") do
      if (← peek) == .eof then fail "expected '}'"
      ops := ops.push (← op)
    pure (.mk params ops.toList label)

  /-- A region in the generic form: `^b(%x: T, …) { … }`, the label and parameters optional. -/
  partial def genericRegion : P Region := do
    let label ← match ← peek with
      | .label l => discard next; pure (some l)
      | _ => pure none
    let params ← if ← trySym "(" then sepBy result ")" else pure []
    region params label

  /-- `cf.blocks`'s blocks: `{ ^a: ops ^b(%x: T): ops … }`. -/
  partial def blocks : P (List Region) := do
    expectSym "{"
    let mut bs := #[]
    while !(← trySym "}") do
      let label ← labelName
      let params ← if ← trySym "(" then sepBy result ")" else pure []
      expectSym ":"
      let mut ops := #[]
      repeat
        match ← peek with
        | .label _ | .sym "}" => break
        | .eof => fail "expected '}'"
        | _ => ops := ops.push (← op)
      bs := bs.push (.mk params ops.toList (some label))
    pure bs.toList

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
      let (kind, args, params) ← head kind d results
      let loc ← optLoc
      let mut regions := #[]
      for kw in d.regions do
        let r ← match kw with
          | none => region (if regions.isEmpty then params else [])
          | some kw =>
            if ← tryIdent kw then
              region (← if ← trySym "(" then sepBy result ")" else pure [])
            else pure (.mk [] [] none)
        regions := regions.push r
      if d.hasBlocks then regions := regions ++ (← blocks).toArray
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

/-- `memspace default ptr 64 addr 64 [align 8] [int 8:1 16:2 …]` -/
def memspace : P SpaceCfg := do
  let name ← ident
  unless name == "default" do fail "only the default memory space can be declared for now"
  unless ← tryIdent "ptr" do fail "expected 'ptr'"
  let ptrBits ← nat
  unless ← tryIdent "addr" do fail "expected 'addr'"
  let addrBits ← nat
  let ptrAlign ← if ← tryIdent "align" then nat else pure (SpaceCfg.naturalAlign ptrBits)
  let mut ints := defaultInts
  if ← tryIdent "int" then
    ints := []
    repeat
      let w ← nat
      expectSym ":"
      ints := ints ++ [(w, ← nat)]
      unless (← peek) matches .int _ do break
  pure { ptrBits, addrBits, ptrAlign, ints }

/-- Hex digits, two per byte. -/
def hexBytes (s : String) : Option (List Nat) :=
  let digit (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else none
  let rec go : List Char → Option (List Nat)
    | [] => some []
    | a :: b :: rest => do
      let x ← digit a
      let y ← digit b
      pure ((x * 16 + y) :: (← go rest))
    | [_] => none
  go s.toList

/-- `zero`, an integer, `null`, `@name`, `bytes "00ff"`, or `{init, …}`. -/
partial def init : P Init := do
  match ← peek with
  | .ident "zero" => discard next; pure .zero
  | .ident "null" => discard next; pure .null
  | .ident "bytes" =>
    discard next
    match ← peek with
    | .str s =>
      let some bs := hexBytes s | fail "expected two lowercase hex digits per byte"
      discard next
      pure (.bytes bs)
    | t => fail s!"expected a string of hex digits but found {t.describe}"
  | .int n => discard next; pure (.int n)
  | .global s => discard next; pure (.sym s)
  | .sym "{" => discard next; pure (.list (← sepBy init "}"))
  | t => fail s!"expected an initializer but found {t.describe}"

/-- `global [const] @name: T [align N] = INIT` -/
def global : P Global := do
  let const ← tryIdent "const"
  let name ← globalName
  expectSym ":"
  let t ← ty
  let align ← if ← tryIdent "align" then nat else pure 1
  expectSym "="
  pure { name, ty := t, const, align, init := ← init }

/-- `args`, `exposed`, or `globals`. -/
def memClass : P MemClass := do
  match ← ident with
  | "args" => pure .args
  | "exposed" => pure .exposed
  | "globals" => pure .globals
  | s => fail s!"expected args, exposed, or globals but found '{s}'"

/-- `read(args)`, `write(exposed)`, `alloc`, `free`, `trap`, `diverge`, or `unwind`. -/
def extEffect : P ExtEffect := do
  match ← ident with
  | "read" => do expectSym "("; let m ← memClass; expectSym ")"; pure (.read m)
  | "write" => do expectSym "("; let m ← memClass; expectSym ")"; pure (.write m)
  | "alloc" => pure .alloc
  | "free" => pure .free
  | "trap" => pure .trap
  | "diverge" => pure .diverge
  | "unwind" => pure .unwind
  | s => fail s!"unknown effect '{s}'"

/-- `extern func @name(T, …) [-> T | -> (T, …)] effects[E, …] TRUST`, after `extern`. -/
def extern : P Extern := do
  unless ← tryIdent "func" do fail "expected 'func' after 'extern'"
  let name ← match ← peek with
    | .global s => discard next; pure s
    | t => fail s!"expected a function name like @main but found {t.describe}"
  expectSym "("
  let params ← sepBy ty ")"
  let rets ← if ← trySym "->" then do
      if ← trySym "(" then sepBy ty ")" else pure [← ty]
    else pure []
  unless ← tryIdent "effects" do fail "expected 'effects' after an external function's signature"
  expectSym "["
  let effects ← sepBy extEffect "]"
  pure { name, params, rets, effects, trust := ← trust }

/-- `hfir`, `mfir`, or `lfir TARGET`, after `layer`. -/
def layer : P Layer := do
  match ← peek with
  | .ident "hfir" => discard next; pure .hfir
  | .ident "mfir" => discard next; pure .mfir
  | .ident "lfir" =>
    discard next
    match ← peek with
    | .ident t =>
      unless targets.contains t do
        fail s!"unknown target '{t}': expected {", ".intercalate targets}"
      discard next
      pure (.lfir t)
    | t => fail s!"expected a target after lfir but found {t.describe}"
  | .ident s => fail s!"unknown layer '{s}': expected hfir, mfir, or lfir"
  | t => fail s!"expected a layer but found {t.describe}"

def module : P Module := do
  let mut funcs := #[]
  let mut globals := #[]
  let mut externs := #[]
  let mut space : SpaceCfg := {}
  let mut layer? : Option Layer := none
  while (← peek) != .eof do
    if (← peek) == .ident "layer" then
      if layer?.isSome then fail "the module's layer is declared more than once"
      discard next
      layer? := some (← layer)
    else if ← tryIdent "memspace" then space ← memspace
    else if ← tryIdent "global" then globals := globals.push (← global)
    else if ← tryIdent "extern" then externs := externs.push (← extern)
    else funcs := funcs.push (← func)
  pure { layer := layer?.getD .hfir, space, globals := globals.toList, externs := externs.toList,
         funcs := funcs.toList }

end P

def parseModule (input : String) : Except String Module := do
  let toks ← lex input
  let (m, _) ← P.module.run { toks }
  pure m

end Fir
