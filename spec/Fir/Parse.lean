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
(`int.add.nsw`, `int.div.s.trap.wrap`).
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

/-- Exactly `n` comma-separated operands. -/
def operands (n : Nat) : P (List Operand) := do
  let mut acc := #[]
  for i in [0:n] do
    if i > 0 then expectSym ","
    acc := acc.push (← operand)
  pure acc.toList

/-- Zero or more comma-separated operands (for terminators). -/
def variadic : P (List Operand) := do
  match ← peek with
  | .value _ | .hole _ => sepBy1 operand
  | _ => pure []

/-- `, align N` -/
def alignArg : P Nat := do
  expectSym ","
  unless ← tryIdent "align" do fail "expected 'align'"
  nat

def optLoc : P (Option Loc) := do
  match ← peek with
  | .loc l c => discard next; pure (some ⟨l, c⟩)
  | _ => pure none

def ovf : List String → Option Ovf
  | ["wrap"] => some .wrap
  | ["nsw"] => some .nsw
  | ["nuw"] => some .nuw
  | ["nsw", "nuw"] => some .nswNuw
  | ["s", "trap"] => some (.trap true)
  | ["u", "trap"] => some (.trap false)
  | ["s", "sat"] => some (.sat true)
  | ["u", "sat"] => some (.sat false)
  | ["s", "ub"] => some (.ub true)
  | ["u", "ub"] => some (.ub false)
  | _ => none

def zeroEdge : String → Option Edge
  | "ub" => some .ub
  | "trap" => some .trap
  | "total" => some .total
  | _ => none

def ovfEdge : String → Option Edge
  | "ub" => some .ub
  | "trap" => some .trap
  | "wrap" => some .wrap
  | _ => none

/-- `(zero, overflow)` edges. One modifier covers both cases. -/
def divEdges (signed : Bool) : List String → Option (Edge × Edge)
  | [z] => do
    let z ← zeroEdge z
    pure (z, if z == .total then .wrap else z)
  | [z, o] => if signed then do pure (← zeroEdge z, ← ovfEdge o) else none
  | _ => none

def shiftEdge : List String → Option ShiftEdge
  | ["ub"] => some .ub
  | ["trap"] => some .trap
  | ["mask"] => some .mask
  | ["total"] => some .total
  | _ => none

def pred : String → Option Pred
  | "eq" => some .eq | "ne" => some .ne
  | "slt" => some .slt | "sle" => some .sle | "sgt" => some .sgt | "sge" => some .sge
  | "ult" => some .ult | "ule" => some .ule | "ugt" => some .ugt | "uge" => some .uge
  | _ => none

/-- Decode an op name with its modifiers. -/
def opKind (name : String) : Option OpKind :=
  match name.splitOn "." with
  | ["int", "const"] => some (.const 0)
  | ["poison"] => some .poison
  | ["freeze"] => some .freeze
  | ["copy"] => some .copy
  | ["select"] => some .select
  | "int" :: "add" :: m => (ovf m).map (.arith .add)
  | "int" :: "sub" :: m => (ovf m).map (.arith .sub)
  | "int" :: "mul" :: m => (ovf m).map (.arith .mul)
  | ["int", "and"] => some (.bit .and)
  | ["int", "or"] => some (.bit .or)
  | ["int", "xor"] => some (.bit .xor)
  | "int" :: "div" :: "s" :: m => (divEdges true m).map fun (z, o) => .div .divS z o
  | "int" :: "div" :: "u" :: m => (divEdges false m).map fun (z, o) => .div .divU z o
  | "int" :: "rem" :: "s" :: m => (divEdges true m).map fun (z, o) => .div .remS z o
  | "int" :: "rem" :: "u" :: m => (divEdges false m).map fun (z, o) => .div .remU z o
  | "int" :: "shl" :: m => (shiftEdge m).map (.shift .shl)
  | "int" :: "shr" :: "u" :: m => (shiftEdge m).map (.shift .shrU)
  | "int" :: "shr" :: "s" :: m => (shiftEdge m).map (.shift .shrS)
  | ["int", "cmp", p] => (pred p).map .cmp
  | ["int", "zext"] => some .zext
  | ["int", "sext"] => some .sext
  | ["int", "trunc", "wrap"] => some (.trunc .wrap)
  | ["int", "trunc", "nsw"] => some (.trunc .nsw)
  | ["int", "trunc", "nuw"] => some (.trunc .nuw)
  | ["cf", "if"] => some .if_
  | ["cf", "loop"] => some (.loop false)
  | ["cf", "yield"] => some .yield
  | ["cf", "break"] => some .brk
  | ["cf", "continue"] => some .cont
  | ["func", "ret"] => some .ret
  | ["ptr", "offset", "inbounds"] => some (.ptrOffset true)
  | ["ptr", "offset", "wrap"] => some (.ptrOffset false)
  | ["ptr", "addr"] => some .ptrAddr
  | ["ptr", "expose"] => some .ptrExpose
  | ["ptr", "from_exposed"] => some .ptrFromExposed
  | ["ptr", "with_addr"] => some .ptrWithAddr
  | ["ptr", "null"] => some .ptrNull
  | ["ptr", "cmp", p] => (pred p).map .ptrCmp
  | ["mem", "stack"] => some (.memStack 0 1)
  | ["mem", "alloc", "null"] => some (.memAlloc .null "" 1)
  | ["mem", "alloc", "trap"] => some (.memAlloc .trap "" 1)
  | ["mem", "free"] => some (.memFree "")
  | ["mem", "load"] => some (.load 1)
  | ["mem", "store"] => some (.store .ptr 1)
  | ["func", "call"] => some (.call "")
  | _ => none

/-- How many operands an op without regions takes, or `none` if variadic. -/
def arity : OpKind → Option Nat
  | .const _ | .poison | .ptrNull => some 0
  | .freeze | .copy | .zext | .sext | .trunc _ | .ptrAddr | .ptrExpose | .ptrFromExposed => some 1
  | .select => some 3
  | .yield | .brk | .cont | .ret => none
  | _ => some 2

mutual
  partial def region (params : List Result) : P Region := do
    expectSym "{"
    let mut ops := #[]
    while !(← trySym "}") do
      if (← peek) == .eof then fail "expected '}'"
      ops := ops.push (← op)
    pure (.mk params ops.toList)

  partial def op : P Op := do
    let results ←
      match ← peek with
      | .value _ =>
        let rs ← sepBy1 result
        expectSym "="
        pure rs
      | _ => pure []
    let name ← ident
    let some kind := opKind name | fail s!"unknown op '{name}'"
    match kind with
    | .const _ =>
      let n ← int
      pure (.mk (.const n) results [] [] (← optLoc))
    | .memStack .. =>
      let size ← nat
      let align ← alignArg
      pure (.mk (.memStack size align) results [] [] (← optLoc))
    | .memAlloc fail .. =>
      let family ← ident
      let n ← operand
      let align ← alignArg
      pure (.mk (.memAlloc fail family align) results [n] [] (← optLoc))
    | .memFree _ =>
      let family ← ident
      let p ← operand
      pure (.mk (.memFree family) results [p] [] (← optLoc))
    | .load _ =>
      let p ← operand
      let align ← alignArg
      pure (.mk (.load align) results [p] [] (← optLoc))
    | .store .. =>
      let t ← ty
      let v ← operand
      expectSym ","
      let p ← operand
      let align ← alignArg
      pure (.mk (.store t align) results [v, p] [] (← optLoc))
    | .call _ =>
      let callee ← match ← peek with
        | .global s => discard next; pure s
        | t => fail s!"expected a function name like @f but found {t.describe}"
      expectSym "("
      let args ← sepBy operand ")"
      pure (.mk (.call callee) results args [] (← optLoc))
    | .if_ =>
      let c ← operand
      let loc ← optLoc
      let thn ← region []
      let els ← if ← tryIdent "else" then region [] else pure (.mk [] [])
      pure (.mk .if_ results [c] [thn, els] loc)
    | .loop _ =>
      let progress ← tryIdent "progress"
      let iter ← if ← tryIdent "iter" then do
          expectSym "("
          sepBy iterArg ")"
        else pure []
      let loc ← optLoc
      let body ← region (iter.map (·.1))
      pure (.mk (.loop progress) results (iter.map (·.2)) [body] loc)
    | k =>
      let args ← match arity k with
        | some n => operands n
        | none => variadic
      pure (.mk k results args [] (← optLoc))

  /-- `%name: type = %init` -/
  partial def iterArg : P (Result × Operand) := do
    let r ← result
    expectSym "="
    pure (r, ← operand)
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
