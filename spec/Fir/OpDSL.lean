/-!
# Op declarations

Every op is declared once, with `fir_ops` (in `Fir.Syntax`). A declaration gives the op's
constructor and fields, its names, its text format, how its operands and results are typed, and
what it does to the world:

```
/-- `mem.load %p, align 4`: the result type is the accessed type. -/
op load (align : Align)
  name "mem.load"
  format "%, align {align}"
  effects read
  rule
    pow2 align
    operands [ptr]
    results t "mem.load has one result"
    loadable t "loaded"
```

From the declarations, the `fir_ops` macro generates the `OpKind` inductive, `OpKind.isTerminator`, the op
table `opDecls`, the name table `opNames`, and the functions that read and write an op's
immediates. The parser, printer, and verifier interpret the tables; `lake exe gen-rust` writes the
same tables, and the Rust `OpKind`, to `crates/fir/src/generated/ops.rs`.

**Fields.** `(zero ovf : Edge)` declares fields of the constructor. Fields of these types are
*immediates*, written in the op's format: `Int`, `Nat` (Rust `u64`), `Align` (a `Nat`; Rust
`u32`), `Symbol` (a dotted name such as `c.malloc`; a `String`), `Func` (a function, `@f`; a
`String`), `Ty`, `Flag` (a `Bool` written as a keyword named after the field), `Succ` (a branch
target `^b(%x, …)`, whose operands are the op's; Rust: an id into a side table), and `Cases`
(`cf.switch`'s `[k: ^b(…), …]`). Fields of any other type (`Bool` or an enum) are *modifiers*,
spelled in the op's name. The Rust variant names its fields when one is a `Bool`, a number, a
string, or a branch target; otherwise it is a tuple.

**Names.** `name "int.{op}.{ovf}"` spells the op: each `{fields}` slot is filled from a
vocabulary, the field type's `Spelled` instance or a named list (`{zero ovf : signedEdges}`), and
`with op := .divS` fixes a field. Several `name` lines may share a constructor. A spelling's text
is printed for its value only if no earlier spelling has the same value; later ones are aliases
the parser accepts.

**Format.** The text after the name, as a template: `{f}` is immediate `f`, `%` an operand,
`%*` zero or more operands, `(%*)` a parenthesized argument list, `%iter` a loop's optional
`iter(%x: T = %init, …)` (its operands, and the first region's parameters), `,` a comma, and a
word a keyword. `region` is a region; `else region` one introduced by a keyword, which may be
left out when empty; `blocks` is any number of labeled regions (`cf.blocks`). The op's location
goes after the format's last item before its regions.

**Rule.** How `checkSimple` types an op without regions, as checks run in order (`Check`).
Control-flow ops (`cf.*`, `func.ret`) have no rule; the verifier checks them against the regions
around them.

**Effects and tier.** Declared as data (decisions: Effects, Effect soundness, Extensibility).
Nothing consumes them yet.

`fir_ops` is a macro that uses only `Init`: importing `Lean` here would link the whole Lean
compiler into `fir-ref` (115 MB instead of 6) and initialize it on every run.
-/

namespace Fir

/-- A modifier's spelling in an op name. -/
structure Spelling (α : Type) where
  text : String
  value : α
  /-- Whether the parser accepts it. A spelling that doesn't parse names a value the parser
  never produces (an unsigned division whose overflow edge differs from its zero edge's), so
  that every value prints. -/
  parses : Bool := true
  deriving Repr

def sp (text : String) (value : α) (parses := true) : Spelling α := { text, value, parses }

/-- A type's modifier vocabulary: the spellings of its values, the printed one first. -/
class Spelled (α : Type) where
  spellings : List (Spelling α)

/-- The type of a declared field. -/
inductive FieldTy where
  | int
  | nat
  | align
  | symbol
  | func
  | ty
  | flag
  /-- A branch target, `^b(%x, …)`: its label and argument count (Rust: an id into a side table). -/
  | succ
  /-- `cf.switch`'s cases, `[k: ^b(…), …]`. -/
  | cases
  /-- A modifier: `Bool` or an enum, named here. -/
  | mod (type : String)
  deriving DecidableEq, Repr, Inhabited

def FieldTy.isImm : FieldTy → Bool
  | .mod _ => false
  | _ => true

structure Field where
  name : String
  ty : FieldTy
  deriving Repr, Inhabited

/-- One piece of an op's readable format. -/
inductive Item where
  | imm (field : String)
  | operand
  | comma
  | keyword (kw : String)
  | variadic
  | args
  | iter
  /-- A region; one introduced by a keyword is left out when empty. -/
  | region (kw : Option String)
  /-- `cf.blocks`'s labeled blocks, `{ ^a: … ^b(%x: T): … }`: any number of regions. -/
  | blocks
  deriving DecidableEq, Repr, Inhabited

/-- Read a format template. -/
partial def parseFormat (s : String) : Except String (List Item) := do
  let items ← go s.toList #[]
  pure (regions items.toList)
where
  go : List Char → Array Item → Except String (Array Item)
    | [], acc => pure acc
    | ' ' :: cs, acc => go cs acc
    | ',' :: cs, acc => go cs (acc.push .comma)
    | '(' :: '%' :: '*' :: ')' :: cs, acc => go cs (acc.push .args)
    | '%' :: '*' :: cs, acc => go cs (acc.push .variadic)
    | '%' :: 'i' :: 't' :: 'e' :: 'r' :: cs, acc => go cs (acc.push .iter)
    | '%' :: cs, acc => go cs (acc.push .operand)
    | '{' :: cs, acc =>
      let name := cs.takeWhile (· != '}')
      if name.length == cs.length then .error "unclosed '{'"
      else go (cs.drop (name.length + 1)) (acc.push (.imm (String.ofList name)))
    | cs@(c :: _), acc =>
      let w := cs.takeWhile fun c => c.isAlphanum || c == '_' || c == '.'
      if w.isEmpty then .error s!"unexpected '{c}'"
      else go (cs.drop w.length) (acc.push (.keyword (String.ofList w)))
  regions : List Item → List Item
    | .keyword "region" :: rest => .region none :: regions rest
    | .keyword "blocks" :: rest => .blocks :: regions rest
    | .keyword kw :: .keyword "region" :: rest => .region (some kw) :: regions rest
    | i :: rest => i :: regions rest
    | [] => []

/-- A type in a rule: a pointer, an address-sized integer, `iN`, or a name bound by an earlier
check or naming a `Ty` field. -/
inductive TyE where
  | ptr
  | addr
  | int (w : Nat)
  | name (n : String)
  deriving DecidableEq, Repr, Inhabited

/-- One check of an op's typing rule. Each fails with a fixed message unless one is given. -/
inductive Check where
  /-- `operands a b "msg"`: name the operand types, or fail if there aren't that many. -/
  | takeIns (vars : List String) (msg : String)
  /-- `results t "msg"`: name the result types, or fail if there aren't that many. -/
  | takeOuts (vars : List String) (msg : String)
  /-- `operands [ptr, addr]` or `operands "label" [addr]`: the operand types are these. -/
  | ins (label : String) (want : List TyE)
  /-- `results [ptr]`: the result types are these. -/
  | outs (want : List TyE)
  /-- `noResults` -/
  | noOuts
  /-- `same "label" [b] [a]`: the types on the left are the ones on the right. -/
  | same (label : String) (got want : List TyE)
  /-- `ints a t`: these are integers. -/
  | ints (ts : List TyE)
  /-- `pow2 align`: the field is a power of two. -/
  | pow2 (field : String)
  /-- `fits n t`: the integer field fits in `t`, signed or unsigned. -/
  | fits (field : String) (t : TyE)
  /-- `widens a t`: `t` is wider than `a`. -/
  | widens (a t : TyE)
  /-- `narrows a t`: `t` is narrower than `a`. -/
  | narrows (a t : TyE)
  /-- `loadable t "loaded"`: memory holds `t` in whole bytes. -/
  | loadable (t : TyE) (verb : String)
  /-- `deny ["ptr.cmp.slt"] "msg"`: fail on these op names. -/
  | deny (names : List String) (msg : String)
  /-- `call callee`: the operands and results match the function's signature. -/
  | call (field : String)
  deriving Repr, Inhabited

/-- Effect categories (decision: Effects); resource tags come later. -/
inductive Effect where
  | read | write | alloc | free | trap | diverge | unwind | sync | extern
  deriving DecidableEq, Repr, Inhabited

/-- How far an op's declared effects are trusted (decision: Effect soundness): proved against its
Lean semantics, checked automatically, or assumed to be anything (`extern`). Core ops are
`verified`: their semantics is the Lean interpreter. -/
inductive Tier where
  | verified | specified | opaque
  deriving DecidableEq, Repr, Inhabited

/-- What `fir_ops` records about an op. The parser, printer, and verifier read `fields`,
`items`, `terminator`, and `rule`; `effects` and `tier` are declared but not yet read. -/
structure OpDecl where
  /-- The Lean constructor. -/
  ctor : String
  /-- The Rust variant. -/
  rust : String
  doc : String
  fields : List Field
  format : String
  items : List Item := (parseFormat format).toOption.getD []
  terminator : Bool
  rule : Option (List Check)
  effects : List Effect
  tier : Tier
  deriving Repr, Inhabited

def OpDecl.imms (d : OpDecl) : List Field := d.fields.filter (·.ty.isImm)

def OpDecl.field? (d : OpDecl) (name : String) : Option Field := d.fields.find? (·.name == name)

/-- The items before the first region, and the regions. -/
def OpDecl.head (d : OpDecl) : List Item :=
  d.items.takeWhile fun | .region _ | .blocks => false | _ => true
def OpDecl.regions (d : OpDecl) : List (Option String) :=
  d.items.filterMap fun | .region kw => some kw | _ => none
/-- Whether the op's regions are labeled blocks (`cf.blocks`). `blocks` is always the last
item. -/
def OpDecl.hasBlocks (d : OpDecl) : Bool := d.items.getLast? == some .blocks

namespace OpDSL

open Lean

set_option hygiene false

declare_syntax_cat firArg
syntax ident : firArg
syntax str : firArg
syntax num : firArg
syntax "[" firArg,* "]" : firArg

declare_syntax_cat firCheck
syntax withPosition(ident (colGt firArg)*) : firCheck

declare_syntax_cat firBinder
syntax "(" ident+ " : " ident ")" : firBinder

declare_syntax_cat firSet
syntax ident " := " term:max : firSet

declare_syntax_cat firClause (behavior := both)
syntax &"name" str ("with" firSet,+)? : firClause
syntax &"format" str : firClause
syntax &"terminator" : firClause
syntax &"rust" ident : firClause
syntax withPosition(&"effects" (colGt ident)*) : firClause
syntax &"rule" many1Indent(firCheck) : firClause

declare_syntax_cat firOp (behavior := both)
syntax (docComment)? &"op" ident firBinder* many1Indent(firClause) : firOp

/-- Declare the ops; see the module documentation. -/
syntax (name := firOps) "fir_ops" many1Indent(firOp) : command

/-- A `name` line: the template's literal parts and slots, and the fixed fields. -/
structure NameLine where
  /-- Literal text, then each slot followed by the literal text after it. -/
  parts : List String
  /-- Each slot's fields and vocabulary (none: the field type's `Spelled` instance). -/
  slots : List (List String × Option String)
  fixed : List (String × Term)

structure Decl where
  doc : Option (TSyntax `Lean.Parser.Command.docComment)
  ctor : Ident
  binders : Array (Array Ident × Ident)
  fields : List Field
  names : List NameLine
  format : String
  terminator : Bool
  rust : Option String
  effects : List String
  rule : Option (Array (TSyntax `firCheck))

def fieldTy : String → FieldTy
  | "Int" => .int
  | "Nat" => .nat
  | "Align" => .align
  | "Symbol" => .symbol
  | "Func" => .func
  | "Ty" => .ty
  | "Flag" => .flag
  | "Succ" => .succ
  | "Cases" => .cases
  | t => .mod t

/-- The Lean type of a field type. -/
def leanTy : String → Name
  | "Align" => `Nat
  | "Symbol" | "Func" => `String
  | "Flag" => `Bool
  | t => .mkSimple t

/-- `"int.{op}.{ovf}"` → `["int.", ".", ""]` and the slots. -/
def parseTemplate (s : String) : Except String (List String × List (List String × Option String)) := do
  let pieces := s.splitOn "{"
  let first := pieces.head!
  let mut parts := [first]
  let mut slots := []
  for piece in pieces.tail do
    let [slot, lit] := piece.splitOn "}" | throw s!"bad name template '{s}'"
    let (fs, vocab) := match slot.splitOn ":" with
      | [fs, v] => (fs, some v.trimAscii.toString)
      | _ => (slot, none)
    let fs := (fs.splitOn " ").filter (!·.isEmpty)
    slots := slots ++ [(fs, vocab)]
    parts := parts ++ [lit]
  pure (parts, slots)

def parseDecl (stx : TSyntax `firOp) : MacroM Decl := do
  let `(firOp| $[$doc?]? op $ctor:ident $bs:firBinder* $cs:firClause*) := stx
    | Macro.throwErrorAt stx "bad op declaration"
  let mut binders := #[]
  let mut fields := []
  for b in bs do
    let `(firBinder| ($ids:ident* : $t:ident)) := b | Macro.throwErrorAt b "bad field"
    binders := binders.push (ids, t)
    for id in ids do
      fields := fields ++ [{ name := id.getId.toString, ty := fieldTy t.getId.toString }]
  let mut d : Decl :=
    { doc := doc?, ctor, binders, fields, names := [], format := "", terminator := false,
      rust := none, effects := [], rule := none }
  for c in cs do
    match c with
    | `(firClause| name $s:str $[with $sets,*]?) =>
      let (parts, slots) ← match parseTemplate s.getString with
        | .ok r => pure r
        | .error e => Macro.throwErrorAt s e
      let mut fixed := []
      for set in (sets.map (·.getElems)).getD #[] do
        let `(firSet| $f:ident := $t) := set | Macro.throwErrorAt set "bad field setting"
        fixed := fixed ++ [(f.getId.toString, t)]
      d := { d with names := d.names ++ [{ parts, slots, fixed }] }
    | `(firClause| format $s:str) => d := { d with format := s.getString }
    | `(firClause| terminator) => d := { d with terminator := true }
    | `(firClause| rust $r:ident) => d := { d with rust := some r.getId.toString }
    | `(firClause| effects $es:ident*) =>
      d := { d with effects := es.toList.map (·.getId.toString) }
    | `(firClause| rule $checks:firCheck*) => d := { d with rule := some checks }
    | _ => Macro.throwErrorAt c "bad clause"
  pure d

/-- The term for a type in a rule. -/
def tyE (stx : TSyntax `firArg) : MacroM Term := do
  let `(firArg| $id:ident) := stx | Macro.throwErrorAt stx "expected a type"
  match id.getId.toString with
  | "ptr" => `(TyE.ptr)
  | "addr" => `(TyE.addr)
  | s =>
    match s.toList with
    | 'i' :: ds =>
      match (String.ofList ds).toNat? with
      | some w => `(TyE.int $(quote w))
      | none => `(TyE.name $(quote s))
    | _ => `(TyE.name $(quote s))

def tyList (stx : TSyntax `firArg) : MacroM Term := do
  let `(firArg| [$ts,*]) := stx | Macro.throwErrorAt stx "expected a list of types"
  let ts ← ts.getElems.mapM tyE
  `([$ts,*])

def argIdent (stx : TSyntax `firArg) : MacroM String := do
  let `(firArg| $id:ident) := stx | Macro.throwErrorAt stx "expected a name"
  pure id.getId.toString

def argStr (stx : TSyntax `firArg) : MacroM String := do
  let `(firArg| $s:str) := stx | Macro.throwErrorAt stx "expected a string"
  pure s.getString

def isList : TSyntax `firArg → Bool
  | `(firArg| [$_,*]) => true
  | _ => false

def checkTerm (stx : TSyntax `firCheck) : MacroM Term := do
  let `(firCheck| $head:ident $args:firArg*) := stx | Macro.throwErrorAt stx "bad check"
  let args := args.toList
  let idents (xs : List (TSyntax `firArg)) := xs.mapM argIdent
  match head.getId.toString, args with
  | "operands", [l] => `(Check.ins "operands" $(← tyList l))
  | "operands", [label, l] =>
    if isList l then `(Check.ins $(quote (← argStr label)) $(← tyList l))
    else `(Check.takeIns [$(quote (← argIdent label))] $(quote (← argStr l)))
  | "operands", xs@(_ :: _) =>
    `(Check.takeIns $(quote (← idents xs.dropLast)) $(quote (← argStr xs.getLast!)))
  | "results", [l] => `(Check.outs $(← tyList l))
  | "results", xs@(_ :: _) =>
    `(Check.takeOuts $(quote (← idents xs.dropLast)) $(quote (← argStr xs.getLast!)))
  | "noResults", [] => `(Check.noOuts)
  | "same", [label, a, b] => `(Check.same $(quote (← argStr label)) $(← tyList a) $(← tyList b))
  | "ints", ts => `(Check.ints [$(← ts.toArray.mapM tyE),*])
  | "pow2", [f] => `(Check.pow2 $(quote (← argIdent f)))
  | "fits", [f, t] => `(Check.fits $(quote (← argIdent f)) $(← tyE t))
  | "widens", [a, t] => `(Check.widens $(← tyE a) $(← tyE t))
  | "narrows", [a, t] => `(Check.narrows $(← tyE a) $(← tyE t))
  | "loadable", [t, verb] => `(Check.loadable $(← tyE t) $(quote (← argStr verb)))
  | "deny", [l, msg] =>
    let `(firArg| [$ns,*]) := l | Macro.throwErrorAt l "expected a list of names"
    `(Check.deny $(quote (← ns.getElems.toList.mapM argStr)) $(quote (← argStr msg)))
  | "call", [f] => `(Check.call $(quote (← argIdent f)))
  | _, _ => Macro.throwErrorAt stx "unknown check"

partial def flatArg : TSyntax `firArg → List String
  | `(firArg| $id:ident) => [id.getId.toString]
  | `(firArg| [$xs,*]) => xs.getElems.toList.flatMap flatArg
  | _ => []

/-- The names a rule binds or reads, to check them against the fields. -/
def ruleNames (stx : TSyntax `firCheck) : MacroM (List String × List String) := do
  let `(firCheck| $head:ident $args:firArg*) := stx | pure ([], [])
  let all := args.toList.flatMap flatArg
  match head.getId.toString with
  | "operands" | "results" =>
    if args.size ≥ 2 && args.all (fun a => a matches `(firArg| $_:ident) || a matches `(firArg| $_:str))
    then pure (all, []) else pure ([], all)
  | _ => pure ([], all)

def capitalize (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => s

def rustName (d : Decl) : String :=
  d.rust.getD (capitalize ((d.ctor.getId.toString.dropEndWhile (· == '_')).toString))

def fieldTyTerm : FieldTy → MacroM Term
  | .int => `(FieldTy.int)
  | .nat => `(FieldTy.nat)
  | .align => `(FieldTy.align)
  | .symbol => `(FieldTy.symbol)
  | .func => `(FieldTy.func)
  | .ty => `(FieldTy.ty)
  | .flag => `(FieldTy.flag)
  | .succ => `(FieldTy.succ)
  | .cases => `(FieldTy.cases)
  | .mod t => `(FieldTy.mod $(quote t))

/-- The value a field of the name table's kinds holds when the name doesn't set it. -/
def defaultTerm : FieldTy → MacroM Term
  | .int => `((0 : Int))
  | .nat => `((0 : Nat))
  | .align => `((1 : Nat))
  | .symbol | .func => `("")
  | .ty => `(Ty.ptr)
  | .flag => `(false)
  | .succ => `(({ label := "", nargs := 0 } : Succ))
  | .cases => `(([] : Cases))
  | .mod _ => Macro.throwError "a modifier field must be set by the name"

/-- The `Imm` constructor for an immediate field. -/
def immCtor : FieldTy → Name
  | .int => `Imm.int
  | .nat | .align => `Imm.nat
  | .symbol | .func => `Imm.str
  | .ty => `Imm.ty
  | .succ => `Imm.succ
  | .cases => `Imm.cases
  | _ => `Imm.flag

def validate (d : Decl) : MacroM Unit := do
  let ctor := d.ctor.getId.toString
  let items ← match parseFormat d.format with
    | .ok items => pure items
    | .error e => Macro.throwErrorAt d.ctor s!"{ctor}: format: {e}"
  let fieldNamed (n : String) := d.fields.find? (·.name == n)
  -- Every immediate appears in the format once, and nothing else does.
  for f in d.fields do
    let uses := items.filter (· == .imm f.name) |>.length
    if f.ty.isImm && uses != 1 then
      Macro.throwErrorAt d.ctor s!"{ctor}: immediate '{f.name}' must appear once in the format"
    if !f.ty.isImm && uses != 0 then
      Macro.throwErrorAt d.ctor s!"{ctor}: modifier '{f.name}' belongs in the name"
  for i in items do
    if let .imm n := i then
      unless (fieldNamed n).isSome do Macro.throwErrorAt d.ctor s!"{ctor}: no field '{n}'"
  -- Regions come last; `%iter` feeds the first.
  let head := items.takeWhile fun | .region _ | .blocks => false | _ => true
  unless (items.drop head.length).all (· matches .region _ | .blocks) do
    Macro.throwErrorAt d.ctor s!"{ctor}: regions must come last in the format"
  if items.contains .iter && head.length == items.length then
    Macro.throwErrorAt d.ctor s!"{ctor}: %iter needs a region"
  if items.contains .blocks && items.getLast? != some .blocks then
    Macro.throwErrorAt d.ctor s!"{ctor}: blocks must be the last item of the format"
  -- Each modifier is set by every name line.
  if d.names.isEmpty then Macro.throwErrorAt d.ctor s!"{ctor}: no name"
  for n in d.names do
    let set := n.fixed.map (·.1) ++ n.slots.flatMap (·.1)
    for f in d.fields do
      if !f.ty.isImm && !set.contains f.name then
        Macro.throwErrorAt d.ctor s!"{ctor}: a name line leaves '{f.name}' unset"
    for s in set do
      unless (fieldNamed s).isSome do Macro.throwErrorAt d.ctor s!"{ctor}: no field '{s}'"
  -- Rules name bound types or `Ty` fields.
  if let some checks := d.rule then
    let mut bound : List String := []
    for c in checks do
      let (binds, reads) ← ruleNames c
      for r in reads do
        let ok := bound.contains r || ["ptr", "addr", "i1"].contains r ||
          (r.startsWith "i" && ((r.drop 1).toString.toNat?).isSome) ||
          (fieldNamed r).isSome
        unless ok do Macro.throwErrorAt c s!"{ctor}: '{r}' is not bound"
      bound := bound ++ binds

@[macro firOps] def expandFirOps : Macro := fun stx => do
  let mut cmds : Array Syntax := #[]
  let decls ← stx[1].getArgs.mapM fun s => parseDecl ⟨s⟩
  for d in decls do validate d
  -- The inductive. Each constructor's type names its fields: `(size : Nat) → (align : Nat) → OpKind`.
  let docs := decls.map (·.doc)
  let ctors := decls.map (·.ctor)
  let types ← decls.mapM fun d => do
    let mut t ← `(OpKind)
    for (ids, ty) in d.binders.reverse do
      let ty := mkIdent (leanTy ty.getId.toString)
      for id in ids.reverse do t ← `(($(mkIdent id.getId) : $ty) → $t)
    pure t
  cmds := cmds.push (← `(inductive OpKind where
    $[$[$docs:docComment]? | $ctors:ident : $types]*
    deriving DecidableEq, Repr))
  let ctorName (d : Decl) : Ident := mkIdent (`OpKind ++ d.ctor.getId)
  let any (d : Decl) : MacroM Term := `($(ctorName d) ..)
  -- `isTerminator`
  let terms ← (decls.filter (·.terminator)).mapM any
  let pats := terms.push (← `(_))
  let rhss := (terms.map fun _ => (mkIdent `true : Term)).push (mkIdent `false)
  cmds := cmds.push (← `(def OpKind.isTerminator : OpKind → Bool $[| $pats => $rhss]*))
  -- The op table, and each kind's place in it.
  let declTerms ← decls.mapM fun d => do
    let fields ← d.fields.toArray.mapM fun f => do
      `({ name := $(quote f.name), ty := $(← fieldTyTerm f.ty) : Field })
    let rule ← match d.rule with
      | some cs => do `(some [$(← cs.mapM checkTerm),*])
      | none => `(none)
    let effects ← d.effects.toArray.mapM fun e => `($(mkIdent (.str `Effect e)):ident)
    let doc := match d.doc with
      | some doc => doc.getDocString.trimAscii.toString
      | none => ""
    `({ ctor := $(quote d.ctor.getId.toString), rust := $(quote (rustName d)),
        doc := $(quote doc), fields := [$fields,*], format := $(quote d.format),
        terminator := $(quote d.terminator), rule := $rule, effects := [$effects,*],
        tier := .verified : OpDecl })
  cmds := cmds.push (← `(def opDecls : Array OpDecl := #[$declTerms,*]))
  let pats ← decls.mapM any
  let idxs := (Array.range decls.size).map fun i => (quote i : Term)
  cmds := cmds.push (← `(def OpKind.declIdx : OpKind → Nat $[| $pats => $idxs]*))
  cmds := cmds.push (← `(def OpKind.decl (k : OpKind) : OpDecl := opDecls[k.declIdx]!))
  -- Immediates: read, write, and reset to the name table's defaults.
  let pat (d : Decl) (keep : Field → Bool) : MacroM Term := do
    let args ← d.fields.toArray.mapM fun f =>
      if keep f then pure (mkIdent (.mkSimple f.name) : Term) else `(_)
    `($(ctorName d) $args*)
  let mut getPats : Array Term := #[]
  let mut getNames : Array Term := #[]
  let mut getRhss : Array Term := #[]
  let mut setPats : Array Term := #[]
  let mut setNames : Array Term := #[]
  let mut setVals : Array Term := #[]
  let mut setRhss : Array Term := #[]
  let mut erasePats : Array Term := #[]
  let mut eraseRhss : Array Term := #[]
  let mut modRhss : Array Term := #[]
  for d in decls do
    for f in d.fields do
      if f.ty.isImm then
        let v := mkIdent (.mkSimple f.name)
        getPats := getPats.push (← pat d (·.name == f.name))
        getNames := getNames.push (quote f.name)
        getRhss := getRhss.push (← `(some ($(mkIdent (immCtor f.ty)) $v)))
        let args := d.fields.toArray.map fun g =>
          if g.name == f.name then mkIdent `v else mkIdent (.mkSimple g.name)
        setPats := setPats.push (← pat d (·.name != f.name))
        setNames := setNames.push (quote f.name)
        setVals := setVals.push (← `($(mkIdent (immCtor f.ty)) v))
        setRhss := setRhss.push (← `($(ctorName d) $args*))
    erasePats := erasePats.push (← pat d (!·.ty.isImm))
    let args ← d.fields.toArray.mapM fun f =>
      if f.ty.isImm then defaultTerm f.ty else pure (mkIdent (.mkSimple f.name))
    eraseRhss := eraseRhss.push (← `($(ctorName d) $args*))
    let reprs ← (d.fields.filter (!·.ty.isImm)).toArray.mapM fun f =>
      `(reprStr $(mkIdent (.mkSimple f.name)))
    modRhss := modRhss.push (← `([$reprs,*]))
  cmds := cmds.push (← `(
    /-- The immediate field with this name. -/
    def OpKind.imm : OpKind → String → Option Imm
      $[| $getPats, $getNames => $getRhss]*
      | _, _ => none))
  cmds := cmds.push (← `(
    /-- Set an immediate field; a wrong name or kind of value changes nothing. -/
    def OpKind.setImm : OpKind → String → Imm → OpKind
      $[| $setPats, $setNames, $setVals => $setRhss]*
      | k, _, _ => k))
  cmds := cmds.push (← `(
    /-- The kind with its immediates reset, as the name table holds it. -/
    def OpKind.erase : OpKind → OpKind $[| $erasePats => $eraseRhss]*))
  cmds := cmds.push (← `(
    /-- Each modifier field's `repr`, for the Rust generator. -/
    def OpKind.modReprs : OpKind → List String $[| $erasePats => $modRhss]*))
  -- The name table.
  let mut nameTerms := #[]
  for d in decls do
    for n in d.names do
      let slotVars := (List.range n.slots.length).map fun i => mkIdent (.mkSimple s!"s{i}")
      let fieldArg (f : Field) : MacroM Term := do
        if let some (_, t) := n.fixed.find? (·.1 == f.name) then return t
        for (fs, _) in n.slots, v in slotVars do
          if let some j := fs.idxOf? f.name then
            let mut t ← `($(v).value)
            for _ in [0:j] do t ← `(Prod.snd $t)
            if j + 1 < fs.length then t ← `(Prod.fst $t)
            return t
        defaultTerm f.ty
      let args ← d.fields.toArray.mapM fieldArg
      let mut text ← `($(quote n.parts.head!))
      for v in slotVars, lit in n.parts.tail do
        text ← `($text ++ $(v).text ++ $(quote lit))
      let mut parses ← `(true)
      for v in slotVars do parses ← `($parses && $(v).parses)
      let mut t ← `([({ text := $text, value := $(ctorName d) $args*, parses := $parses } : Spelling OpKind)])
      for (fs, vocab) in n.slots.reverse, v in slotVars.reverse do
        let vocabTerm ← match vocab, fs with
          | some name, _ => pure (mkIdent (.mkSimple name) : Term)
          | none, [f] =>
            let some field := d.fields.find? (·.name == f) | Macro.throwError s!"no field {f}"
            let .mod ty := field.ty | Macro.throwError s!"{f} is not a modifier"
            `((Spelled.spellings : List (Spelling $(mkIdent (leanTy ty)))))
          | none, _ => Macro.throwError "a slot with several fields needs a vocabulary"
        t ← `(List.flatMap (fun $v => $t) $vocabTerm)
      nameTerms := nameTerms.push t
  cmds := cmds.push (← `(
    /-- Every op name with the kind it spells (immediates reset). -/
    def opNames : List (Spelling OpKind) := List.flatten [$nameTerms,*]))
  pure (mkNullNode cmds)

end OpDSL

end Fir
