import Fir.Basic
import Fir.Syntax
import Fir.Interp

/-!
# Printer

Prints modules in canonical text, which the parser reads back unchanged. Each op prints in its
declared readable form, or in the generic form (see `Fir.Parse`) when its operands or regions
don't fit that form; only modules that fail to verify have such ops.
-/

namespace Fir

def Trust.name : Trust → String
  | .assume => "assume"
  | .check => "check"
  | .proved => "proved"

def TrustedFact.render : TrustedFact → String
  | ⟨f, t⟩ =>
    let body := match f with
      | .rangeS lo hi => s!"range.s({lo}, {hi})"
      | .rangeU lo hi => s!"range.u({lo}, {hi})"
      | .nonnull => "nonnull"
      | .align n => s!"align({n})"
      | .noalias => "noalias"
      | .readonly => "readonly"
    s!"{body} {t.name}"

def Result.render (r : Result) : String :=
  let facts := if r.facts.isEmpty then "" else
    s!" [{", ".intercalate (r.facts.map TrustedFact.render)}]"
  s!"%{r.name}: {r.ty}{facts}"

def Operand.render : Operand → String
  | .var n => s!"%{n}"
  | .hole n t => s!"?{n}: {t}"

def renderOpLoc (showLocs : Bool) : Option Loc → String
  | some l => if showLocs then s!" @{l.line}:{l.col}" else ""
  | none => ""

def commas (xs : List String) : String := ", ".intercalate xs

/-- A branch target in the generic form: `^b`, or `^b(n)` for `n` arguments. -/
def Succ.renderGeneric (s : Succ) : String :=
  "^" ++ s.label ++ (if s.nargs == 0 then "" else s!"({s.nargs})")

/-- An immediate's value as text. Branch targets are in the generic form; the readable form
writes them with their operands. -/
def Imm.render (f : Field) : Imm → String
  | .int n => toString n
  | .nat n => toString n
  | .str s => if f.ty == .func then "@" ++ s else s
  | .ty t => toString t
  | .flag b => toString b
  | .succ s => s.renderGeneric
  | .cases cs => "[" ++ commas (cs.map fun (k, s) => s!"{k}: {s.renderGeneric}") ++ "]"

/-- How many of an op's operands are its branch targets' arguments. -/
def OpKind.succArgs (k : OpKind) : Nat :=
  k.decl.imms.foldl (init := 0) fun n f =>
    match k.imm f.name with
    | some (.succ s) => n + s.nargs
    | some (.cases cs) => n + (cs.map (·.2.nargs)).sum
    | _ => n

/-- Whether the readable form can show an op with these operands and regions: as many operands
as the format holds (with its branch targets' arguments), and the regions it lists, with
parameters only where `%iter` gives them; or, for `cf.blocks`, regions that all have labels. -/
def OpDecl.fits (d : OpDecl) (k : OpKind) (args : List Operand) (regions : List Region) : Bool :=
  let iter := d.items.contains .iter
  (if d.hasBlocks then regions.all (·.label.isSome)
   else regions.length == d.regions.length && regions.all (·.label.isNone) &&
    regions.zipIdx.all fun (r, i) => r.params.isEmpty || (iter && i == 0)) &&
  (if d.items.contains .variadic || d.items.contains .args then true
   else if iter then some args.length == regions.head?.map (·.params.length)
   else args.length == (d.items.filter (· == .operand)).length + k.succArgs)

mutual
  partial def renderRegion (showLocs : Bool) (indent : String) (r : Region) : String :=
    let body := r.ops.map (renderOp showLocs (indent ++ "  "))
    "{\n" ++ String.join body ++ indent ++ "}"

  /-- `cf.blocks`'s blocks, each label at the op's indentation and its ops one level in. -/
  partial def renderBlocks (showLocs : Bool) (indent : String) (rs : List Region) : String :=
    let block (r : Region) :=
      let params := if r.params.isEmpty then "" else
        "(" ++ commas (r.params.map Result.render) ++ ")"
      indent ++ "^" ++ r.label.getD "" ++ params ++ ":\n" ++
        String.join (r.ops.map (renderOp showLocs (indent ++ "  ")))
    "{\n" ++ String.join (rs.map block) ++ indent ++ "}"

  /-- The readable form, from the op's declared format. -/
  partial def renderReadable (showLocs : Bool) (indent : String) (op : Op) : String := Id.run do
    let d := op.kind.decl
    let mut out := op.kind.name
    let mut args := op.args
    -- A branch target with its arguments, taken from the operands.
    let target (s : Succ) (args : List Operand) : String × List Operand :=
      let mine := args.take s.nargs
      let text := if mine.isEmpty then "" else "(" ++ commas (mine.map Operand.render) ++ ")"
      ("^" ++ s.label ++ text, args.drop s.nargs)
    for item in d.head do
      match item with
      | .imm f =>
        match (d.field? f).getD default, op.kind.imm f with
        | { ty := .flag, .. }, some (.flag b) => if b then out := out ++ " " ++ f
        | _, some (.succ s) =>
          let (text, rest) := target s args
          out := out ++ " " ++ text
          args := rest
        | _, some (.cases cs) =>
          let mut items := #[]
          for (k, s) in cs do
            let (text, rest) := target s args
            items := items.push s!"{k}: {text}"
            args := rest
          out := out ++ " [" ++ commas items.toList ++ "]"
        | field, some v => out := out ++ " " ++ v.render field
        | _, none => pure ()
      | .operand =>
        if let a :: rest := args then
          out := out ++ " " ++ a.render
          args := rest
      | .comma => out := out ++ ","
      | .keyword kw => out := out ++ " " ++ kw
      | .variadic =>
        unless args.isEmpty do out := out ++ " " ++ commas (args.map Operand.render)
        args := []
      | .args =>
        out := out ++ "(" ++ commas (args.map Operand.render) ++ ")"
        args := []
      | .iter =>
        let params := (op.regions.head?.map (·.params)).getD []
        unless params.isEmpty do
          let items := (params.zip args).map fun (r, a) => s!"{r.render} = {a.render}"
          out := out ++ " iter(" ++ commas items ++ ")"
        args := []
      | .region _ | .blocks => pure ()
    out := out ++ renderOpLoc showLocs op.loc
    for kw in d.regions, r in op.regions do
      match kw with
      | none => out := out ++ " " ++ renderRegion showLocs indent r
      | some kw =>
        unless r.ops.isEmpty do out := out ++ " " ++ kw ++ " " ++ renderRegion showLocs indent r
    if d.hasBlocks then out := out ++ " " ++ renderBlocks showLocs indent op.regions
    pure out

  /-- The generic form: `"name"(operands) {attrs} @loc (regions)`. -/
  partial def renderGeneric (showLocs : Bool) (indent : String) (op : Op) : String :=
    let d := op.kind.decl
    let attrs := if d.imms.isEmpty then "" else
      let items := d.imms.map fun f =>
        f.name ++ " = " ++ (((op.kind.imm f.name).map (·.render f)).getD "")
      " {" ++ commas items ++ "}"
    let region (r : Region) :=
      let label := match r.label with
        | some l => "^" ++ l
        | none => ""
      let params := if r.params.isEmpty then "" else
        "(" ++ commas (r.params.map Result.render) ++ ")"
      let head := label ++ params
      (if head.isEmpty then "" else head ++ " ") ++ renderRegion showLocs indent r
    let regions := if op.regions.isEmpty then "" else
      " (" ++ commas (op.regions.map region) ++ ")"
    "\"" ++ op.kind.name ++ "\"(" ++ commas (op.args.map Operand.render) ++ ")" ++ attrs ++
      renderOpLoc showLocs op.loc ++ regions

  partial def renderOp (showLocs : Bool) (indent : String) (op : Op) : String :=
    let results := if op.results.isEmpty then "" else
      commas (op.results.map Result.render) ++ " = "
    let line := if op.kind.decl.fits op.kind op.args op.regions
      then renderReadable showLocs indent op
      else renderGeneric showLocs indent op
    indent ++ results ++ line ++ "\n"
end

def Func.render (showLocs : Bool) (f : Func) : String :=
  let params := commas (f.params.map Result.render)
  let rets := match f.rets with
    | [] => ""
    | [t] => s!" -> {t}"
    | ts => s!" -> ({commas (ts.map toString)})"
  let file := match f.file with
    | some s => if showLocs then s!" loc \"{s}\"" else ""
    | none => ""
  s!"func @{f.name}({params}){rets}{file} " ++ renderRegion showLocs "" f.body ++ "\n"

def Module.render (m : Module) (showLocs := true) : String :=
  let header := if m.space == {} then "" else
    s!"memspace default ptr {m.space.ptrBits} addr {m.space.addrBits}\n\n"
  header ++ "\n".intercalate (m.funcs.map (Func.render showLocs))

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def Ptr.render : Ptr → String
  | .rel a _ off => if off == 0 then s!"#{a}" else if off > 0 then s!"#{a}+{off}" else s!"#{a}{off}"
  | .abs 0 [] => "null"
  | .abs addr _ => hex addr

def Byte.render : Byte → String
  | .bits b => hex b.toNat
  | .poison => "poison"
  | .frag p i => s!"{p.render}[{i}]"

/-- Integers print signed, except `i1`, which prints as `0` or `1`. Pointers print as their
allocation and offset (`#2+8`), or as an address. -/
def RVal.render : RVal → String
  | .int w .poison => s!"i{w} poison"
  | .int w (.bits b) => if w = 1 then s!"i1 {b.toNat}" else s!"i{w} {b.toInt}"
  | .ptr none => "ptr poison"
  | .ptr (some p) => s!"ptr {p.render}"
  | .bytes bs => s!"b{bs.length * 8} ({commas (bs.map Byte.render)})"

def renderHaltLoc : Option Loc → String
  | some l => s!" @{l.line}:{l.col}"
  | none => ""

/-- One line describing how a run ended. Tests compare against this text. -/
def renderHalt (h : Halt) : String :=
  let l := renderHaltLoc h.loc
  let main := match h.behavior with
    | .ret [] => "returned"
    | .ret vs => s!"returned {commas (vs.map RVal.render)}"
    | .trap r => s!"trap {r.name}{l}"
    | .ub k => s!"ub {k.name}{l}"
    | .hole n => s!"hole ?{n}{l}"
    | .stuck msg => s!"stuck{l}: {msg}"
    | .diverge => "diverges"
    | .ambiguous => s!"ambiguous{l}"
  let note := if h.note.isEmpty then "" else s!" ({h.note})"
  "; ".intercalate ((main ++ note) :: h.leaks)

end Fir
