import Fir.Syntax

/-!
# `gen-rust`: the Rust op definitions

```
lake exe gen-rust > ../crates/fir/src/generated/ops.rs
```

Prints the Rust counterpart of the op declarations in `Fir.Syntax`: the `OpKind` enum, its names
(`op_kind`, `OpKind::mnemonic`), its declarations (`OpKind::decl`, read through
`crates/fir/src/decl.rs`), and access to its immediates. The Rust tests check that the file is
up to date.
-/

namespace Fir.GenRust

open Fir

/-- A Rust string literal. -/
def rustStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | c => c.toString) ++ "\""

def capitalize (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => s

/-- A modifier value's `repr` (`Fir.Ovf.trap true`) as Rust (`Ovf::Trap(true)`). The modifier
enums are mirrored in `crates/fir/src/ir.rs` with capitalized variant names. -/
def rustOfRepr (r : String) : String :=
  let r := if r.startsWith "Fir." then (r.drop 4).toString else r
  match r.splitOn " " with
  | [head] => path head
  | head :: args => s!"{path head}({", ".intercalate args})"
  | [] => r
where
  path (head : String) : String :=
    match head.splitOn "." with
    | [ty, ctor] => s!"{ty}::{capitalize ctor}"
    | _ => head

def _root_.Fir.FieldTy.rust : FieldTy → String
  | .int => "IntId"
  | .nat => "u64"
  | .align => "u32"
  | .symbol | .func => "StrId"
  | .ty => "Ty"
  | .succ => "SuccId"
  | .cases => "CasesId"
  | .flag | .mod "Bool" => "bool"
  | .mod t => t

/-- What the name table's kinds hold in an immediate. -/
def _root_.Fir.FieldTy.placeholder : FieldTy → String
  | .int => "IntId::PLACEHOLDER"
  | .nat => "0"
  | .align => "1"
  | .symbol | .func => "StrId::PLACEHOLDER"
  | .ty => "Ty::Ptr"
  | .succ => "SuccId::PLACEHOLDER"
  | .cases => "CasesId::EMPTY"
  | _ => "false"

def _root_.Fir.FieldTy.immVariant : FieldTy → String
  | .int => "Int"
  | .nat => "Nat"
  | .align => "Align"
  | .symbol | .func => "Str"
  | .ty => "Ty"
  | .succ => "Succ"
  | .cases => "Cases"
  | _ => "Flag"

def _root_.Fir.FieldTy.rustDecl : FieldTy → String
  | .int => "Int"
  | .nat => "Nat"
  | .align => "Align"
  | .symbol => "Symbol"
  | .func => "Func"
  | .ty => "Ty"
  | .succ => "Succ"
  | .cases => "Cases"
  | _ => "Flag"

/-- A variant names its fields when one is a `bool`, a number, a string, or a branch target. -/
def _root_.Fir.OpDecl.isStruct (d : OpDecl) : Bool :=
  d.fields.any fun f => match f.ty with
    | .nat | .align | .symbol | .func | .flag | .mod "Bool" | .succ | .cases => true
    | _ => false

/-- `Variant(a, b)` or `Variant { x: a, y: b }` from each field's text; `rest` ends a struct
pattern (`..`) when some fields are left out. -/
def _root_.Fir.OpDecl.rustApply (d : OpDecl) (vals : List (Field × Option String)) : String :=
  let shown := vals.filterMap fun (f, v) => v.map (f, ·)
  if d.fields.isEmpty then s!"OpKind::{d.rust}"
  else if d.isStruct then
    let items := shown.map fun (f, v) => if v == f.name then f.name else s!"{f.name}: {v}"
    let items := if shown.length < d.fields.length then items ++ [".."] else items
    s!"OpKind::{d.rust} \{ {", ".intercalate items} }"
  else
    s!"OpKind::{d.rust}({", ".intercalate (vals.map fun (_, v) => v.getD "_")})"

/-- The kind's Rust text: modifiers as values, immediates as placeholders (an expression) or
left out (a pattern). -/
def rustKind (k : OpKind) (pattern : Bool) : String :=
  let d := k.decl
  let mods := k.modReprs
  let (vals, _) := d.fields.foldl (init := ([], mods)) fun (acc, mods) f =>
    if f.ty.isImm then (acc ++ [(f, if pattern then none else some f.ty.placeholder)], mods)
    else match mods with
      | m :: rest => (acc ++ [(f, some (rustOfRepr m))], rest)
      | [] => (acc ++ [(f, none)], [])
  d.rustApply vals

def docLines (indent doc : String) : List String :=
  if doc.isEmpty then [] else
  (doc.splitOn "\n").map fun l =>
    let l := l.trimAscii.toString
    if l.isEmpty then s!"{indent}///" else s!"{indent}/// {l}"

def immIndex (d : OpDecl) (name : String) : Nat := (d.imms.map (·.name)).idxOf name

def rustItem (d : OpDecl) : Item → String
  | .imm f => s!"Item::Imm({immIndex d f})"
  | .operand => "Item::Operand"
  | .comma => "Item::Comma"
  | .keyword kw => s!"Item::Keyword({rustStr kw})"
  | .variadic => "Item::Variadic"
  | .args => "Item::Args"
  | .iter => "Item::Iter"
  | .region none => "Item::Region(None)"
  | .region (some kw) => s!"Item::Region(Some({rustStr kw}))"
  | .blocks => "Item::Blocks"

def rustTyE (d : OpDecl) (env : List String) : TyE → String
  | .ptr => "TyE::Ptr"
  | .addr => "TyE::Addr"
  | .int w => s!"TyE::Int({w})"
  | .name n => match env.idxOf? n with
    | some i => s!"TyE::Var({i})"
    | none => s!"TyE::Field({immIndex d n})"

def rustTys (d : OpDecl) (env : List String) (ts : List TyE) : String :=
  s!"&[{", ".intercalate (ts.map (rustTyE d env))}]"

/-- A rule's checks, with names turned into variable and field indices. -/
def rustRule (d : OpDecl) (checks : List Check) : Except String (List String) := do
  let mut env : List String := []
  let mut out := []
  for c in checks do
    let t := rustTyE d env
    let ts := rustTys d env
    let s ← match c with
      | .takeIns vs msg => do env := env ++ vs; pure s!"Check::TakeIns({vs.length}, {rustStr msg})"
      | .takeOuts vs msg => do env := env ++ vs; pure s!"Check::TakeOuts({vs.length}, {rustStr msg})"
      | .ins label want => pure s!"Check::Ins({rustStr label}, {ts want})"
      | .outs want => pure s!"Check::Outs({ts want})"
      | .noOuts => pure "Check::NoOuts"
      | .same label got want => pure s!"Check::Same({rustStr label}, {ts got}, {ts want})"
      | .ints xs => pure s!"Check::Ints({ts xs})"
      | .pow2 f => pure s!"Check::Pow2({immIndex d f})"
      | .fits f x => pure s!"Check::Fits({immIndex d f}, {t x})"
      | .widens a x => pure s!"Check::Widens({t a}, {t x})"
      | .narrows a x => pure s!"Check::Narrows({t a}, {t x})"
      | .loadable x verb => pure s!"Check::Loadable({t x}, {rustStr verb})"
      | .deny names msg =>
        pure s!"Check::Deny(&[{", ".intercalate (names.map rustStr)}], {rustStr msg})"
      | .call f => pure s!"Check::Call({immIndex d f})"
    out := out ++ [s]
  if env.length > 4 then throw s!"{d.ctor}: a rule names at most 4 types"
  pure out

def rustDecl (d : OpDecl) : Except String String := do
  let imms := d.imms.map fun f =>
    s!"Field \{ name: {rustStr f.name}, ty: FieldTy::{f.ty.rustDecl} }"
  let items := d.items.map (rustItem d)
  let rule ← match d.rule with
    | none => pure "None"
    | some cs => do
      let cs ← rustRule d cs
      pure ("Some(&[\n" ++ String.join (cs.map (s!"            {·},\n")) ++ "        ])")
  let effects := d.effects.map fun e => s!"Effect::{capitalize (reprStr e |>.drop 11 |>.toString)}"
  let tier := s!"Tier::{capitalize (reprStr d.tier |>.drop 9 |>.toString)}"
  pure <| String.intercalate "\n" [
    "    OpDecl {",
    s!"        ctor: {rustStr d.ctor},",
    s!"        imms: &[{", ".intercalate imms}],",
    s!"        items: &[{", ".intercalate items}],",
    s!"        terminator: {d.terminator},",
    s!"        rule: {rule},",
    s!"        effects: &[{", ".intercalate effects}],",
    s!"        tier: {tier},",
    "    },"]

def generate : Except String String := do
  let decls := opDecls.toList
  let mut out : Array String := #[]
  let emit (xs : Array String) (s : String) := xs.push s
  out := emit out "// Generated by `lake exe gen-rust` (spec/GenRust.lean) from the op declarations in
// spec/Fir/Syntax.lean. Do not edit: change the declarations and regenerate with
// `cd spec && lake exe gen-rust > ../crates/fir/src/generated/ops.rs`.

use crate::body::{CasesId, IntId, StrId, SuccId};
use crate::decl::{Check, Effect, Field, FieldTy, Imm, Item, OpDecl, Tier, TyE};
use crate::ir::*;

/// What an op does. Mirrors `Fir.OpKind`. Alignments are 32-bit (Lean's are unbounded).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum OpKind {"
  for d in decls do
    for l in docLines "    " d.doc do out := emit out l
    let variant := if d.fields.isEmpty then d.rust
      else if d.isStruct then
        s!"{d.rust} \{ {", ".intercalate (d.fields.map fun f => s!"{f.name}: {f.ty.rust}")} }"
      else s!"{d.rust}({", ".intercalate (d.fields.map (·.ty.rust))})"
    out := emit out s!"    {variant},"
  out := emit out "}\n"
  -- Names and declarations.
  out := emit out "impl OpKind {"
  let terms := decls.filter (·.terminator) |>.map fun d => d.rustApply (d.fields.map (·, none))
  out := emit out s!"    pub fn is_terminator(&self) -> bool \{
        matches!(self, {" | ".intercalate terms})
    }
"
  out := emit out "    /// The op's name with its modifiers, as printed.
    pub fn mnemonic(&self) -> &'static str {
        match self {"
  let mut seen : List OpKind := []
  for s in opNames do
    if seen.contains s.value then continue
    seen := s.value :: seen
    out := emit out s!"            {rustKind s.value true} => {rustStr s.text},"
  out := emit out "        }
    }
"
  out := emit out "    /// The op's declaration.
    pub fn decl(&self) -> &'static OpDecl {
        match self {"
  for d in decls, i in [0:decls.length] do
    let pat := d.rustApply (d.fields.map (·, none))
    out := emit out s!"            {pat} => &DECLS[{i}],"
  out := emit out "        }
    }
"
  out := emit out "    /// The immediate with this index in the declaration's `imms`.
    pub fn imm(&self, i: usize) -> Option<Imm> {
        Some(match (self, i) {"
  for d in decls do
    for f in d.imms, j in [0:d.imms.length] do
      let pat := d.rustApply (d.fields.map fun g => (g, if g.name == f.name then some "x" else none))
      out := emit out s!"            ({pat}, {j}) => Imm::{f.ty.immVariant}(*x),"
  out := emit out "            _ => return None,
        })
    }
"
  out := emit out "    /// Set the immediate with this index; a wrong index or kind of value changes nothing.
    pub fn set_imm(&mut self, i: usize, v: Imm) {
        match (self, i, v) {"
  for d in decls do
    for f in d.imms, j in [0:d.imms.length] do
      let pat := d.rustApply (d.fields.map fun g => (g, if g.name == f.name then some "x" else none))
      out := emit out s!"            ({pat}, {j}, Imm::{f.ty.immVariant}(v)) => *x = v,"
  out := emit out "            _ => {}
        }
    }
}
"
  out := emit out "/// Decode an op name with its modifiers. Immediates get placeholders (such as `align 1`, or
/// string and integer ids that point nowhere) that the parser fills.
pub fn op_kind(name: &str) -> Option<OpKind> {
    Some(match name {"
  for s in opNames do
    if s.parses then out := emit out s!"        {rustStr s.text} => {rustKind s.value false},"
  out := emit out "        _ => return None,
    })
}
"
  out := emit out s!"static DECLS: [OpDecl; {decls.length}] = ["
  for d in decls do out := emit out (← rustDecl d)
  out := emit out "];"
  pure ("\n".intercalate out.toList ++ "\n")

end Fir.GenRust

def main : IO UInt32 := do
  match Fir.GenRust.generate with
  | .ok s => IO.print s; pure 0
  | .error e => IO.eprintln e; pure 1
