import Fir.Syntax
import Fir.DceKinds

/-!
# `gen-rust`: the Rust op definitions

```
lake exe gen-rust > ../crates/fir/src/generated/ops.rs
lake exe gen-rust contracts > ../crates/fir/src/generated/contracts.rs
lake exe gen-rust manifest > ../docs/assurance/op-contracts.json
```

Prints the Rust counterpart of the op declarations in `Fir.Syntax`: the `OpKind` enum, its names
(`op_kind`, `OpKind::mnemonic`), its declarations (`OpKind::decl`, read through
`crates/fir/src/decl.rs`), and access to its immediates. The Rust tests check that the file is
up to date.

`contracts` prints the op contracts (`crates/fir/src/contract.rs` reads them): for each kind an
op name spells, what the Lean proofs let optimizations do with it, with the theorem that says so
(`Fir.Dce.dcePerm`, `Fir.Dce.dcePerm_sound`). `manifest` prints the same with the declarations,
as JSON, for tools and reviewers. Both fail on a contradiction between a permission and a
declaration (a kind that may be deleted but is declared to write, allocate, free, call, or end a
block).
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
  | .nat | .float => "u64"
  | .align | .index => "u32"
  | .symbol | .func | .global => "StrId"
  | .ty => "Ty"
  | .succ => "SuccId"
  | .cases => "CasesId"
  | .reg => "Reg"
  | .flag | .mod "Bool" => "bool"
  | .mod t => t

/-- What the name table's kinds hold in an immediate. -/
def _root_.Fir.FieldTy.placeholder : FieldTy → String
  | .int => "IntId::PLACEHOLDER"
  | .nat | .index | .float => "0"
  | .align => "1"
  | .symbol | .func | .global => "StrId::PLACEHOLDER"
  | .ty => "Ty::Ptr"
  | .succ => "SuccId::PLACEHOLDER"
  | .cases => "CasesId::EMPTY"
  | .reg => "Reg::XZR"
  | _ => "false"

def _root_.Fir.FieldTy.immVariant : FieldTy → String
  | .int => "Int"
  | .nat | .float => "Nat"
  | .align => "Align"
  | .index => "Index"
  | .symbol | .func | .global => "Str"
  | .ty => "Ty"
  | .succ => "Succ"
  | .cases => "Cases"
  | .reg => "Reg"
  | _ => "Flag"

def _root_.Fir.FieldTy.rustDecl : FieldTy → String
  | .int => "Int"
  | .nat => "Nat"
  | .align => "Align"
  | .index => "Index"
  | .symbol => "Symbol"
  | .func => "Func"
  | .global => "Global"
  | .ty => "Ty"
  | .succ => "Succ"
  | .cases => "Cases"
  | .reg => "Reg"
  | .float => "Float"
  | _ => "Flag"

/-- A variant names its fields when one is a `bool`, a number, a string, a branch target, or a
register. -/
def _root_.Fir.OpDecl.isStruct (d : OpDecl) : Bool :=
  d.fields.any fun f => match f.ty with
    | .nat | .align | .index | .symbol | .func | .global | .flag | .mod "Bool" | .succ | .cases
    | .reg | .float => true
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
  | .slice => "TyE::Slice"
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
      | .sized x => pure s!"Check::Sized({t x})"
      | .field x i => pure s!"Check::Field({t x}, {immIndex d i})"
      | .sig f => pure s!"Check::Sig({immIndex d f})"
      | .global f => pure s!"Check::Global({immIndex d f})"
      | .func f => pure s!"Check::Func({immIndex d f})"
      | .parts x => pure s!"Check::Parts({t x})"
      | .part a i x => pure s!"Check::Part({t a}, {immIndex d i}, {t x})"
      | .variant u i x => pure s!"Check::Variant({t u}, {immIndex d i}, {t x})"
      | .isUnion u => pure s!"Check::Union({t u})"
      | .scalar x => pure s!"Check::Scalar({t x})"
      | .floats xs => pure s!"Check::Floats({ts xs})"
      | .numeric xs => pure s!"Check::Numeric({ts xs})"
      | .sameWidth a x => pure s!"Check::SameWidth({t a}, {t x})"
      | .floatBits f x => pure s!"Check::FloatBits({immIndex d f}, {t x})"
      | .vararg x => pure s!"Check::Vararg({t x})"
    out := out ++ [s]
  if env.length > 4 then throw s!"{d.ctor}: a rule names at most 4 types"
  pure out

/-! Layers and dialects (decisions: Layers, Dialects). -/

/-- The `layers` and `dialect` fields of a declaration. A target's ops are never in HFIR. -/
def rustLayerFields (d : OpDecl) : Except String (List String) := do
  if targets.contains d.dialect && d.layers.contains .hfir then
    throw s!"{d.ctor}: an op of the target {d.dialect} can't be in HFIR"
  let has (k : LayerKind) := toString (d.layers.contains k)
  pure [s!"        layers: crate::decl::Layers \{ hfir: {has .hfir}, mfir: {has .mfir}, lfir: {has .lfir} },",
    s!"        dialect: {rustStr d.dialect},"]

/-- The LFIR targets. -/
def rustTargets : String :=
  s!"/// The LFIR target dialects (Lean's `Fir.targets`).
pub static TARGETS: [&str; {targets.length}] = [{", ".intercalate (targets.map rustStr)}];
"

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
  let layers ← rustLayerFields d
  pure <| String.intercalate "\n" <| [
    "    OpDecl {",
    s!"        ctor: {rustStr d.ctor},",
    s!"        imms: &[{", ".intercalate imms}],",
    s!"        items: &[{", ".intercalate items}],",
    s!"        terminator: {d.terminator},",
    s!"        rule: {rule},",
    s!"        effects: &[{", ".intercalate effects}],",
    s!"        tier: {tier},"] ++ layers ++ [
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
  out := emit out rustTargets
  out := emit out s!"static DECLS: [OpDecl; {decls.length}] = ["
  for d in decls do out := emit out (← rustDecl d)
  out := emit out "];"
  pure ("\n".intercalate out.toList ++ "\n")

/-! ## Contracts -/

/-- The theorem that binds `dcePerm`'s deletions to `Dce.PureKind`. -/
def dceTheorem : String := "Fir.Dce.dcePerm_sound"

/-- Effects a kind that may be deleted can't declare. -/
def impureEffects : List Effect := [.write, .alloc, .free, .diverge, .unwind, .sync, .extern]

/-- Every kind an op name spells, with its printed name, in name-table order. -/
def kindsWithNames : List (OpKind × String) := Id.run do
  let mut seen : List OpKind := []
  let mut out := #[]
  for s in opNames do
    if seen.contains s.value then continue
    seen := s.value :: seen
    out := out.push (s.value, s.text)
  pure out.toList

/-- Contradictions between a kind's permissions and its declaration. -/
def contradictions (k : OpKind) (name : String) : List String :=
  let d := k.decl
  let deletes := match Dce.dcePerm k with | .keep => false | _ => true
  if !deletes then [] else
  (if d.terminator then [s!"{name}: dead code elimination may delete it, but it ends a block"] else []) ++
  (if k.callee?.isSome then [s!"{name}: dead code elimination may delete it, but it calls"] else []) ++
  (if k.stackAlloc?.isSome then [s!"{name}: dead code elimination may delete it, but it allocates stack memory"] else []) ++
  (if d.rule.isNone then [s!"{name}: dead code elimination may delete it, but it has no typing rule (control flow)"] else []) ++
  ((d.effects.filter impureEffects.contains).map fun e =>
    s!"{name}: dead code elimination may delete it, but its declaration lists the effect {reprStr e}")

def checkContracts : Except String Unit := do
  let errs := kindsWithNames.flatMap fun (k, n) => contradictions k n
  unless errs.isEmpty do throw ("contradictions:\n" ++ "\n".intercalate errs)

def rustDce (k : OpKind) : String :=
  match Dce.dcePerm k with
  | .delete => s!"Dce::Delete(Evidence::Proved(DCE_THEOREM))"
  | .trusted why => s!"Dce::Delete(Evidence::Trusted({rustStr why}))"
  | .keep => "Dce::Keep"

def generateContracts : Except String String := do
  checkContracts
  let ks := kindsWithNames
  let mut out : Array String := #[]
  out := out.push "// Generated by `lake exe gen-rust contracts` (spec/GenRust.lean) from the op declarations in
// spec/Fir/Syntax.lean and the classifications proved in spec/Fir/DceKinds.lean. Do not edit:
// regenerate with `cd spec && lake exe gen-rust contracts > ../crates/fir/src/generated/contracts.rs`.

use crate::body::{CasesId, IntId, StrId, SuccId};
use crate::contract::{Dce, Evidence, OpContract};
use crate::ir::*;
"
  out := out.push s!"/// The theorem that proves every kind `Dce::Delete(Evidence::Proved(_))` names pure
/// (`∀ k, Fir.Dce.dcePerm k = .delete → Fir.Dce.PureKind k`).
pub const DCE_THEOREM: &str = {rustStr dceTheorem};
"
  out := out.push "impl OpKind {
    /// What the Lean declarations and proofs let a pass do with ops of this kind
    /// ([`crate::contract`]). Every variant and modifier is matched: a kind the Lean name table
    /// doesn't spell is a compile error here.
    pub fn contract(&self) -> &'static OpContract {
        match self {"
  for (k, _) in ks, i in [0:ks.length] do
    out := out.push s!"            {rustKind k true} => &CONTRACTS[{i}],"
  out := out.push "        }
    }
}
"
  out := out.push s!"/// One kind per op name, as the name table holds it (immediates are placeholders), in the
/// order of [`CONTRACTS`].
pub static KINDS: [OpKind; {ks.length}] = ["
  for (k, _) in ks do
    out := out.push s!"    {rustKind k false},"
  out := out.push "];
"
  out := out.push s!"/// The contracts, one per op name.
pub static CONTRACTS: [OpContract; {ks.length}] = ["
  for (k, n) in ks, i in [0:ks.length] do
    out := out.push s!"    OpContract \{ index: {i}, name: {rustStr n}, calls: {k.callee?.isSome}, dce: {rustDce k} },"
  out := out.push "];"
  pure ("\n".intercalate out.toList ++ "\n")

def jsonStr := rustStr

def jsonList (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def jsonDce (k : OpKind) : String :=
  match Dce.dcePerm k with
  | .delete => s!"\{\"permission\": \"delete\", \"evidence\": \"proved\", \"theorem\": {jsonStr dceTheorem}}"
  | .trusted why => s!"\{\"permission\": \"delete\", \"evidence\": \"trusted\", \"why\": {jsonStr why}}"
  | .keep => "{\"permission\": \"keep\"}"

def generateManifest : Except String String := do
  checkContracts
  let ks := kindsWithNames
  let entries := ks.map fun (k, n) =>
    let d := k.decl
    let mods := (d.fields.filter (!·.ty.isImm)).zip k.modReprs |>.map fun (f, r) =>
      s!"{jsonStr f.name}: {jsonStr r}"
    let imms := d.imms.map fun f => s!"\{\"name\": {jsonStr f.name}, \"type\": {jsonStr f.ty.rustDecl}}"
    let effects := d.effects.map fun e => jsonStr ((reprStr e).drop 11).toString
    let layers := d.layers.map fun l => jsonStr l.name
    String.intercalate "\n" [
      "    {",
      s!"      \"name\": {jsonStr n},",
      s!"      \"ctor\": {jsonStr d.ctor},",
      s!"      \"rust\": {jsonStr d.rust},",
      s!"      \"dialect\": {jsonStr d.dialect},",
      s!"      \"modifiers\": \{{", ".intercalate mods}},",
      s!"      \"immediates\": {jsonList imms},",
      s!"      \"layers\": {jsonList layers},",
      s!"      \"terminator\": {d.terminator},",
      s!"      \"typing\": {jsonStr (if d.rule.isSome then "rule" else "control flow (checked against the enclosing regions)")},",
      s!"      \"calls\": {k.callee?.isSome},",
      s!"      \"effects\": \{\"declared\": {jsonList effects}, \"evidence\": \"declared, not checked against the semantics\"},",
      s!"      \"tier\": {jsonStr ((reprStr d.tier).drop 9).toString},",
      s!"      \"dce\": {jsonDce k}",
      "    }"]
  pure <| String.intercalate "\n" [
    "{",
    "  \"generator\": \"lake exe gen-rust manifest (spec/GenRust.lean)\",",
    "  \"note\": \"What the Lean declarations and proofs say about each op kind. A declaration is not a proof: only entries with evidence 'proved' are backed by a theorem, and matching declarations do not make the Rust implementation equivalent to the Lean semantics.\",",
    s!"  \"theorems\": \{\"dce\": \{\"name\": {jsonStr dceTheorem}, \"statement\": \"∀ k, Fir.Dce.dcePerm k = .delete → Fir.Dce.PureKind k\"}},",
    "  \"ops\": [",
    ",\n".intercalate entries,
    "  ]",
    "}"] ++ "\n"

end Fir.GenRust

def main (args : List String) : IO UInt32 := do
  let out := match args with
    | [] | ["ops"] => Fir.GenRust.generate
    | ["contracts"] => Fir.GenRust.generateContracts
    | ["manifest"] => Fir.GenRust.generateManifest
    | _ => .error "usage: gen-rust [ops | contracts | manifest]"
  match out with
  | .ok s => IO.print s; pure 0
  | .error e => IO.eprintln e; pure 1
