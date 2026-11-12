import Fir.Syntax

/-!
# `gen-builder`: the builder API's op methods

```
lake exe gen-builder rust > ../crates/fir/src/generated/builder.rs
lake exe gen-builder capi > ../crates/fir-capi/src/generated/ops.rs
```

Prints, from the op declarations in `Fir.Syntax`, one builder method per op (`rust`: methods of
`fir::FuncBuilder`) and one C function per op over it (`capi`: `extern "C"` functions of the
`fir-capi` crate). The Rust tests check that both files are up to date.

A method is named after the op's dialect (its name up to the first `.`) and its constructor:
`int.{op}.{ovf}` is `int_arith`, `mem.load` is `mem_load`, `cf.cond_br` is `cf_cond_br`. Its
arguments are the result types the op's rule doesn't imply, every modifier, then the immediates
and operands in the order the op's format writes them. An op with regions gets a `_begin` method
that makes it with empty regions, and a method that builds each region in a closure.
-/

namespace Fir.GenBuilder

open Fir

/-- A Rust string literal. -/
def rustStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | c => c.toString) ++ "\""

def docLines (indent doc : String) : List String :=
  if doc.isEmpty then [] else
  (doc.splitOn "\n").map fun l =>
    let l := l.trimAscii.toString
    if l.isEmpty then s!"{indent}///" else s!"{indent}/// {l}"

/-- A variant names its fields when one is a `bool`, a number, a string, a branch target, or a
register (as in `GenRust`). -/
def isStruct (d : OpDecl) : Bool :=
  d.fields.any fun f => match f.ty with
    | .nat | .align | .index | .symbol | .func | .global | .flag | .mod "Bool" | .succ | .cases
    | .reg => true
    | _ => false

/-- `OpKind::Variant(a, b)` or `OpKind::Variant { x: a, y: b }`, each field from its text. -/
def rustApply (d : OpDecl) (vals : List (Field × String)) : String :=
  if d.fields.isEmpty then s!"OpKind::{d.rust}"
  else if isStruct d then
    let items := vals.map fun (f, v) => if v == f.name then f.name else s!"{f.name}: {v}"
    s!"OpKind::{d.rust} \{ {", ".intercalate items} }"
  else
    s!"OpKind::{d.rust}({", ".intercalate (vals.map (·.2))})"

/-- `PtrFromExposed` → `ptr_from_exposed` -/
def snake (s : String) : String :=
  String.join (s.toList.mapIdx fun i c =>
    if c.isUpper then (if i == 0 then "" else "_") ++ c.toLower.toString else c.toString)

/-- The method's name: the dialect, then the constructor in snake case, unless it already starts
with the dialect. The `aarch64` dialect's constructors start with `A64`, which the dialect
replaces: `A64BlAlloc` is `aarch64_bl_alloc`. -/
def methodName (d : OpDecl) (i : Nat) : String :=
  let sn := snake d.rust
  match opNames.find? (·.value.declIdx == i) with
  | some s =>
    match s.text.splitOn "." with
    | dialect :: _ :: _ =>
      let sn := if dialect == "aarch64" && sn.startsWith "a64_" then (sn.drop 4).toString else sn
      if sn == dialect || sn.startsWith (dialect ++ "_") then sn else dialect ++ "_" ++ sn
    | _ => sn
  | none => sn

/-- Where an op's results come from. -/
inductive ResMode where
  /-- No results. -/
  | none
  /-- The rule gives `n` result types (`results [a]`). -/
  | implied (n : Nat)
  /-- The caller gives `n` (`results t "msg"`). -/
  | given (n : Nat)
  /-- The callee's results (`call f`). -/
  | callee (field : String)
  /-- The function type's results (`sig f`). -/
  | sig (field : String)
  /-- An op with regions: the caller gives any number. -/
  | regions

def resMode (d : OpDecl) : ResMode :=
  if !d.regions.isEmpty || d.hasBlocks then .regions else
  match d.rule with
  | none => .none
  | some cs =>
    let m := cs.findSome? fun
      | .call f => some (ResMode.callee f)
      | .sig f => some (.sig f)
      | .takeOuts vs _ => some (.given vs.length)
      | .outs w => some (.implied w.length)
      | .noOuts => some .none
      | _ => none
    m.getD .none

def tyName : TyE → String
  | .ptr => "p"
  | .addr => "n"
  | .int _ => "x"
  | .name _ => "value"

/-- Number repeated names: `p, p` → `p, p1`. -/
def dedupe (ns : List String) : List String :=
  let (_, out) := ns.foldl (init := ([], [])) fun (seen, out) n =>
    let k := seen.count n
    (seen ++ [n], out ++ [if k == 0 then n else s!"{n}{k}"])
  out

/-- The operands' parameter names: the rule's, or from their types. -/
def operandNames (d : OpDecl) : List String :=
  let n := (d.head.filter (· == .operand)).length
  let fromRule := d.rule.bind fun cs => cs.findSome? fun
    | .takeIns vs _ => if vs.length == n then some vs else none
    | .ins _ want => if want.length == n then some (want.map tyName) else none
    | _ => none
  let isSig := d.rule.any (·.any fun | .sig _ => true | _ => false)
  let dflt := if d.ctor == "if_" || d.ctor == "condBr" then "cond" else if isSig then "p" else "x"
  let names := fromRule.getD ((List.range n).map fun _ => dflt)
  -- Positional letters when the names repeat or clash with a field's.
  let clash := names.any (fun x => d.fields.any (·.name == x)) || dedupe names != names
  if clash then (List.range n).map fun i => String.singleton (Char.ofNat ('a'.toNat + i)) else names

/-- A closure's name for each region. -/
def regionNames (d : OpDecl) : List String :=
  let rs := d.regions
  rs.mapIdx fun i kw => match kw with
    | some k => k ++ "_"
    | none =>
      if (rs.drop (i + 1)).any (· == some "else") then "then_"
      else if rs.length == 1 then "body" else s!"region{i}"

/-- One parameter: its name, its Rust and C types, the statements that convert it (Rust, C),
and the expressions passed on (to the kind or `simple` in Rust, to the method in C). -/
structure Param where
  name : String
  rust : String
  c : List (String × String)
  rustConv : List String := []
  /-- The value the kind's field gets. -/
  kindVal : Option String := none
  cConv : List String := []
  cArg : String

/-- The parameter for a field: a modifier or an immediate. -/
def fieldParam (f : Field) : Param :=
  let n := f.name
  match f.ty with
  | .mod "Bool" => { name := n, rust := "bool", c := [(n, "bool")], cArg := n }
  | .mod t => { name := n, rust := t, c := [(n, s!"Fir{t}")], cArg := s!"{t}::from_c({n})?" }
  | .int =>
    { name := n, rust := "impl Into<IntImm>", c := [(n, "i64")], cArg := n,
      rustConv := [s!"let {n}_id = self.int_imm({n}.into());"], kindVal := some s!"{n}_id" }
  | .nat => { name := n, rust := "u64", c := [(n, "u64")], cArg := n }
  | .align | .index => { name := n, rust := "u32", c := [(n, "u32")], cArg := n }
  | .flag => { name := n, rust := "bool", c := [(n, "bool")], cArg := n }
  | .symbol =>
    { name := n, rust := "&str", c := [(n, "*const c_char")], cArg := s!"crate::cstr({n})?",
      rustConv := [s!"let {n}_id = self.str_imm({n})?;"], kindVal := some s!"{n}_id" }
  | .func =>
    { name := n, rust := "FuncRef", c := [(n, "FirFunc")], cArg := s!"FuncRef::from_raw({n})",
      rustConv := [s!"let {n}_id = self.func_imm({n})?;"], kindVal := some s!"{n}_id" }
  | .global =>
    { name := n, rust := "GlobalRef", c := [(n, "FirGlobal")],
      cArg := s!"GlobalRef::from_raw({n})",
      rustConv := [s!"let {n}_id = self.global_imm({n})?;"], kindVal := some s!"{n}_id" }
  | .ty =>
    { name := n, rust := "Ty", c := [(n, "FirType")], cArg := s!"crate::ty({n})?",
      rustConv := [s!"let {n}_id = self.ty_imm({n})?;"], kindVal := some s!"{n}_id" }
  | .succ =>
    { name := n, rust := "Target<'_>", c := [(n, "FirTarget")],
      cConv := [s!"let {n}_args = crate::values({n}.args, {n}.nargs);"],
      cArg := s!"crate::target({n}, {n}_args)",
      rustConv := [s!"let {n}_id = self.succ({n})?;"], kindVal := some s!"{n}_id" }
  | .cases =>
    { name := n, rust := "&[SwitchCase<'_>]", c := [(n, "*const FirCase"), (s!"n{n}", "usize")],
      cConv := [s!"let {n}_v = crate::switch_cases({n}, n{n});"], cArg := s!"&{n}_v",
      rustConv := [s!"let {n}_id = self.cases({n})?;"], kindVal := some s!"{n}_id" }
  | .reg =>
    { name := n, rust := "Reg", c := [(n, "FirReg")], cArg := s!"Reg({n})",
      rustConv := [s!"let {n}_r = self.reg({n})?;"], kindVal := some s!"{n}_r" }

def operandParam (n : String) : Param :=
  { name := n, rust := "impl Into<Operand>", c := [(n, "FirValue")],
    cArg := s!"Operand::from_raw({n})", rustConv := [s!"self.operand({n}.into());"] }

def listParam (n : String) : Param :=
  { name := n, rust := "&[Operand]", c := [(n, "*const FirValue"), (s!"n{n}", "usize")],
    cArg := s!"crate::values({n}, n{n})", rustConv := [s!"self.operand_list({n});"] }

/-- An op with regions or blocks takes its result types, unless it is a terminator
(`aarch64.code`), which has none. -/
def hasResults (d : OpDecl) : Bool :=
  match resMode d with
  | .regions => !d.terminator
  | _ => true

def resultsParam : ResMode → List Param
  | .given 1 =>
    [{ name := "result", rust := "Ty", c := [("result", "FirType")], cArg := "crate::ty(result)?" }]
  | .given _ | .regions =>
    [{ name := "results", rust := "&[Ty]",
       c := [("results", "*const FirType"), ("nresults", "usize")],
       cConv := ["let results = crate::tys(results, nresults)?;"], cArg := "&results" }]
  | _ => []

/-- The parameters, in order: result types, modifiers, then the format's immediates and
operands. -/
def params (d : OpDecl) : List Param := Id.run do
  let mut ps := if hasResults d then resultsParam (resMode d) else []
  for f in d.fields do
    if !f.ty.isImm then ps := ps ++ [fieldParam f]
  let mut ops := operandNames d
  for item in d.head do
    match item with
    | .imm n =>
      if let some f := d.field? n then ps := ps ++ [fieldParam f]
    | .operand =>
      match ops with
      | o :: rest => ps := ps ++ [operandParam o]; ops := rest
      | [] => pure ()
    | .variadic | .args => ps := ps ++ [listParam "args"]
    | .iter => ps := ps ++ [listParam "inits"]
    | _ => pure ()
  return ps

/-- `OpKind::…` with each field from its parameter. -/
def kindExpr (d : OpDecl) (ps : List Param) : String :=
  rustApply d (d.fields.map fun f =>
    (f, (ps.find? (·.name == f.name)).bind (·.kindVal) |>.getD f.name))

def retTy : ResMode → String
  | .none => "OpId"
  | .implied 1 | .given 1 => "ValueId"
  | .regions => "OpId"
  | _ => "Results"

def nRegions (d : OpDecl) : Nat := d.regions.length

def sigText (ps : List Param) : String :=
  ", ".intercalate ("&mut self" :: ps.map fun p => s!"{p.name}: {p.rust}")

/-- The Rust methods for one op. -/
def rustOp (d : OpDecl) (i : Nat) : List String := Id.run do
  let name := methodName d i
  let ps := params d
  let mode := resMode d
  let mut out := docLines "    " d.doc
  let isRegions := match mode with | .regions => true | _ => false
  let begin := if isRegions then name ++ "_begin" else name
  if isRegions then
    out := out ++ ["    ///", "    /// Makes the op with empty regions; see the closure form."]
  out := out ++ [s!"    pub fn {begin}({sigText ps}) -> Result<{retTy mode}, BuildError> \{",
    "        self.begin_op();"]
  for p in ps do
    for s in p.rustConv do out := out ++ [s!"        {s}"]
  out := out ++ [s!"        let kind = {kindExpr d ps};"]
  let res := match mode with
    | .none => "Res::None"
    | .implied _ => "Res::Implied"
    | .given 1 => "Res::Given(&[result])"
    | .given _ => "Res::Given(results)"
    | .callee f => s!"Res::Callee({f})"
    | .sig f => s!"Res::Sig({f}_id)"
    | .regions => ""
  match mode with
  | .regions =>
    let iter := d.items.contains .iter
    let results := if hasResults d then "results" else "&[]"
    out := out ++ [s!"        self.region_op(kind, {results}, {nRegions d}, {iter})"]
  | .none => out := out ++ [s!"        self.simple(kind, {res})"]
  | .implied 1 | .given 1 =>
    out := out ++ [s!"        let made = self.simple(kind, {res})?;", "        Ok(self.result(made, 0))"]
  | _ =>
    out := out ++ [s!"        let made = self.simple(kind, {res})?;", "        Ok(self.all_results(made))"]
  out := out ++ ["    }", ""]
  if !isRegions then return out
  -- The closure form.
  let iter := d.items.contains .iter
  let closures := (regionNames d).mapIdx fun j r =>
    if iter && j == 0 then (r, "impl FnOnce(&mut Self, Values) -> Result<(), BuildError>")
    else (r, "impl FnOnce(&mut Self) -> Result<(), BuildError>")
  let closures := if d.hasBlocks then
      closures ++ [("blocks", "impl FnOnce(&mut Self, OpId) -> Result<(), BuildError>")]
    else closures
  out := out ++ docLines "    " d.doc
  out := out ++ ["    ///",
    "    /// Builds each region in a closure, with the insertion point at its end, and returns to",
    "    /// the insertion point after the op."]
  let sig := sigText (ps ++ closures.map fun (n, t) => { name := n, rust := t, c := [], cArg := "" })
  out := out ++ [s!"    pub fn {name}({sig}) -> Result<Results, BuildError> \{"]
  let args := ", ".intercalate (ps.map (·.name))
  out := out ++ [s!"        let op = self.{begin}({args})?;"]
  for (r, _) in closures, j in [0:closures.length] do
    if d.hasBlocks && r == "blocks" then
      out := out ++ ["        self.in_blocks(op, blocks)?;"]
    else
      out := out ++ [s!"        let r = self.region(op, {j})?;"]
      if iter && j == 0 then
        out := out ++ ["        let params = self.region_params(r)?;",
          s!"        self.in_region(r, |f| {r}(f, params))?;"]
      else
        out := out ++ [s!"        self.in_region(r, {r})?;"]
  out := out ++ ["        Ok(self.all_results(op))", "    }", ""]
  return out

def generateRust : String := Id.run do
  let decls := opDecls.toList
  let mut out : Array String := #[
    "// Generated by `lake exe gen-builder rust` (spec/GenBuilder.lean) from the op declarations in",
    "// spec/Fir/Syntax.lean. Do not edit: change the declarations and regenerate with",
    "// `cd spec && lake exe gen-builder rust > ../crates/fir/src/generated/builder.rs`.",
    "",
    "use crate::body::{OpId, Operand, ValueId};",
    "use crate::builder::{",
    "    BuildError, FuncBuilder, FuncRef, GlobalRef, IntImm, Res, Results, SwitchCase, Target, Values,",
    "};",
    "use crate::ir::*;",
    "",
    "/// One method per op, generated from its declaration.",
    "impl FuncBuilder<'_> {"]
  for d in decls, i in [0:decls.length] do
    out := out ++ (rustOp d i).toArray
  out := out.pop.push "}"
  return "\n".intercalate out.toList ++ "\n"

/-- The C function for one op (the `_begin` form for ops with regions). -/
def capiOp (d : OpDecl) (i : Nat) : List String := Id.run do
  let name := methodName d i
  let ps := params d
  let mode := resMode d
  let isRegions := match mode with | .regions => true | _ => false
  let method := if isRegions then name ++ "_begin" else name
  let (cRet, conv) := match mode with
    | .none | .regions => ("FirOp", "|op| op.raw()")
    | .implied 1 | .given 1 => ("FirValue", "|v| v.raw()")
    | _ => ("FirOp", "|r| r.op.raw()")
  let mut out := docLines "" d.doc
  if isRegions then
    out := out ++ ["///", "/// Makes the op with empty regions: fill them with `fir_position_at_end`."]
  let cps := ps.flatMap (·.c)
  let sig := ", ".intercalate ("fb: *mut FirBuilder" :: cps.map fun (n, t) => s!"{n}: {t}")
  out := out ++ ["#[unsafe(no_mangle)]",
    s!"pub unsafe extern \"C\" fn fir_{method}({sig}) -> {cRet} \{",
    "    unsafe {",
    "        with_builder(fb, FIR_INVALID, |builder| {"]
  for p in ps do
    for s in p.cConv do out := out ++ [s!"            {s}"]
  let args := ", ".intercalate (ps.map (·.cArg))
  out := out ++ [s!"            builder.{method}({args}).map({conv})", "        })", "    }", "}", ""]
  return out

def generateCapi : String := Id.run do
  let decls := opDecls.toList
  let mut out : Array String := #[
    "// Generated by `lake exe gen-builder capi` (spec/GenBuilder.lean) from the op declarations in",
    "// spec/Fir/Syntax.lean. Do not edit: change the declarations and regenerate with",
    "// `cd spec && lake exe gen-builder capi > ../crates/fir-capi/src/generated/ops.rs`.",
    "//",
    "// One C function per op, over the method of `fir::FuncBuilder` with the same name. On failure",
    "// each returns `FIR_INVALID` and leaves the message in `fir_module_error`.",
    "",
    "use std::os::raw::c_char;",
    "",
    "use fir::{FuncRef, GlobalRef, Operand, Reg};",
    "",
    "use crate::*;",
    ""]
  for d in decls, i in [0:decls.length] do
    out := out ++ (capiOp d i).toArray
  out := out.pop
  return "\n".intercalate out.toList ++ "\n"

end Fir.GenBuilder

def main (args : List String) : IO UInt32 := do
  match args with
  | ["rust"] => IO.print Fir.GenBuilder.generateRust; pure 0
  | ["capi"] => IO.print Fir.GenBuilder.generateCapi; pure 0
  | _ => IO.eprintln "usage: gen-builder (rust | capi)"; pure 2
