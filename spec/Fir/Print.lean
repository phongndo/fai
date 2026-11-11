import Fir.Basic
import Fir.Syntax

/-!
# Printer

Prints modules in canonical text, which the parser reads back unchanged.
-/

namespace Fir

def Ovf.suffix : Ovf → String
  | .wrap => "wrap"
  | .nsw => "nsw"
  | .nuw => "nuw"
  | .nswNuw => "nsw.nuw"
  | .trap s => if s then "s.trap" else "u.trap"
  | .sat s => if s then "s.sat" else "u.sat"
  | .ub s => if s then "s.ub" else "u.ub"

def Edge.name : Edge → String
  | .ub => "ub"
  | .trap => "trap"
  | .total => "total"
  | .wrap => "wrap"

def ShiftEdge.name : ShiftEdge → String
  | .ub => "ub"
  | .trap => "trap"
  | .mask => "mask"
  | .total => "total"

def Pred.name : Pred → String
  | .eq => "eq" | .ne => "ne"
  | .slt => "slt" | .sle => "sle" | .sgt => "sgt" | .sge => "sge"
  | .ult => "ult" | .ule => "ule" | .ugt => "ugt" | .uge => "uge"

/-- The division modifiers: one when it covers both edge cases, otherwise two. -/
def divSuffix (signed : Bool) (zero ovf : Edge) : String :=
  if !signed || (zero, ovf) == (.ub, .ub) || (zero, ovf) == (.trap, .trap) ||
      (zero, ovf) == (.total, .wrap) then zero.name
  else s!"{zero.name}.{ovf.name}"

def OpKind.name : OpKind → String
  | .const _ => "int.const"
  | .poison => "poison"
  | .freeze => "freeze"
  | .select => "select"
  | .arith op o =>
    let n := match op with | .add => "add" | .sub => "sub" | .mul => "mul"
    s!"int.{n}.{o.suffix}"
  | .bit op => match op with | .and => "int.and" | .or => "int.or" | .xor => "int.xor"
  | .div op z o =>
    let n := match op with
      | .divS => "div.s" | .divU => "div.u" | .remS => "rem.s" | .remU => "rem.u"
    s!"int.{n}.{divSuffix op.signed z o}"
  | .shift op e =>
    let n := match op with | .shl => "shl" | .shrU => "shr.u" | .shrS => "shr.s"
    s!"int.{n}.{e.name}"
  | .cmp p => s!"int.cmp.{p.name}"
  | .zext => "int.zext"
  | .sext => "int.sext"
  | .trunc m => s!"int.trunc.{match m with | .wrap => "wrap" | .nsw => "nsw" | .nuw => "nuw"}"
  | .if_ => "cf.if"
  | .loop _ => "cf.loop"
  | .yield => "cf.yield"
  | .brk => "cf.break"
  | .cont => "cf.continue"
  | .ret => "func.ret"

def Trust.name : Trust → String
  | .assume => "assume"
  | .check => "check"
  | .proved => "proved"

def TrustedFact.render : TrustedFact → String
  | ⟨.rangeS lo hi, t⟩ => s!"range.s({lo}, {hi}) {t.name}"
  | ⟨.rangeU lo hi, t⟩ => s!"range.u({lo}, {hi}) {t.name}"

def Result.render (r : Result) : String :=
  let facts := if r.facts.isEmpty then "" else
    s!" [{", ".intercalate (r.facts.map TrustedFact.render)}]"
  s!"%{r.name}: {r.ty}{facts}"

def Operand.render : Operand → String
  | .var n => s!"%{n}"
  | .hole n t => s!"?{n}: {t}"

def renderLoc (showLocs : Bool) : Option Loc → String
  | some l => if showLocs then s!" @{l.line}:{l.col}" else ""
  | none => ""

def commas (xs : List String) : String := ", ".intercalate xs

mutual
  partial def renderRegion (showLocs : Bool) (indent : String) (r : Region) : String :=
    let body := r.ops.map (renderOp showLocs (indent ++ "  "))
    "{\n" ++ String.join body ++ indent ++ "}"

  partial def renderOp (showLocs : Bool) (indent : String) (op : Op) : String :=
    let results := if op.results.isEmpty then "" else
      commas (op.results.map Result.render) ++ " = "
    let loc := renderLoc showLocs op.loc
    let args := commas (op.args.map Operand.render)
    let line := match op.kind, op.regions with
      | .const n, _ => s!"int.const {n}{loc}"
      | .if_, [thn, els] =>
        let elsText := if els.ops.isEmpty then "" else
          " else " ++ renderRegion showLocs indent els
        s!"cf.if {args}{loc} " ++ renderRegion showLocs indent thn ++ elsText
      | .loop p, [body] =>
        let prog := if p then " progress" else ""
        let iter := if body.params.isEmpty then "" else
          let items := (body.params.zip op.args).map fun ((n, t), a) =>
            s!"%{n}: {t} = {a.render}"
          s!" iter({commas items})"
        s!"cf.loop{prog}{iter}{loc} " ++ renderRegion showLocs indent body
      | k, _ =>
        let sep := if args.isEmpty then "" else " "
        s!"{k.name}{sep}{args}{loc}"
    indent ++ results ++ line ++ "\n"
end

def Func.render (showLocs : Bool) (f : Func) : String :=
  let params := commas (f.params.map fun (n, t) => s!"%{n}: {t}")
  let rets := match f.rets with
    | [] => ""
    | [t] => s!" -> {t}"
    | ts => s!" -> ({commas (ts.map toString)})"
  let file := match f.file with
    | some s => if showLocs then s!" loc \"{s}\"" else ""
    | none => ""
  s!"func @{f.name}({params}){rets}{file} " ++ renderRegion showLocs "" f.body ++ "\n"

def Module.render (m : Module) (showLocs := true) : String :=
  "\n".intercalate (m.funcs.map (Func.render showLocs))

/-- Integers print signed, except `i1`, which prints as `0` or `1`. -/
def RVal.render : RVal → String
  | ⟨w, .poison⟩ => s!"i{w} poison"
  | ⟨w, .bits b⟩ => if w = 1 then s!"i1 {b.toNat}" else s!"i{w} {b.toInt}"

def renderHaltLoc : Option Loc → String
  | some l => s!" @{l.line}:{l.col}"
  | none => ""

/-- One line describing how a run ended. Tests compare against this text. -/
def renderHalt : Behavior × Option Loc → String
  | (.ret [], _) => "returned"
  | (.ret vs, _) => s!"returned {commas (vs.map RVal.render)}"
  | (.trap r, l) => s!"trap {r.name}{renderHaltLoc l}"
  | (.ub k, l) => s!"ub {k.name}{renderHaltLoc l}"
  | (.hole n, l) => s!"hole ?{n}{renderHaltLoc l}"
  | (.stuck msg, l) => s!"stuck{renderHaltLoc l}: {msg}"
  | (.diverge, _) => "diverges"

end Fir
