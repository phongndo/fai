import Fir.Basic
import Fir.Syntax
import Fir.Interp

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
  | .copy => "copy"
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
  | .memStack .. => "mem.stack"
  | .memAlloc f .. => s!"mem.alloc.{match f with | .null => "null" | .trap => "trap"}"
  | .memFree _ => "mem.free"
  | .load _ => "mem.load"
  | .store .. => "mem.store"
  | .ptrOffset ib => if ib then "ptr.offset.inbounds" else "ptr.offset.wrap"
  | .ptrAddr => "ptr.addr"
  | .ptrExpose => "ptr.expose"
  | .ptrFromExposed => "ptr.from_exposed"
  | .ptrWithAddr => "ptr.with_addr"
  | .ptrNull => "ptr.null"
  | .ptrCmp p => s!"ptr.cmp.{p.name}"
  | .call _ => "func.call"

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

mutual
  partial def renderRegion (showLocs : Bool) (indent : String) (r : Region) : String :=
    let body := r.ops.map (renderOp showLocs (indent ++ "  "))
    "{\n" ++ String.join body ++ indent ++ "}"

  partial def renderOp (showLocs : Bool) (indent : String) (op : Op) : String :=
    let results := if op.results.isEmpty then "" else
      commas (op.results.map Result.render) ++ " = "
    let loc := renderOpLoc showLocs op.loc
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
          let items := (body.params.zip op.args).map fun (r, a) =>
            s!"{r.render} = {a.render}"
          s!" iter({commas items})"
        s!"cf.loop{prog}{iter}{loc} " ++ renderRegion showLocs indent body
      | .memStack size align, _ => s!"mem.stack {size}, align {align}{loc}"
      | .memAlloc _ family align, _ => s!"{op.kind.name} {family} {args}, align {align}{loc}"
      | .memFree family, _ => s!"mem.free {family} {args}{loc}"
      | .load align, _ => s!"mem.load {args}, align {align}{loc}"
      | .store t align, _ => s!"mem.store {t} {args}, align {align}{loc}"
      | .call callee, _ => s!"func.call @{callee}({args}){loc}"
      | k, _ =>
        let sep := if args.isEmpty then "" else " "
        s!"{k.name}{sep}{args}{loc}"
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
