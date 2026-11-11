import Std.Data.HashMap
import Std.Data.HashSet
import Fir.Syntax

/-!
# Verifier

The rules a well-formed FIR-0 module must follow. A verified module never gets `stuck` in the
interpreter.

* Types: every `iN` has `N ≥ 1`.
* SSA: every value is defined once per function, and used only where it is visible (after its
  definition, in the same region or a nested one).
* Ops: operand counts and types match the op; constants and facts fit their type.
* Control flow: a terminator is the last op of its region. `cf.yield` ends a `cf.if` region;
  `cf.break` and `cf.continue` appear inside a loop; loop bodies end with a terminator; a
  function body ends with `func.ret`.

Holes are allowed. They're collected and reported with the type each one must have.
-/

namespace Fir

/-- The region being checked. -/
inductive RegionCtx where
  | func (rets : List Ty)
  | ifBranch (results : List Ty)
  | loopBody (params : List Ty) (results : List Ty)

structure Hole where
  name : String
  ty : Ty
  loc : Option Loc

structure VState where
  defined : Std.HashSet String := {}
  holes : Array Hole := #[]

abbrev VM := StateT VState (Except String)

def Loc.render : Option Loc → String
  | some l => s!"@{l.line}:{l.col}"
  | none => "@?"

def verr (loc : Option Loc) (msg : String) : VM α := throw s!"{Loc.render loc}: {msg}"

abbrev Scope := Std.HashMap String Ty

def checkTy (loc : Option Loc) (t : Ty) : VM Unit :=
  if t.width = 0 then verr loc "i0 is not a valid type" else pure ()

def define (loc : Option Loc) (scope : Scope) (name : String) (t : Ty) : VM Scope := do
  checkTy loc t
  if (← get).defined.contains name then verr loc s!"%{name} is defined more than once"
  modify fun s => { s with defined := s.defined.insert name }
  pure (scope.insert name t)

def operandTy (loc : Option Loc) (scope : Scope) : Operand → VM Ty
  | .var n =>
    match scope[n]? with
    | some t => pure t
    | none => verr loc s!"%{n} is not defined here"
  | .hole n t => do
    checkTy loc t
    modify fun s => { s with holes := s.holes.push { name := n, ty := t, loc } }
    pure t

def expectTys (loc : Option Loc) (what : String) (got want : List Ty) : VM Unit :=
  if got == want then pure ()
  else verr loc s!"{what}: expected ({", ".intercalate (want.map toString)}) but got ({", ".intercalate (got.map toString)})"

def fitsSigned (w : Nat) (n : Int) : Bool := -(2 ^ (w - 1) : Int) ≤ n && n < 2 ^ (w - 1)
def fitsUnsigned (w : Nat) (n : Int) : Bool := 0 ≤ n && n < 2 ^ w

def checkFact (loc : Option Loc) (t : Ty) : TrustedFact → VM Unit
  | ⟨.rangeS lo hi, _⟩ =>
    unless fitsSigned t.width lo && fitsSigned t.width hi && lo ≤ hi do
      verr loc s!"range.s({lo}, {hi}) is not a valid signed range for {t}"
  | ⟨.rangeU lo hi, _⟩ =>
    unless fitsUnsigned t.width lo && fitsUnsigned t.width hi && lo ≤ hi do
      verr loc s!"range.u({lo}, {hi}) is not a valid unsigned range for {t}"

/-- Check the operand and result types of an op without regions. -/
def checkSimple (loc : Option Loc) (k : OpKind) (ins : List Ty) (outs : List Ty) : VM Unit := do
  let one (t : Ty) := expectTys loc "results" outs [t]
  match k with
  | .const n =>
    expectTys loc "operands" ins []
    let [t] := outs | verr loc "int.const has one result"
    unless fitsSigned t.width n || fitsUnsigned t.width n do
      verr loc s!"{n} does not fit in {t}"
  | .poison =>
    expectTys loc "operands" ins []
    let [_] := outs | verr loc "poison has one result"
  | .freeze =>
    let [t] := ins | verr loc "freeze takes one operand"
    one t
  | .select =>
    let [c, a, b] := ins | verr loc "select takes three operands"
    expectTys loc "select" [c, b] [.int 1, a]
    one a
  | .arith .. | .bit _ | .div .. | .shift .. =>
    let [a, b] := ins | verr loc "this op takes two operands"
    expectTys loc "operands" [b] [a]
    one a
  | .cmp _ =>
    let [a, b] := ins | verr loc "int.cmp takes two operands"
    expectTys loc "operands" [b] [a]
    one (.int 1)
  | .zext | .sext =>
    let [a] := ins | verr loc "this op takes one operand"
    let [t] := outs | verr loc "this op has one result"
    unless t.width > a.width do verr loc s!"cannot extend {a} to {t}"
  | .trunc _ =>
    let [a] := ins | verr loc "int.trunc takes one operand"
    let [t] := outs | verr loc "int.trunc has one result"
    unless t.width < a.width do verr loc s!"cannot truncate {a} to {t}"
  | _ => verr loc "unexpected op"

def nearestLoop : List RegionCtx → Option (List Ty × List Ty)
  | [] => none
  | .loopBody ps rs :: _ => some (ps, rs)
  | _ :: rest => nearestLoop rest

def funcRets : List RegionCtx → List Ty
  | [] => []
  | [.func rets] => rets
  | _ :: rest => funcRets rest

mutual
  /-- Check the ops of a region. `ctx` lists the enclosing regions, innermost first. -/
  partial def verifyOps (ctx : List RegionCtx) (scope : Scope) (regionLoc : Option Loc) :
      List Op → VM Unit
    | [] =>
      match ctx with
      | .ifBranch [] :: _ => pure ()
      | .ifBranch _ :: _ => verr regionLoc "this cf.if region must end with cf.yield"
      | .loopBody .. :: _ => verr regionLoc "a loop body must end with cf.break or cf.continue"
      | _ => verr regionLoc "the function body must end with func.ret"
    | op :: rest => do
      let scope ← verifyOp ctx scope op
      if op.kind.isTerminator && !rest.isEmpty then
        verr op.loc "a terminator must be the last op of its region"
      if op.kind.isTerminator then pure () else verifyOps ctx scope regionLoc rest

  partial def verifyOp (ctx : List RegionCtx) (scope : Scope) (op : Op) : VM Scope := do
    let loc := op.loc
    let ins ← op.args.mapM (operandTy loc scope)
    let outs := op.results.map (·.ty)
    for r in op.results do
      for f in r.facts do checkFact loc r.ty f
    match op.kind, op.regions with
    | .yield, [] =>
      let .ifBranch rs :: _ := ctx | verr loc "cf.yield must end a cf.if region"
      expectTys loc "cf.yield" ins rs
    | .brk, [] =>
      let some (_, rs) := nearestLoop ctx | verr loc "cf.break outside a loop"
      expectTys loc "cf.break" ins rs
    | .cont, [] =>
      let some (ps, _) := nearestLoop ctx | verr loc "cf.continue outside a loop"
      expectTys loc "cf.continue" ins ps
    | .ret, [] => expectTys loc "func.ret" ins (funcRets ctx)
    | .if_, [thn, els] =>
      expectTys loc "cf.if condition" ins [.int 1]
      for r in [thn, els] do
        unless r.params.isEmpty do verr loc "cf.if regions have no parameters"
        verifyOps (.ifBranch outs :: ctx) scope loc r.ops
    | .loop _, [body] =>
      let ps := body.params.map (·.2)
      expectTys loc "cf.loop initial values" ins ps
      let mut inner := scope
      for (n, t) in body.params do inner ← define loc inner n t
      verifyOps (.loopBody ps outs :: ctx) inner loc body.ops
    | k, [] =>
      if k.isTerminator || k matches .if_ || k matches .loop _ then
        verr loc "malformed op"
      checkSimple loc k ins outs
    | _, _ => verr loc "malformed op"
    let mut scope := scope
    for r in op.results do scope ← define loc scope r.name r.ty
    pure scope
end

def verifyFunc (f : Func) : VM Unit := do
  modify fun s => { s with defined := {} }
  for t in f.rets do checkTy none t
  let mut scope : Scope := {}
  for (n, t) in f.params do scope ← define none scope n t
  verifyOps [.func f.rets] scope none f.body.ops

/-- Verify a module. On success, returns the holes it contains. -/
def verifyModule (m : Module) : Except String (Array Hole) := do
  let mut names : Std.HashSet String := {}
  for f in m.funcs do
    if names.contains f.name then throw s!"function @{f.name} is defined more than once"
    names := names.insert f.name
  let (_, st) ← (m.funcs.forM fun f =>
    tryCatch (verifyFunc f) fun e => throw s!"in @{f.name}: {e}").run {}
  pure st.holes

end Fir
