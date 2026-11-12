import Std.Data.HashMap
import Std.Data.HashSet
import Fir.Syntax

/-!
# Verifier

The rules a well-formed module must follow. A verified module never gets `stuck` in the
interpreter.

* Types: `iN` has `N ≥ 1`; `bN` has `N` a positive multiple of 8. Memory spaces have positive
  sizes that are multiples of 8, with the address size at most the pointer size.
* SSA: every value is defined once per function, and used only where it is visible (after its
  definition, in the same region or a nested one).
* Ops: operand counts and types match the op; constants and facts fit their type; alignments
  are powers of two; calls match the callee's signature.
* Control flow: a terminator is the last op of its region. `cf.yield` ends a `cf.if` region;
  `cf.break` and `cf.continue` appear inside a loop; loop bodies end with a terminator; a
  function body ends with `func.ret`.
* Facts: ranges apply to integers, `nonnull` and `align` to pointers, and `noalias` and
  `readonly` only to pointer parameters of functions.

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
  space : SpaceCfg := {}
  /-- Each function's parameter and return types. -/
  sigs : Std.HashMap String (List Ty × List Ty) := {}

abbrev VM := StateT VState (Except String)

def Loc.render : Option Loc → String
  | some l => s!"@{l.line}:{l.col}"
  | none => "@?"

def verr (loc : Option Loc) (msg : String) : VM α := throw s!"{Loc.render loc}: {msg}"

abbrev VScope := Std.HashMap String Ty

def checkTy (loc : Option Loc) : Ty → VM Unit
  | .int 0 => verr loc "i0 is not a valid type"
  | .byte w => unless w > 0 && w % 8 == 0 do verr loc s!"b{w} is not a valid type"
  | _ => pure ()

def isPow2 (n : Nat) : Bool := n > 0 && n &&& (n - 1) == 0

def fitsSigned (w : Nat) (n : Int) : Bool := -(2 ^ (w - 1) : Int) ≤ n && n < 2 ^ (w - 1)
def fitsUnsigned (w : Nat) (n : Int) : Bool := 0 ≤ n && n < 2 ^ w

def checkFact (loc : Option Loc) (isParam : Bool) (name : String) (t : Ty) :
    TrustedFact → VM Unit
  | ⟨.rangeS lo hi, _⟩ =>
    unless t.isInt && fitsSigned t.width lo && fitsSigned t.width hi && lo ≤ hi do
      verr loc s!"range.s({lo}, {hi}) is not a valid signed range for {t}"
  | ⟨.rangeU lo hi, _⟩ =>
    unless t.isInt && fitsUnsigned t.width lo && fitsUnsigned t.width hi && lo ≤ hi do
      verr loc s!"range.u({lo}, {hi}) is not a valid unsigned range for {t}"
  | ⟨.nonnull, _⟩ => unless t == .ptr do verr loc s!"nonnull applies to pointers, not {t}"
  | ⟨.align n, _⟩ =>
    unless t == .ptr && isPow2 n do verr loc s!"align({n}) needs a pointer and a power of two"
  | ⟨.noalias, _⟩ | ⟨.readonly, _⟩ =>
    unless t == .ptr && isParam do
      verr loc s!"%{name}: noalias and readonly apply only to pointer parameters of functions"

def define (loc : Option Loc) (scope : VScope) (r : Result) (isParam := false) : VM VScope := do
  checkTy loc r.ty
  for f in r.facts do checkFact loc isParam r.name r.ty f
  if (← get).defined.contains r.name then verr loc s!"%{r.name} is defined more than once"
  modify fun s => { s with defined := s.defined.insert r.name }
  pure (scope.insert r.name r.ty)

def operandTy (loc : Option Loc) (scope : VScope) : Operand → VM Ty
  | .var n =>
    match scope[n]? with
    | some t => pure t
    | none => verr loc s!"%{n} is not defined here"
  | .hole n t => do
    checkTy loc t
    modify fun s => { s with holes := s.holes.push { name := n, ty := t, loc } }
    pure t

def tys (ts : List Ty) : String := s!"({", ".intercalate (ts.map toString)})"

def expectTys (loc : Option Loc) (what : String) (got want : List Ty) : VM Unit :=
  if got == want then pure ()
  else verr loc s!"{what}: expected {tys want} but got {tys got}"

def isLoadable (space : SpaceCfg) : Ty → Bool
  | .int w => w % 8 == 0
  | .ptr => space.ptrBits % 8 == 0
  | .byte _ => true

/-- Check the operand and result types of an op without regions. -/
def checkSimple (loc : Option Loc) (k : OpKind) (ins outs : List Ty) : VM Unit := do
  let st ← get
  let addr := Ty.int st.space.addrBits
  let one (t : Ty) := expectTys loc "results" outs [t]
  let ints (ts : List Ty) := unless ts.all Ty.isInt do verr loc s!"expected integers but got {tys ts}"
  match k with
  | .const n =>
    expectTys loc "operands" ins []
    let [t] := outs | verr loc "int.const has one result"
    ints [t]
    unless fitsSigned t.width n || fitsUnsigned t.width n do
      verr loc s!"{n} does not fit in {t}"
  | .poison =>
    expectTys loc "operands" ins []
    let [t] := outs | verr loc "poison has one result"
    ints [t]
  | .freeze =>
    let [t] := ins | verr loc "freeze takes one operand"
    ints [t]
    one t
  | .copy =>
    let [t] := ins | verr loc "copy takes one operand"
    one t
  | .select =>
    let [c, a, b] := ins | verr loc "select takes three operands"
    expectTys loc "select" [c, b] [.int 1, a]
    ints [a]
    one a
  | .arith .. | .bit _ | .div .. | .shift .. =>
    let [a, b] := ins | verr loc "this op takes two operands"
    expectTys loc "operands" [b] [a]
    ints [a]
    one a
  | .cmp _ =>
    let [a, b] := ins | verr loc "int.cmp takes two operands"
    expectTys loc "operands" [b] [a]
    ints [a]
    one (.int 1)
  | .zext | .sext =>
    let [a] := ins | verr loc "this op takes one operand"
    let [t] := outs | verr loc "this op has one result"
    ints [a, t]
    unless t.width > a.width do verr loc s!"cannot extend {a} to {t}"
  | .trunc _ =>
    let [a] := ins | verr loc "int.trunc takes one operand"
    let [t] := outs | verr loc "int.trunc has one result"
    ints [a, t]
    unless t.width < a.width do verr loc s!"cannot truncate {a} to {t}"
  | .memStack _ align =>
    unless isPow2 align do verr loc "alignment must be a power of two"
    expectTys loc "operands" ins []
    one .ptr
  | .memAlloc _ _ align =>
    unless isPow2 align do verr loc "alignment must be a power of two"
    expectTys loc "mem.alloc size" ins [addr]
    one .ptr
  | .memFree _ =>
    expectTys loc "operands" ins [.ptr]
    one' outs
  | .load align =>
    unless isPow2 align do verr loc "alignment must be a power of two"
    expectTys loc "operands" ins [.ptr]
    let [t] := outs | verr loc "mem.load has one result"
    unless isLoadable st.space t do verr loc s!"{t} can't be loaded: its size isn't whole bytes"
  | .store t align =>
    unless isPow2 align do verr loc "alignment must be a power of two"
    expectTys loc "operands" ins [t, .ptr]
    unless isLoadable st.space t do verr loc s!"{t} can't be stored: its size isn't whole bytes"
    one' outs
  | .ptrOffset _ => expectTys loc "operands" ins [.ptr, addr]; one .ptr
  | .ptrAddr | .ptrExpose => expectTys loc "operands" ins [.ptr]; one addr
  | .ptrFromExposed => expectTys loc "operands" ins [addr]; one .ptr
  | .ptrWithAddr => expectTys loc "operands" ins [.ptr, addr]; one .ptr
  | .ptrNull => expectTys loc "operands" ins []; one .ptr
  | .ptrCmp p =>
    if p matches .slt | .sle | .sgt | .sge then verr loc "pointer comparisons are unsigned"
    expectTys loc "operands" ins [.ptr, .ptr]
    one (.int 1)
  | .call callee =>
    let some (params, rets) := st.sigs[callee]? | verr loc s!"no function @{callee}"
    expectTys loc s!"arguments of @{callee}" ins params
    expectTys loc s!"results of @{callee}" outs rets
  | _ => verr loc "unexpected op"
where
  one' (outs : List Ty) : VM Unit :=
    unless outs.isEmpty do verr none "this op has no results"

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
  partial def verifyOps (ctx : List RegionCtx) (scope : VScope) (regionLoc : Option Loc) :
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

  partial def verifyOp (ctx : List RegionCtx) (scope : VScope) (op : Op) : VM VScope := do
    let loc := op.loc
    let ins ← op.args.mapM (operandTy loc scope)
    let outs := op.results.map (·.ty)
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
      let ps := body.params.map (·.ty)
      expectTys loc "cf.loop initial values" ins ps
      let mut inner := scope
      for r in body.params do inner ← define loc inner r
      verifyOps (.loopBody ps outs :: ctx) inner loc body.ops
    | k, [] =>
      if k.isTerminator || k matches .if_ || k matches .loop _ then
        verr loc "malformed op"
      checkSimple loc k ins outs
    | _, _ => verr loc "malformed op"
    let mut scope := scope
    for r in op.results do scope ← define loc scope r
    pure scope
end

def verifyFunc (f : Func) : VM Unit := do
  modify fun s => { s with defined := {} }
  for t in f.rets do checkTy none t
  let mut scope : VScope := {}
  for r in f.params do scope ← define none scope r (isParam := true)
  verifyOps [.func f.rets] scope none f.body.ops

/-- Verify a module. On success, returns the holes it contains. -/
def verifyModule (m : Module) : Except String (Array Hole) := do
  let sp := m.space
  unless sp.ptrBits > 0 && sp.ptrBits % 8 == 0 && sp.addrBits > 0 && sp.addrBits % 8 == 0 &&
      sp.addrBits ≤ sp.ptrBits do
    throw s!"memspace: pointer size {sp.ptrBits} and address size {sp.addrBits} must be positive multiples of 8, with the address size at most the pointer size"
  let mut sigs : Std.HashMap String (List Ty × List Ty) := {}
  for f in m.funcs do
    if sigs.contains f.name then throw s!"function @{f.name} is defined more than once"
    sigs := sigs.insert f.name (f.params.map (·.ty), f.rets)
  let (_, st) ← (m.funcs.forM fun f =>
    tryCatch (verifyFunc f) fun e => throw s!"in @{f.name}: {e}").run { space := sp, sigs }
  pure st.holes

end Fir
