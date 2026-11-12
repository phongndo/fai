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
  definition, in the same region or a nested one). The blocks of `cf.blocks` are regions too: a
  value defined in a block is visible only in that block, and values from outside the
  `cf.blocks` in all of them; block arguments carry values from one block to another.
* Ops: operand counts and types match the op; constants and facts fit their type; alignments
  are powers of two; calls match the callee's signature.
* Control flow: a terminator is the last op of its region. `cf.yield` ends a `cf.if` region or
  a block; `cf.break` and `cf.continue` appear inside a loop; loop bodies and blocks end with a
  terminator; a function body ends with `func.ret`.
* Blocks: `cf.blocks` has at least one block; every block has a label, unique in its
  `cf.blocks`, and no other region has one; the first block has no parameters. `cf.br`,
  `cf.cond_br`, and `cf.switch` appear inside `cf.blocks` (possibly inside `cf.if` and `cf.loop`
  regions there) and name blocks of the nearest one, with arguments of the blocks' parameter
  types. A switch is on an integer, with keys that fit its type and differ modulo `2^N`.
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
  /-- A block of `cf.blocks`: the labels of its blocks with their parameter types, and the
  `cf.blocks`'s results. -/
  | block (blocks : List (String × List Ty)) (results : List Ty)

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

/-- Check the operand and result types of an op without regions, by its declared rule. -/
def checkSimple (loc : Option Loc) (k : OpKind) (ins outs : List Ty) : VM Unit := do
  let st ← get
  let addr := Ty.int st.space.addrBits
  let some rule := k.decl.rule | verr loc "unexpected op"
  -- The types named so far.
  let mut env : List (String × Ty) := []
  for c in rule do
    let ty : TyE → Ty := fun
      | .ptr => .ptr
      | .addr => addr
      | .int w => .int w
      | .name n => match env.lookup n, k.imm n with
        | some t, _ => t
        | none, some (.ty t) => t
        | none, _ => .ptr
    match c with
    | .takeIns vs msg =>
      unless ins.length == vs.length do verr loc msg
      env := env ++ vs.zip ins
    | .takeOuts vs msg =>
      unless outs.length == vs.length do verr loc msg
      env := env ++ vs.zip outs
    | .ins label want => expectTys loc label ins (want.map ty)
    | .outs want => expectTys loc "results" outs (want.map ty)
    | .noOuts => unless outs.isEmpty do verr loc "this op has no results"
    | .same label got want => expectTys loc label (got.map ty) (want.map ty)
    | .ints ts =>
      let ts := ts.map ty
      unless ts.all Ty.isInt do verr loc s!"expected integers but got {tys ts}"
    | .pow2 f =>
      let some (.nat a) := k.imm f | verr loc "malformed op"
      unless isPow2 a do verr loc "alignment must be a power of two"
    | .fits f t =>
      let some (.int n) := k.imm f | verr loc "malformed op"
      let t := ty t
      unless fitsSigned t.width n || fitsUnsigned t.width n do verr loc s!"{n} does not fit in {t}"
    | .widens a t =>
      let (a, t) := (ty a, ty t)
      unless t.width > a.width do verr loc s!"cannot extend {a} to {t}"
    | .narrows a t =>
      let (a, t) := (ty a, ty t)
      unless t.width < a.width do verr loc s!"cannot truncate {a} to {t}"
    | .loadable t verb =>
      let t := ty t
      unless isLoadable st.space t do verr loc s!"{t} can't be {verb}: its size isn't whole bytes"
    | .deny names msg => if names.contains k.name then verr loc msg
    | .call f =>
      let some (.str callee) := k.imm f | verr loc "malformed op"
      let some (params, rets) := st.sigs[callee]? | verr loc s!"no function @{callee}"
      expectTys loc s!"arguments of @{callee}" ins params
      expectTys loc s!"results of @{callee}" outs rets

def nearestLoop : List RegionCtx → Option (List Ty × List Ty)
  | [] => none
  | .loopBody ps rs :: _ => some (ps, rs)
  | _ :: rest => nearestLoop rest

/-- The blocks of the nearest enclosing `cf.blocks`. -/
def nearestBlocks : List RegionCtx → Option (List (String × List Ty))
  | [] => none
  | .block bs _ :: _ => some bs
  | _ :: rest => nearestBlocks rest

/-- Check a branch to `s` with arguments of types `args`. -/
def checkSucc (loc : Option Loc) (bs : List (String × List Ty)) (s : Succ) (args : List Ty) :
    VM Unit := do
  let some ps := bs.lookup s.label | verr loc s!"no block ^{s.label} in the enclosing cf.blocks"
  expectTys loc s!"arguments of ^{s.label}" args ps

/-- A branch's operand types after its own, split among its targets in order. -/
def splitArgs : List Succ → List Ty → List (Succ × List Ty)
  | [], _ => []
  | s :: ss, ts => (s, ts.take s.nargs) :: splitArgs ss (ts.drop s.nargs)

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
      | .block .. :: _ => verr regionLoc "a block must end with a terminator"
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
      match ctx with
      | .ifBranch rs :: _ | .block _ rs :: _ => expectTys loc "cf.yield" ins rs
      | _ => verr loc "cf.yield must end a cf.if region or a block"
    | .brk, [] =>
      let some (_, rs) := nearestLoop ctx | verr loc "cf.break outside a loop"
      expectTys loc "cf.break" ins rs
    | .cont, [] =>
      let some (ps, _) := nearestLoop ctx | verr loc "cf.continue outside a loop"
      expectTys loc "cf.continue" ins ps
    | .ret, [] => expectTys loc "func.ret" ins (funcRets ctx)
    | .br dest, [] =>
      let some bs := nearestBlocks ctx | verr loc "cf.br outside cf.blocks"
      unless ins.length == dest.nargs do verr loc "malformed op"
      checkSucc loc bs dest ins
    | .condBr t f, [] =>
      let some bs := nearestBlocks ctx | verr loc "cf.cond_br outside cf.blocks"
      unless ins.length == 1 + t.nargs + f.nargs do verr loc "malformed op"
      expectTys loc "cf.cond_br condition" (ins.take 1) [.int 1]
      for (s, ts) in splitArgs [t, f] (ins.drop 1) do checkSucc loc bs s ts
    | .switch d cs, [] =>
      let some bs := nearestBlocks ctx | verr loc "cf.switch outside cf.blocks"
      let targets := d :: cs.map (·.2)
      unless ins.length == 1 + (targets.map (·.nargs)).sum do verr loc "malformed op"
      let t := ins.headD (.int 1)
      unless t.isInt do verr loc s!"cf.switch value: expected an integer but got {t}"
      let mut seen : List Int := []
      for (k, _) in cs do
        unless fitsSigned t.width k || fitsUnsigned t.width k do
          verr loc s!"{k} does not fit in {t}"
        if seen.contains (k % 2 ^ t.width) then verr loc s!"cf.switch has more than one case {k}"
        seen := (k % 2 ^ t.width) :: seen
      for (s, ts) in splitArgs targets (ins.drop 1) do checkSucc loc bs s ts
    | .blocks _, rs =>
      unless ins.isEmpty do verr loc "malformed op"
      let some entry := rs.head? | verr loc "cf.blocks needs at least one block"
      let mut bs : List (String × List Ty) := []
      for r in rs do
        let some l := r.label | verr loc "every block of cf.blocks needs a label"
        if (bs.lookup l).isSome then verr loc s!"block ^{l} is defined more than once"
        bs := bs ++ [(l, r.params.map (·.ty))]
      unless entry.params.isEmpty do verr loc "the entry block of cf.blocks has no parameters"
      for r in rs do
        let mut inner := scope
        for p in r.params do inner ← define loc inner p
        verifyOps (.block bs outs :: ctx) inner loc r.ops
    | .if_, [thn, els] =>
      expectTys loc "cf.if condition" ins [.int 1]
      for r in [thn, els] do
        unless r.params.isEmpty do verr loc "cf.if regions have no parameters"
        unless r.label.isNone do verr loc "only blocks of cf.blocks have labels"
        verifyOps (.ifBranch outs :: ctx) scope loc r.ops
    | .loop _, [body] =>
      unless body.label.isNone do verr loc "only blocks of cf.blocks have labels"
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
