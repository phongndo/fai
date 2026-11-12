import Std.Data.HashMap
import Std.Data.HashSet
import Fir.Syntax
import Fir.Layout

/-!
# Verifier

The rules a well-formed module must follow. A verified module never gets `stuck` in the
interpreter.

* Types: `iN` has `N ≥ 1`; `bN` has `N` a positive multiple of 8. Values (results, parameters,
  function results, holes) have the layer's value types (`Layer.valueTy`): `iN`, `ptr`, `bN`,
  `f32`, `f64`,
  and in HFIR also structs, arrays, unions, and slices. Struct fields and array elements have a
  layout (no function types, unions, or integers whose size isn't whole bytes); a union has at
  least one variant, each a value type; function types take value types; a struct's or array's
  size is below `2^addrBits`. Memory spaces have
  positive sizes that are multiples of 8, with the address size at most the pointer size, and
  power-of-two alignments for pointers and integers, the integers listed by increasing width.
* Globals: names are unique among globals and functions; the type has a layout; the alignment
  is a power of two; the initializer fits the type (`zero` anything, an integer an `iN` or `bN`
  it fits, `null` or `@name` a pointer, `bytes` exactly the type's size, `{…}` one item per
  field or element).
* SSA: every value is defined once per function, and used only where it is visible (after its
  definition, in the same region or a nested one). The blocks of `cf.blocks` are regions too: a
  value defined in a block is visible only in that block, and values from outside the
  `cf.blocks` in all of them; block arguments carry values from one block to another.
* Layers: every op is allowed in the module's layer (`Layer.allows`), checked before anything
  else about the op.
* Ops: operand counts and types match the op; constants and facts fit their type; alignments
  are powers of two; calls match the callee's signature.
* Control flow: a terminator is the last op of its region. `cf.yield` ends a `cf.if` or
  `cf.try` region or a block; `cf.break` and `cf.continue` appear inside a loop; loop bodies and blocks end with a
  terminator; a function body ends with `func.ret`.
* Blocks: `cf.blocks` has at least one block; every block has a label, unique in its
  `cf.blocks`, and no other region has one; the first block has no parameters. `cf.br`,
  `cf.cond_br`, and `cf.switch` appear inside `cf.blocks` (possibly inside `cf.if` and `cf.loop`
  regions there) and name blocks of the nearest one, with arguments of the blocks' parameter
  types. They can't leave a `cf.try` region.
* Exceptions: `cf.try`'s first region has no parameters and its catch region one, a `ptr`;
  `exn.throw` throws a `ptr`. `func.invoke`'s handler is a block of the nearest `cf.blocks` whose
  only parameter is a `ptr`, and `unwind` passes no arguments. A switch is on an integer, with keys that fit its type and differ modulo `2^N`.
* Target code (LFIR): a target's code op (`aarch64.code`) is a function's whole body. It has at
  least one block; every block has a label, unique in it, and no parameters, and ends with a
  terminator. The target's other ops appear directly in its blocks, its branches name blocks of
  it, and `func.ret` doesn't appear in it.
* Facts: ranges apply to integers, `nonnull` and `align` to pointers, and `noalias` and
  `readonly` only to pointer parameters of functions.
* Varargs: a variadic function, external function, or function type takes variadic arguments
  after its parameters, each an `iN` or `bN` of 8 to 64 bits in whole bytes, a `ptr`, or a float
  (`Ty.isVararg`), which is also what `va.arg` reads; `va.start` is only in a variadic function.
  `va_list` is a memory type: no value, parameter, or part of a value has it.
* Signatures: every function's parameter and result types are value types. This is checked
  for all functions before any body, so calls only ever compare value types.

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
  /-- A block of a target's code op (`aarch64.code`): the op's name and its blocks' labels. -/
  | code (name : String) (labels : List String)
  /-- A region of `cf.try`, with the op's results. Jumps can't leave it. -/
  | tryRegion (results : List Ty)

structure Hole where
  name : String
  ty : Ty
  loc : Option Loc

structure VState where
  defined : Std.HashSet String := {}
  holes : Array Hole := #[]
  space : SpaceCfg := {}
  layer : Layer := .hfir
  /-- Each function's parameter and return types, and whether it is variadic. -/
  sigs : Std.HashMap String (List Ty × List Ty × Bool) := {}
  globals : Std.HashSet String := {}
  /-- Whether the function being checked is variadic (`va.start` is allowed in it). -/
  variadic : Bool := false

abbrev VM := StateT VState (Except String)

def Loc.render : Option Loc → String
  | some l => s!"@{l.line}:{l.col}"
  | none => "@?"

def verr (loc : Option Loc) (msg : String) : VM α := throw s!"{Loc.render loc}: {msg}"

abbrev VScope := Std.HashMap String Ty

/-- Whether a type has a `va_list` in it, which values can't (decision: va_list). -/
partial def Ty.hasVaList : Ty → Bool
  | .vaList => true
  | .struct _ fs | .union fs => fs.any Ty.hasVaList
  | .array _ e => e.hasVaList
  | _ => false

/-- Check that a type is well formed: valid widths, parts with a layout, function types of
value types, and sizes that fit the address space. -/
partial def checkTy (loc : Option Loc) : Ty → VM Unit
  | .int 0 => verr loc "i0 is not a valid type"
  | .byte w => unless w > 0 && w % 8 == 0 do verr loc s!"b{w} is not a valid type"
  | .int _ | .ptr | .float _ | .vaList => pure ()
  | t@(.struct _ fs) => do
    for f in fs do
      checkTy loc f
      unless f.hasLayout do verr loc s!"{f} can't be part of {t}"
    checkSize t
  | t@(.array _ e) => do
    checkTy loc e
    unless e.hasLayout do verr loc s!"{e} can't be part of {t}"
    checkSize t
  | t@(.func ps rs _) => do
    let l := (← get).layer
    for x in ps ++ rs do
      checkTy loc x
      unless l.valueTy x && !x.hasVaList do verr loc s!"{x} can't be a parameter or result of {t}"
  | .slice => pure ()
  | t@(.union vs) => do
    if vs.isEmpty then verr loc s!"{t} needs at least one variant"
    for v in vs do
      checkTy loc v
      unless v.isHValue && !v.hasVaList do verr loc s!"{v} can't be a variant of {t}"
where
  checkSize (t : Ty) : VM Unit := do
    let sp := (← get).space
    unless t.size sp < 2 ^ sp.addrBits do verr loc s!"{t} is too large for the address space"

/-- Check that a value's type is a well-formed value type. -/
def checkValueTy (loc : Option Loc) (t : Ty) : VM Unit := do
  checkTy loc t
  unless (← get).layer.valueTy t && !t.hasVaList do verr loc s!"{t} is not a value type"

/-- Check that a type is well formed and has a layout. -/
def checkSized (loc : Option Loc) (t : Ty) : VM Unit := do
  checkTy loc t
  unless t.hasLayout do verr loc s!"{t} has no size in memory"

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
  checkValueTy loc r.ty
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
    checkValueTy loc t
    modify fun s => { s with holes := s.holes.push { name := n, ty := t, loc } }
    pure t

def tys (ts : List Ty) : String := s!"({", ".intercalate (ts.map toString)})"

def expectTys (loc : Option Loc) (what : String) (got want : List Ty) : VM Unit :=
  if got == want then pure ()
  else verr loc s!"{what}: expected {tys want} but got {tys got}"

def isLoadableScalar (space : SpaceCfg) : Ty → Bool
  | .int w => w % 8 == 0
  | .ptr => space.ptrBits % 8 == 0
  | .byte _ | .float _ => true
  | _ => false

/-- A scalar in whole bytes, or an aggregate with a layout whose leaves are. -/
def isLoadable (space : SpaceCfg) (t : Ty) : Bool :=
  if t.isValue then isLoadableScalar space t
  else t.hasLayout && (t.leaves space).all (isLoadableScalar space ·.2)

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
      | .slice => .slice
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
      unless st.layer.valueTy t do verr loc s!"{t} can't be {verb}: it is not a value type"
      unless t.isValue || t.hasLayout do verr loc s!"{t} can't be {verb}: it has no layout"
      unless isLoadable st.space t do verr loc s!"{t} can't be {verb}: its size isn't whole bytes"
    | .deny names msg => if names.contains k.name then verr loc msg
    | .call f =>
      let some (.str callee) := k.imm f | verr loc "malformed op"
      let some (params, rets, va) := st.sigs[callee]? | verr loc s!"no function @{callee}"
      checkArgs loc s!"arguments of @{callee}" ins params va
      expectTys loc s!"results of @{callee}" outs rets
    | .sized t => checkSized loc (ty t)
    | .field t f =>
      let t := ty t
      checkSized loc t
      let some (.nat i) := k.imm f | verr loc "malformed op"
      match t with
      | .struct _ fs => unless i < fs.length do verr loc s!"{t} has no field {i}"
      | _ => verr loc s!"{t} is not a struct"
    | .sig f =>
      let some (.ty t) := k.imm f | verr loc "malformed op"
      checkTy loc t
      let .func ps rs va := t | verr loc s!"{t} is not a function type"
      checkArgs loc "operands" ins (.ptr :: ps) va
      expectTys loc "results" outs rs
    | .global f =>
      let some (.str g) := k.imm f | verr loc "malformed op"
      unless st.globals.contains g do verr loc s!"no global @{g}"
    | .func f =>
      let some (.str g) := k.imm f | verr loc "malformed op"
      unless st.sigs.contains g do verr loc s!"no function @{g}"
    | .parts t =>
      match ty t with
      | .struct _ fs => expectTys loc "operands" ins fs
      | t@(.array n e) =>
        unless ins.length == n && ins.all (· == e) do
          verr loc s!"operands: expected {n} values of type {e} for {t} but got {tys ins}"
      | t => verr loc s!"{t} is not a struct or an array"
    | .part a f t =>
      let (a, t) := (ty a, ty t)
      let some (.nat i) := k.imm f | verr loc "malformed op"
      let part? := match a with
        | .struct _ fs => fs[i]?
        | .array n e => if i < n then some e else none
        | _ => none
      match a, part? with
      | .struct .., some p | .array .., some p => expectTys loc s!"part {i} of {a}" [t] [p]
      | .struct .., none | .array .., none => verr loc s!"{a} has no part {i}"
      | _, _ => verr loc s!"{a} is not a struct or an array"
    | .variant u f t =>
      let (u, t) := (ty u, ty t)
      let some (.nat i) := k.imm f | verr loc "malformed op"
      match u with
      | .union vs =>
        match vs[i]? with
        | some v => expectTys loc s!"variant {i} of {u}" [t] [v]
        | none => verr loc s!"{u} has no variant {i}"
      | _ => verr loc s!"{u} is not a union"
    | .isUnion u =>
      match ty u with
      | .union _ => pure ()
      | u => verr loc s!"{u} is not a union"
    | .scalar t =>
      let t := ty t
      unless t.isValue do verr loc s!"{t} is not a scalar type"
    | .floats ts =>
      let ts := ts.map ty
      unless ts.all Ty.isFloat do verr loc s!"expected floats but got {tys ts}"
    | .numeric ts =>
      let ts := ts.map ty
      unless ts.all (fun t => t.isInt || t.isFloat) do
        verr loc s!"expected integers or floats but got {tys ts}"
    | .sameWidth a t =>
      let (a, t) := (ty a, ty t)
      unless a.width == t.width do verr loc s!"{a} and {t} have different widths"
    | .floatBits f t =>
      let some (.nat n) := k.imm f | verr loc "malformed op"
      let t := ty t
      unless n < 2 ^ t.width do verr loc s!"{n} is not the bits of a {t}"
    | .vararg t =>
      let t := ty t
      unless t.isVararg do verr loc s!"{t} can't be a variadic argument"
where
  /-- A call's arguments against a signature's parameters: exactly them, or, for a variadic
  signature, them and then variadic arguments of the types `Ty.isVararg` allows. -/
  checkArgs (loc : Option Loc) (what : String) (ins params : List Ty) (va : Bool) : VM Unit := do
    if !va then expectTys loc what ins params
    else
      expectTys loc what (ins.take params.length) params
      for t in ins.drop params.length do
        unless t.isVararg do verr loc s!"{what}: {t} can't be a variadic argument"

def nearestLoop : List RegionCtx → Option (List Ty × List Ty)
  | [] => none
  | .loopBody ps rs :: _ => some (ps, rs)
  | _ :: rest => nearestLoop rest

/-- The blocks of the nearest enclosing `cf.blocks`, unless a `cf.try` region is nearer. -/
def nearestBlocks : List RegionCtx → Option (List (String × List Ty))
  | [] => none
  | .block bs _ :: _ => some bs
  | .tryRegion _ :: _ => none
  | _ :: rest => nearestBlocks rest

/-- Why a jump has no blocks to go to. -/
def noBlocks (what : String) : List RegionCtx → String
  | [] => s!"{what} outside cf.blocks"
  | .tryRegion _ :: _ => s!"{what} can't leave a cf.try region"
  | _ :: rest => noBlocks what rest

/-- Check a branch to `s` with arguments of types `args`. -/
def checkSucc (loc : Option Loc) (bs : List (String × List Ty)) (s : Succ) (args : List Ty) :
    VM Unit := do
  let some ps := bs.lookup s.label | verr loc s!"no block ^{s.label} in the enclosing cf.blocks"
  expectTys loc s!"arguments of ^{s.label}" args ps

/-- A branch's operand types after its own, split among its targets in order. -/
def splitArgs : List Succ → List Ty → List (Succ × List Ty)
  | [], _ => []
  | s :: ss, ts => (s, ts.take s.nargs) :: splitArgs ss (ts.drop s.nargs)

/-- The nearest enclosing target code op's name and labels. -/
def nearestCode : List RegionCtx → Option (String × List String)
  | [] => none
  | .code n ls :: _ => some (n, ls)
  | _ :: rest => nearestCode rest

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
      | .tryRegion [] :: _ => pure ()
      | .tryRegion _ :: _ => verr regionLoc "this cf.try region must end with cf.yield"
      | .loopBody .. :: _ => verr regionLoc "a loop body must end with cf.break or cf.continue"
      | .block .. :: _ | .code .. :: _ => verr regionLoc "a block must end with a terminator"
      | _ => verr regionLoc "the function body must end with func.ret"
    | op :: rest => do
      let scope ← verifyOp ctx scope op
      if op.kind.isTerminator && !rest.isEmpty then
        verr op.loc "a terminator must be the last op of its region"
      if op.kind.isTerminator then pure () else verifyOps ctx scope regionLoc rest

  partial def verifyOp (ctx : List RegionCtx) (scope : VScope) (op : Op) : VM VScope := do
    let loc := op.loc
    let layer := (← get).layer
    unless layer.allows op.kind.decl do
      verr loc s!"{op.kind.name} is not allowed in layer {layer.render}; it is allowed in {op.kind.decl.layersText}"
    let ins ← op.args.mapM (operandTy loc scope)
    let outs := op.results.map (·.ty)
    match op.kind, op.regions with
    | .yield, [] =>
      match ctx with
      | .ifBranch rs :: _ | .block _ rs :: _ | .tryRegion rs :: _ => expectTys loc "cf.yield" ins rs
      | _ => verr loc "cf.yield must end a cf.if or cf.try region or a block"
    | .brk, [] =>
      let some (_, rs) := nearestLoop ctx | verr loc "cf.break outside a loop"
      expectTys loc "cf.break" ins rs
    | .cont, [] =>
      let some (ps, _) := nearestLoop ctx | verr loc "cf.continue outside a loop"
      expectTys loc "cf.continue" ins ps
    | .ret, [] =>
      if let some (name, _) := nearestCode ctx then verr loc s!"func.ret can't be inside {name}"
      expectTys loc "func.ret" ins (funcRets ctx)
    | .br dest, [] =>
      let some bs := nearestBlocks ctx | verr loc (noBlocks "cf.br" ctx)
      unless ins.length == dest.nargs do verr loc "malformed op"
      checkSucc loc bs dest ins
    | .condBr t f, [] =>
      let some bs := nearestBlocks ctx | verr loc (noBlocks "cf.cond_br" ctx)
      unless ins.length == 1 + t.nargs + f.nargs do verr loc "malformed op"
      expectTys loc "cf.cond_br condition" (ins.take 1) [.int 1]
      for (s, ts) in splitArgs [t, f] (ins.drop 1) do checkSucc loc bs s ts
    | .switch d cs, [] =>
      let some bs := nearestBlocks ctx | verr loc (noBlocks "cf.switch" ctx)
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
    | .try_, [body, handler] =>
      unless ins.isEmpty do verr loc "malformed op"
      unless body.params.isEmpty do verr loc "the first region of cf.try has no parameters"
      unless body.label.isNone && handler.label.isNone do
        verr loc "only blocks of cf.blocks have labels"
      verifyOps (.tryRegion outs :: ctx) scope loc body.ops
      unless (handler.params.map (·.ty)) == [.ptr] do
        verr loc "the catch region of cf.try takes one parameter, the exception, a ptr"
      let mut inner := scope
      for r in handler.params do inner ← define loc inner r
      verifyOps (.tryRegion outs :: ctx) inner loc handler.ops
    | .throw_, [] =>
      expectTys loc "exn.throw" ins [.ptr]
      unless outs.isEmpty do verr loc "exn.throw has no results"
    | k@(.invoke _ s), [] | k@(.invokeIndirect _ s), [] =>
      unless s.nargs == 0 do verr loc "a handler takes the exception only; unwind passes no arguments"
      checkSimple loc k ins outs
      let some bs := nearestBlocks ctx | verr loc s!"{k.name} names a handler outside cf.blocks"
      let some ps := bs.lookup s.label | verr loc s!"no block ^{s.label} in the enclosing cf.blocks"
      expectTys loc s!"parameters of handler ^{s.label}" ps [.ptr]
    | .loop _, [body] =>
      unless body.label.isNone do verr loc "only blocks of cf.blocks have labels"
      let ps := body.params.map (·.ty)
      expectTys loc "cf.loop initial values" ins ps
      let mut inner := scope
      for r in body.params do inner ← define loc inner r
      verifyOps (.loopBody ps outs :: ctx) inner loc body.ops
    | .vaStart, [] =>
      unless (← get).variadic do verr loc "va.start is only allowed in a variadic function"
      checkSimple loc .vaStart ins outs
    | k, [] =>
      if k.isTerminator && k.decl.rule.isSome then
        -- A target's branch, return, or trap: it ends a block of the target's code.
        let some (name, labels) := nearestCode ctx | verr loc s!"{k.name} must be inside a block of a target's code"
        checkSimple loc k ins outs
        for f in k.decl.imms do
          if let some (.succ s) := k.imm f.name then
            unless labels.contains s.label do verr loc s!"no block ^{s.label} in the enclosing {name}"
      else
        if k.isTerminator || k matches .if_ || k matches .loop _ || k matches .try_ then
          verr loc "malformed op"
        if targets.contains k.decl.dialect && !(ctx.head? matches some (.code ..)) then
          verr loc s!"{k.name} must be inside a block of a target's code"
        checkSimple loc k ins outs
    | k, rs =>
      -- A target's code op: labeled blocks without parameters, as a function's whole body.
      unless k.decl.hasBlocks && ins.isEmpty && outs.isEmpty do verr loc "malformed op"
      unless ctx matches [.func _] do verr loc s!"{k.name} must be a function's whole body"
      let mut labels : List String := []
      for r in rs do
        let some l := r.label | verr loc s!"every block of {k.name} needs a label"
        if labels.contains l then verr loc s!"block ^{l} is defined more than once"
        unless r.params.isEmpty do verr loc s!"blocks of {k.name} have no parameters"
        labels := labels ++ [l]
      for r in rs do verifyOps (.code k.name labels :: ctx) scope loc r.ops
    let mut scope := scope
    for r in op.results do scope ← define loc scope r
    pure scope
end

def verifyFunc (f : Func) : VM Unit := do
  modify fun s => { s with defined := {}, variadic := f.variadic }
  for t in f.rets do checkValueTy none t
  let mut scope : VScope := {}
  for r in f.params do scope ← define none scope r (isParam := true)
  verifyOps [.func f.rets] scope none f.body.ops

def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- Check a global's initializer against its type. -/
partial def checkInit (g : String) (syms : Std.HashSet String) (sp : SpaceCfg) :
    Ty → Init → Except String Unit
  | _, .zero => pure ()
  | t, .int n =>
    match t with
    | .int w | .byte w =>
      unless fitsSigned w n || fitsUnsigned w n do throw s!"global @{g}: {n} does not fit in {t}"
    | _ => throw s!"global @{g}: an integer can't initialize {t}"
  | t, .float f b => do
    unless t == Ty.float f do throw s!"global @{g}: an {f.name} can't initialize {t}"
    unless b < 2 ^ f.width do throw s!"global @{g}: {b} is not the bits of an {f.name}"
  | .ptr, .null => pure ()
  | t, .null => throw s!"global @{g}: null can't initialize {t}"
  | .ptr, .sym s => unless syms.contains s do throw s!"global @{g}: no global or function @{s}"
  | t, .sym s => throw s!"global @{g}: @{s} can't initialize {t}"
  | t, .bytes bs =>
    unless bs.length == t.size sp do
      throw s!"global @{g}: {bs.length} bytes can't initialize {t}, which takes {t.size sp}"
  | t@(.struct _ fs), .list items => do
    unless items.length == fs.length do
      throw s!"global @{g}: {t} takes {fs.length} initializers but got {items.length}"
    for (f, i) in fs.zip items do checkInit g syms sp f i
  | t@(.array n e), .list items => do
    unless items.length == n do
      throw s!"global @{g}: {t} takes {n} initializers but got {items.length}"
    for i in items do checkInit g syms sp e i
  | t, .list _ => throw s!"global @{g}: a list can't initialize {t}"

/-- Verify a module. On success, returns the holes it contains. -/
def verifyModule (m : Module) : Except String (Array Hole) := do
  let sp := m.space
  unless sp.ptrBits > 0 && sp.ptrBits % 8 == 0 && sp.addrBits > 0 && sp.addrBits % 8 == 0 &&
      sp.addrBits ≤ sp.ptrBits do
    throw s!"memspace: pointer size {sp.ptrBits} and address size {sp.addrBits} must be positive multiples of 8, with the address size at most the pointer size"
  unless isPow2 sp.ptrAlign do throw s!"memspace: pointer alignment {sp.ptrAlign} must be a power of two"
  unless sp.vaSize > 0 && isPow2 sp.vaAlign do
    throw s!"memspace: va_list size {sp.vaSize} must be positive and its alignment {sp.vaAlign} a power of two"
  let mut last := 0
  for (w, a) in sp.ints do
    unless w > last do throw "memspace: integer alignments must be listed by increasing width"
    unless isPow2 a do throw s!"memspace: alignment {a} of i{w} must be a power of two"
    last := w
  -- Names.
  let mut names : Std.HashSet String := {}
  for g in m.globals do
    if names.contains g.name then throw s!"global @{g.name} is defined more than once"
    names := names.insert g.name
  let globals := names
  let mut sigs : Std.HashMap String (List Ty × List Ty × Bool) := {}
  for x in m.externs do
    if names.contains x.name then throw s!"function @{x.name} is defined more than once"
    names := names.insert x.name
    sigs := sigs.insert x.name (x.params, x.rets, x.variadic)
  for f in m.funcs do
    if names.contains f.name then throw s!"function @{f.name} is defined more than once"
    names := names.insert f.name
    sigs := sigs.insert f.name (f.params.map (·.ty), f.rets, f.variadic)
  -- Globals.
  let st : VState := { space := sp, layer := m.layer, sigs, globals }
  for g in m.globals do
    let r := (do
      checkSized none g.ty
      unless isPow2 g.align do verr none "alignment must be a power of two").run st
    if let .error e := r then throw s!"global @{g.name}: {(e.dropPrefix? "@?: ").map (·.toString) |>.getD e}"
    checkInit g.name names sp g.ty g.init
  -- External functions.
  for x in m.externs do
    for t in x.params ++ x.rets do
      unless t.isValue do throw s!"extern @{x.name}: {t} is not a value type"
    let mut seen : List ExtEffect := []
    for e in x.effects do
      if seen.contains e then throw s!"extern @{x.name}: {e.render} is listed twice"
      if e == .unwind then
        throw s!"extern @{x.name}: unwinding out of an external function is not supported yet"
      seen := seen ++ [e]
    if x.trust == .proved then
      throw s!"extern @{x.name}: the effects of an external function can be assumed or checked, not proved"
  -- Signatures, then bodies.
  for f in m.funcs do
    for t in f.params.map (·.ty) ++ f.rets do
      unless m.layer.valueTy t do throw s!"in @{f.name}: @?: {t} is not a value type"
  let (_, st) ← (m.funcs.forM fun f =>
    tryCatch (verifyFunc f) fun e => throw s!"in @{f.name}: {e}").run st
  pure st.holes

end Fir
