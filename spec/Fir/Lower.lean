import Fir.Interp
import Fir.Verify
import Fir.LowerBits

/-!
# Lowering HFIR to MFIR

`lowerModule` turns an HFIR module into an MFIR one: the building blocks become core ops, and
`ptr.field` and `ptr.index` become `ptr.offset` by computed offsets (decisions: Layers, Layout,
HFIR lowering). It runs three passes over each function.

**Scalarizing** (`scalarize`) replaces every aggregate, union, and slice value by its scalars
(`scalars`): a value `%s` of type `struct<C>{i32, ptr}` becomes `%s.0: i32` and `%s.1: ptr`. A
union becomes its `i32` tag and the scalars of every variant, in order; the variants it doesn't
hold are `poison`. A slice becomes its pointer and its length. Scalar values keep their names.
Function parameters and results, region parameters, op results, and the operands of branches,
`cf.yield`, `cf.break`, `cf.continue`, `func.ret`, and calls are replaced by their scalars too, so
the calling convention passes an aggregate as its scalars. The building-block ops become:

* `agg.make`, `agg.extract`, `agg.insert`, `copy`, `union.make`, `union.tag`, `slice.make`,
  `slice.ptr`, `slice.len`: copies of scalars (and `int.const` for a union's tag, `poison` for
  the variants a union doesn't hold);
* `union.get.trap`: a comparison of the tag and `cf.check.tag`, then copies; `union.get.ub`:
  copies only, since the wrong variant is UB;
* `slice.get` and `slice.set`: `int.cmp.ult` of the index and the length and `cf.check.bounds`
  (for `.trap` only; out of bounds is UB for `.ub`), then the element's address as
  `ptr.offset.inbounds` by the index times the stride (`int.mul.wrap`), then the access;
* an aggregate `mem.load` or `mem.store`: one scalar access per leaf (`Ty.leaves`), at
  `ptr.offset.wrap` by the leaf's offset (none for offset 0), with the alignment the offset keeps
  (`Nat.gcd`), as the interpreter defines aggregate accesses.

**Lowering exceptions** (`lowerExn`, decision: Exceptions in MFIR) replaces `cf.try` by a
`cf.blocks` whose entry block is its first region and whose second block (`^.x1`, …) is its
handler; inside, `exn.throw` becomes a `cf.br` to the handler and a call that may throw (to a
function of the module, or through a pointer) a `func.invoke` naming it. A `cf.blocks` between a
throw and its handler, which can't be jumped out of, gets a block that leaves it by `cf.yield`
with two more results, `1` and the exception (its other yields give `0` and `poison`), and a
`cf.if` after it jumps on. Outside `cf.try`, throws and calls stay as they are and unwind to the
caller. Its labels and temporaries are `.x0`, `.x1`, ….

**Expanding** (`expand`) replaces the remaining HFIR-only ops, which take and give scalars:

* `int.add.overflow.s %a, %b` (and `sub`, `mul`, `.u`): extend both operands to a width where the
  operation is exact (one more bit, or twice the bits for `mul`; `sext` for `.s`, `zext` for
  `.u`), compute with `.wrap`, truncate to the result, and compare the exact result with the
  result extended back: they differ exactly when the operation overflows;
* `ptr.field %p, i`: `ptr.offset` by `int.const` of the field's offset;
* `ptr.index.inbounds %p, %i`: the index times the stride computed exactly at twice the address
  size, `int.trunc.nsw` back (`poison` if it doesn't fit, as `ptr.index.inbounds` requires), and
  `ptr.offset.inbounds`; `ptr.index.wrap`: `int.mul.wrap` and `ptr.offset.wrap`.

Expanding fails on what it can't lower exactly: a field offset that isn't a positive signed
address-sized integer, and an in-bounds index whose stride doesn't fit the address size (only
huge types or alignments do either).

New values that no HFIR value becomes are temporaries, numbered per function and pass: `%.s0`,
`%.s1`, … while scalarizing, `%.x0`, … while lowering exceptions, and `%.e0`, … while expanding. Lowering expects a verified module
(each name defined once); the result is checked by the verifier, so a name clash with a
scalar's or temporary's name is reported rather than miscompiled.
-/

namespace Fir.Lower

/-! ## Scalars -/

mutual
  /-- The scalar types an HFIR value of type `t` becomes, in order: a struct's or array's parts'
  scalars, a slice's pointer and `iA` length, a union's `i32` tag and then every variant's
  scalars; a scalar type is itself. -/
  def scalars (aw : Nat) : Ty → List Ty
    | .struct _ fs => scalarsList aw fs
    | .array n e => let s := scalars aw e; (List.range n).flatMap fun _ => s
    | .slice => [.ptr, .int aw]
    | .union vs => .int 32 :: scalarsList aw vs
    | t => [t]
  def scalarsList (aw : Nat) : List Ty → List Ty
    | [] => []
    | t :: ts => scalars aw t ++ scalarsList aw ts
end

/-- Where part `i` of a struct or array type starts among its scalars, and how many it has. -/
def partRange (aw : Nat) : Ty → Nat → Nat × Nat
  | .struct _ fs, i => ((scalarsList aw (fs.take i)).length, (scalars aw (fs.getD i .ptr)).length)
  | .array _ e, i => let k := (scalars aw e).length; (i * k, k)
  | _, _ => (0, 0)

/-- Where variant `i` of a union type starts among its scalars (after the tag), and how many it
has. -/
def variantRange (aw : Nat) : Ty → Nat → Nat × Nat
  | .union vs, i => (1 + (scalarsList aw (vs.take i)).length, (scalars aw (vs.getD i .ptr)).length)
  | _, _ => (0, 0)

/-- The names and types of the scalars a value `%n: t` becomes: `%n` itself for a scalar type,
otherwise `%n.0`, `%n.1`, …. -/
def leafNames (aw : Nat) (n : String) (t : Ty) : List (String × Ty) :=
  if t.isValue then [(n, t)] else (scalars aw t).zipIdx.map fun (s, i) => (s!"{n}.{i}", s)

/-- The results a result becomes. Facts stay on scalars, the only types they apply to. -/
def explodeResult (aw : Nat) (r : Result) : List Result :=
  if r.ty.isValue then [r] else (leafNames aw r.name r.ty).map fun (n, t) => { name := n, ty := t }

/-- The `poison` value of a scalar type. -/
def poisonOf : Ty → RVal
  | .ptr => .ptr none
  | .byte w => .bytes (List.replicate (w / 8) .poison)
  | t => .int t.width .poison

mutual
  /-- The scalars an HFIR value of type `t` is represented by after lowering: its leaves, and for a
  union `poison` for the variants it doesn't hold. -/
  def lowerValue (aw : Nat) : Ty → RVal → List RVal
    | .struct _ fs, .agg xs => lowerValues aw fs xs
    | .array _ e, .agg xs => lowerAll aw e xs
    | .union vs, .agg [tag@(.int 32 (.bits t)), v] => tag :: lowerVariants aw t.toNat 0 v vs
    | _, v => RVal.leaves v
  def lowerValues (aw : Nat) : List Ty → List RVal → List RVal
    | t :: ts, x :: xs => lowerValue aw t x ++ lowerValues aw ts xs
    | _, _ => []
  def lowerAll (aw : Nat) (t : Ty) : List RVal → List RVal
    | [] => []
    | x :: xs => lowerValue aw t x ++ lowerAll aw t xs
  def lowerVariants (aw : Nat) (tag j : Nat) (v : RVal) : List Ty → List RVal
    | [] => []
    | t :: ts =>
      (if tag = j then lowerValue aw t v else (scalars aw t).map poisonOf) ++
        lowerVariants aw tag (j + 1) v ts
end

/-- A function type with each parameter and result replaced by its scalars. -/
def flatSig (aw : Nat) : Ty → Ty
  | .func ps rs => .func (scalarsList aw ps) (scalarsList aw rs)
  | t => t

/-! ## Types of values -/

mutual
  /-- Every value an op list defines, with its type: results and region parameters. -/
  def typesOps : List Op → List (String × Ty)
    | [] => []
    | .mk _ rs _ regs _ :: os => rs.map (fun r => (r.name, r.ty)) ++ typesRegions regs ++ typesOps os
  def typesRegions : List Region → List (String × Ty)
    | [] => []
    | .mk ps ops _ :: rs => ps.map (fun r => (r.name, r.ty)) ++ typesOps ops ++ typesRegions rs
end

/-- What scalarizing reads: the memory space and each value's type. -/
structure Ctx where
  sp : SpaceCfg
  types : Std.HashMap String Ty

def Ctx.aw (cx : Ctx) : Nat := cx.sp.addrBits

def Ctx.tyOf (cx : Ctx) : Operand → Ty
  | .var n => cx.types.getD n .ptr
  | .hole _ t => t

/-- The operands an operand becomes. A hole of an aggregate type becomes holes of the same name,
one per scalar, so a run reaches the same hole. -/
def Ctx.explode (cx : Ctx) : Operand → List Operand
  | .var n => match cx.types[n]? with
    | some t => if t.isValue then [.var n] else (leafNames cx.aw n t).map (.var ·.1)
    | none => [.var n]
  | .hole n t => if t.isValue then [.hole n t] else (scalars cx.aw t).map (.hole n)

def Ctx.explodeAll (cx : Ctx) (as : List Operand) : List Operand := as.flatMap cx.explode

/-- Lowering numbers its temporaries, and fails on what it can't lower. -/
abbrev M := StateT Nat (Except String)

/-- Temporary `k` of a pass with prefix `pre`: `%.s0`, `%.e3`, …. -/
def tempName (pre : String) (k : Nat) : String := "." ++ pre ++ toString k

/-- A new temporary. -/
def fresh (pre : String) : M String := do
  let k ← get
  set (k + 1)
  pure (tempName pre k)

def res (n : String) (t : Ty) : Result := { name := n, ty := t }

def copies (rs : List Result) (as : List Operand) (loc : Option Loc) : List Op :=
  (rs.zip as).map fun (r, a) => .mk .copy [r] [a] [] loc

/-! ## Scalarizing -/

/-- A branch's operands, its own then each target's arguments, replaced by their scalars, with
the targets' argument counts to match. -/
def fixSuccs (cx : Ctx) (k : OpKind) (args : List Operand) : OpKind × List Operand :=
  match k, args with
  | .br d, _ => let a := cx.explodeAll args; (.br { d with nargs := a.length }, a)
  | .condBr t f, c :: rest =>
    let ta := cx.explodeAll (rest.take t.nargs)
    let fa := cx.explodeAll (rest.drop t.nargs)
    (.condBr { t with nargs := ta.length } { f with nargs := fa.length }, c :: ta ++ fa)
  | .switch d cs, v :: rest =>
    let da := cx.explodeAll (rest.take d.nargs)
    let (cs', ca, _) := cs.foldl (init := ([], [], rest.drop d.nargs))
      fun (acc, out, rest) (key, s) =>
        let a := cx.explodeAll (rest.take s.nargs)
        (acc ++ [(key, { s with nargs := a.length })], out ++ a, rest.drop s.nargs)
    (.switch { d with nargs := da.length } cs', v :: da ++ ca)
  | .callIndirect sig, _ => (.callIndirect (flatSig cx.aw sig), cx.explodeAll args)
  | _, _ => (k, cx.explodeAll args)

/-- The address of the leaf at offset `off` of an aggregate at `p`, and the ops computing it. -/
def leafAddr (cx : Ctx) (p : Operand) (off : Nat) (loc : Option Loc) : M (List Op × Operand) :=
  if off = 0 then pure ([], p) else do
    let c ← fresh "s"
    let q ← fresh "s"
    pure ([.mk (.const off) [res c (.int cx.aw)] [] [] loc,
      .mk (.ptrOffset false) [res q .ptr] [p, .var c] [] loc], .var q)

/-- Load each leaf of `r`'s type from `p` into `r`'s scalars. -/
def loadLeaves (cx : Ctx) (A : Nat) (p : Operand) (loc : Option Loc) :
    List (Nat × Ty) → List Result → M (List Op)
  | (off, _) :: ls, r :: rs => do
    let (pre, q) ← leafAddr cx p off loc
    let rest ← loadLeaves cx A p loc ls rs
    pure (pre ++ [.mk (.load (Nat.gcd A off)) [r] [q] [] loc] ++ rest)
  | _, _ => pure []

/-- Store scalars `vs` at the leaves of type `T` at `p`. -/
def storeLeaves (cx : Ctx) (A : Nat) (p : Operand) (loc : Option Loc) :
    List (Nat × Ty) → List Operand → M (List Op)
  | (off, t) :: ls, v :: vs => do
    let (pre, q) ← leafAddr cx p off loc
    let rest ← storeLeaves cx A p loc ls vs
    pure (pre ++ [.mk (.store t (Nat.gcd A off)) [] [v, q] [] loc] ++ rest)
  | _, _ => pure []

/-- A load of `r` from `p`: one op for a scalar, one per leaf for an aggregate. -/
def loadTo (cx : Ctx) (r : Result) (A : Nat) (p : Operand) (loc : Option Loc) : M (List Op) :=
  if r.ty.isValue then pure [.mk (.load A) [r] [p] [] loc]
  else loadLeaves cx A p loc (r.ty.leaves cx.sp) (explodeResult cx.aw r)

/-- A store of a `T` from scalars `vs` to `p`. -/
def storeFrom (cx : Ctx) (T : Ty) (A : Nat) (vs : List Operand) (p : Operand) (loc : Option Loc) :
    M (List Op) :=
  if T.isValue then pure [.mk (.store T A) [] (vs ++ [p]) [] loc]
  else storeLeaves cx A p loc (T.leaves cx.sp) vs

/-- The address of element `i` of the slice with pointer `p` and length `n`, checked against the
length if `trap`, and the ops computing it. -/
def elemAddr (cx : Ctx) (trap : Bool) (T : Ty) (p n i : Operand) (loc : Option Loc) :
    M (List Op × Operand) := do
  let checks ← if trap then do
      let ok ← fresh "s"
      pure [.mk (.cmp .ult) [res ok (.int 1)] [i, n] [] loc, .mk (.check .bounds) [] [.var ok] [] loc]
    else pure []
  let st ← fresh "s"
  let off ← fresh "s"
  let q ← fresh "s"
  pure (checks ++ [.mk (.const (T.stride cx.sp)) [res st (.int cx.aw)] [] [] loc,
    .mk (.arith .mul .wrap) [res off (.int cx.aw)] [i, .var st] [] loc,
    .mk (.ptrOffset true) [res q .ptr] [p, .var off] [] loc], .var q)

/-- A flat op, with its results and operands replaced by their scalars. -/
def scalarizeFlat (cx : Ctx) (k : OpKind) (rs : List Result) (args : List Operand)
    (loc : Option Loc) : M (List Op) := do
  let aw := cx.aw
  let rs' := rs.flatMap (explodeResult aw)
  let keep : M (List Op) := do
    let (k', args') := fixSuccs cx k args
    pure [.mk k' rs' args' [] loc]
  match k, rs, args with
  | .aggMake, [_], _ => pure (copies rs' (cx.explodeAll args) loc)
  | .aggExtract i, [_], [a] =>
    let (start, n) := partRange aw (cx.tyOf a) i
    pure (copies rs' (((cx.explode a).drop start).take n) loc)
  | .aggInsert i, [_], [a, v] =>
    let (start, n) := partRange aw (cx.tyOf a) i
    let la := cx.explode a
    pure (copies rs' (la.take start ++ cx.explode v ++ la.drop (start + n)) loc)
  | .copy, [_], _ => pure (copies rs' (cx.explodeAll args) loc)
  | .unionMake i, [r], [v] =>
    let (start, n) := variantRange aw r.ty i
    let lv := cx.explode v
    pure <| rs'.zipIdx.map fun (rr, j) =>
      if j = 0 then .mk (.const i) [rr] [] [] loc
      else if start ≤ j && j < start + n then .mk .copy [rr] [lv.getD (j - start) v] [] loc
      else .mk .poison [rr] [] [] loc
  | .unionTag, [_], [u] => pure (copies rs' ((cx.explode u).take 1) loc)
  | .unionGet trap i, [_], [u] =>
    let lu := cx.explode u
    let (start, n) := variantRange aw (cx.tyOf u) i
    let checks ← if trap then do
        let c ← fresh "s"
        let ok ← fresh "s"
        pure [.mk (.const i) [res c (.int 32)] [] [] loc,
          .mk (.cmp .eq) [res ok (.int 1)] [lu.headD u, .var c] [] loc,
          .mk (.check .tag) [] [.var ok] [] loc]
      else pure []
    pure (checks ++ copies rs' ((lu.drop start).take n) loc)
  | .sliceMake, [_], _ => pure (copies rs' (cx.explodeAll args) loc)
  | .slicePtr, [_], [s] => pure (copies rs' ((cx.explode s).take 1) loc)
  | .sliceLen, [_], [s] => pure (copies rs' ((cx.explode s).drop 1) loc)
  | .sliceGet trap A, [r], [s, i] =>
    let ls := cx.explode s
    let (pre, q) ← elemAddr cx trap r.ty (ls.getD 0 s) (ls.getD 1 s) i loc
    pure (pre ++ (← loadTo cx r A q loc))
  | .sliceSet trap T A, [], [v, s, i] =>
    let ls := cx.explode s
    let (pre, q) ← elemAddr cx trap T (ls.getD 0 s) (ls.getD 1 s) i loc
    pure (pre ++ (← storeFrom cx T A (cx.explode v) q loc))
  | .load A, [r], [p] => loadTo cx r A p loc
  | .store T A, [], [v, p] => storeFrom cx T A (cx.explode v) p loc
  | _, _, _ => keep

mutual
  /-- Scalarize an op, and the ops in its regions. -/
  def scalarizeOp (cx : Ctx) : Op → M (List Op)
    | .mk k rs args [] loc => scalarizeFlat cx k rs args loc
    | .mk k rs args regs@(_ :: _) loc => do
      let regs' ← scalarizeRegions cx regs
      pure [.mk k (rs.flatMap (explodeResult cx.aw)) (cx.explodeAll args) regs' loc]
  def scalarizeOps (cx : Ctx) : List Op → M (List Op)
    | [] => pure []
    | o :: os => do
      let a ← scalarizeOp cx o
      let b ← scalarizeOps cx os
      pure (a ++ b)
  def scalarizeRegions (cx : Ctx) : List Region → M (List Region)
    | [] => pure []
    | .mk ps ops lbl :: rs => do
      let ops' ← scalarizeOps cx ops
      let rs' ← scalarizeRegions cx rs
      pure (.mk (ps.flatMap (explodeResult cx.aw)) ops' lbl :: rs')
end

/-- The context for scalarizing a function: the type of each value it defines. -/
def Ctx.ofFunc (sp : SpaceCfg) (f : Func) : Ctx :=
  { sp, types := (f.params.map (fun r => (r.name, r.ty)) ++ typesOps f.body.ops).foldl
      (fun m (n, t) => m.insert n t) {} }

/-- Replace a function's aggregate, union, and slice values by their scalars. -/
def scalarize (sp : SpaceCfg) (f : Func) : Except String Func := do
  let cx := Ctx.ofFunc sp f
  let (ops, _) ← (scalarizeOps cx f.body.ops).run 0
  pure { f with
    rets := scalarsList sp.addrBits f.rets
    body := .mk (f.params.flatMap (explodeResult sp.addrBits)) ops f.body.label }

/-! ## Expanding -/

/-- `sext` or `zext`. -/
def extOp (signed : Bool) : OpKind := if signed then .sext else .zext

/-- An op that takes and gives scalars, as core ops. -/
def expandFlat (sp : SpaceCfg) (o : Op) : M (List Op) := do
  let aw := sp.addrBits
  match o with
  | .mk (.overflow op signed) [r, ov] [a, b] [] loc =>
    let w := r.ty.width
    let W := LowerBits.wide op w
    let t0 ← fresh "e"
    let t1 ← fresh "e"
    let t2 ← fresh "e"
    let t3 ← fresh "e"
    pure [.mk (extOp signed) [res t0 (.int W)] [a] [] loc,
      .mk (extOp signed) [res t1 (.int W)] [b] [] loc,
      .mk (.arith op .wrap) [res t2 (.int W)] [.var t0, .var t1] [] loc,
      .mk (.trunc .wrap) [r] [.var t2] [] loc,
      .mk (extOp signed) [res t3 (.int W)] [.var r.name] [] loc,
      .mk (.cmp .ne) [ov] [.var t2, .var t3] [] loc]
  | .mk (.ptrField inb T i) [r] [p] [] loc =>
    let off := (T.fieldOffset? sp i).getD 0
    unless off < 2 ^ (aw - 1) do
      throw s!"{Loc.render loc}: cannot lower: field {i} of {T} is at offset {off}, which doesn't fit a signed i{aw}"
    let c ← fresh "e"
    pure [.mk (.const off) [res c (.int aw)] [] [] loc, .mk (.ptrOffset inb) [r] [p, .var c] [] loc]
  | .mk (.ptrIndex true T) [r] [p, i] [] loc =>
    unless T.stride sp < 2 ^ aw do
      throw s!"{Loc.render loc}: cannot lower: the stride of {T}, {T.stride sp}, doesn't fit an i{aw}"
    let t0 ← fresh "e"
    let t1 ← fresh "e"
    let t2 ← fresh "e"
    let t3 ← fresh "e"
    pure [.mk .sext [res t0 (.int (2 * aw))] [i] [] loc,
      .mk (.const (T.stride sp)) [res t1 (.int (2 * aw))] [] [] loc,
      .mk (.arith .mul .wrap) [res t2 (.int (2 * aw))] [.var t0, .var t1] [] loc,
      .mk (.trunc .nsw) [res t3 (.int aw)] [.var t2] [] loc,
      .mk (.ptrOffset true) [r] [p, .var t3] [] loc]
  | .mk (.ptrIndex false T) [r] [p, i] [] loc =>
    let t0 ← fresh "e"
    let t1 ← fresh "e"
    pure [.mk (.const (T.stride sp)) [res t0 (.int aw)] [] [] loc,
      .mk (.arith .mul .wrap) [res t1 (.int aw)] [i, .var t0] [] loc,
      .mk (.ptrOffset false) [r] [p, .var t1] [] loc]
  | o => pure [o]

mutual
  /-- Expand an op, and the ops in its regions. -/
  def expandOp (sp : SpaceCfg) : Op → M (List Op)
    | o@(.mk _ _ _ [] _) => expandFlat sp o
    | .mk k rs args regs@(_ :: _) loc => do
      let regs' ← expandRegions sp regs
      pure [.mk k rs args regs' loc]
  def expandOps (sp : SpaceCfg) : List Op → M (List Op)
    | [] => pure []
    | o :: os => do
      let a ← expandOp sp o
      let b ← expandOps sp os
      pure (a ++ b)
  def expandRegions (sp : SpaceCfg) : List Region → M (List Region)
    | [] => pure []
    | .mk ps ops lbl :: rs => do
      let ops' ← expandOps sp ops
      let rs' ← expandRegions sp rs
      pure (.mk ps ops' lbl :: rs')
end

/-- Replace a function's checked arithmetic, `ptr.field`, and `ptr.index` by core ops. -/
def expand (sp : SpaceCfg) (f : Func) : Except String Func := do
  let (ops, _) ← (expandOps sp f.body.ops).run 0
  pure { f with body := .mk f.body.params ops f.body.label }

/-! ## Exceptions -/

/-- Whether an op kind may throw: `exn.throw`, a call that may reach a function of the module
(a direct call to one, or any indirect call; external functions don't unwind). -/
def throwsKind (ext : List String) : OpKind → Bool
  | .throw_ | .callIndirect _ | .invokeIndirect .. => true
  | .call f | .invoke f _ => !ext.contains f
  | _ => false

mutual
  /-- Whether code may throw, at any depth. -/
  def mayThrowOps (ext : List String) : List Op → Bool
    | [] => false
    | .mk k _ _ regs _ :: os => throwsKind ext k || mayThrowRegions ext regs || mayThrowOps ext os
  def mayThrowRegions (ext : List String) : List Region → Bool
    | [] => false
    | .mk _ ops _ :: rs => mayThrowOps ext ops || mayThrowRegions ext rs
end

/-- A region's ops ending in a terminator: a `cf.try` region may fall off its end (an implicit
`cf.yield`), a block may not. -/
def endYield (ops : List Op) : List Op :=
  match ops.getLast? with
  | some o => if o.kind.isTerminator then ops else ops ++ [.mk .yield [] [] [] o.loc]
  | none => [.mk .yield [] [] [] none]

/-- A block whose `cf.yield` also gives `0` and a `poison` exception: the `cf.blocks` it belongs
to gives exceptions back as two more results. -/
def extendYield : Region → M Region
  | .mk ps ops lbl =>
    match ops.getLast? with
    | some (.mk .yield [] args [] yloc) => do
      let f ← fresh "x"
      let p ← fresh "x"
      pure (.mk ps (ops.dropLast ++ [.mk (.const 0) [res f (.int 1)] [] [] yloc,
        .mk .poison [res p .ptr] [] [] yloc, .mk .yield [] (args ++ [.var f, .var p]) [] yloc]) lbl)
    | _ => pure (.mk ps ops lbl)

/-- A `cf.blocks` (results `rs`, blocks `bs`, whose exceptions go to its block `^xe`) inside the
`cf.blocks` that handler `^l` belongs to. Jumps can't leave a `cf.blocks`, so `^xe` leaves it by
`cf.yield`, with two more results: `1` and the exception (the other blocks give `0` and `poison`).
A `cf.if` after it jumps to `^l` with the exception. -/
def escape (l xe : String) (p : Bool) (rs : List Result) (bs : List Region) (loc : Option Loc) :
    M (List Op) := do
  let bs ← bs.mapM extendYield
  let e ← fresh "x"
  let ps ← rs.mapM fun r => do pure (res (← fresh "x") r.ty)
  let one ← fresh "x"
  let eb : Region := .mk [res e .ptr]
    (ps.map (fun r => .mk .poison [r] [] [] loc) ++ [.mk (.const 1) [res one (.int 1)] [] [] loc,
      .mk .yield [] (ps.map (fun r => .var r.name) ++ [.var one, .var e]) [] loc]) (some xe)
  let flag ← fresh "x"
  let exn ← fresh "x"
  pure [.mk (.blocks p) (rs ++ [res flag (.int 1), res exn .ptr]) [] (bs ++ [eb]) loc,
    .mk .if_ [] [.var flag] [.mk [] [.mk (.br ⟨l, 1⟩) [] [.var exn] [] loc] none, .mk [] [] none] loc]

mutual
  /-- Lower an op's exceptions, where `h` is the block of the nearest `cf.blocks` that this
  function's exceptions go to (none: they leave the function). -/
  def exnOp (ext : List String) (h : Option String) : Op → M (List Op)
    | .mk .throw_ rs args [] loc =>
      match h with
      | some l => pure [.mk (.br ⟨l, args.length⟩) [] args [] loc]
      | none => pure [.mk .throw_ rs args [] loc]
    | .mk (.call f) rs args [] loc =>
      match h with
      | some l => pure [if ext.contains f then .mk (.call f) rs args [] loc
          else .mk (.invoke f ⟨l, 0⟩) rs args [] loc]
      | none => pure [.mk (.call f) rs args [] loc]
    | .mk (.callIndirect sig) rs args [] loc =>
      match h with
      | some l => pure [.mk (.invokeIndirect sig ⟨l, 0⟩) rs args [] loc]
      | none => pure [.mk (.callIndirect sig) rs args [] loc]
    | .mk .try_ rs _ [.mk _ bops _, .mk hps hops _] loc => do
      let t ← fresh "x"
      let c ← fresh "x"
      let body ← exnOps ext (some c) bops
      let entry : Region := .mk [] (endYield body) (some t)
      match h with
      | some l =>
        if mayThrowOps ext hops then do
          let xe ← fresh "x"
          let hops' ← exnOps ext (some xe) hops
          escape l xe false rs [entry, .mk hps (endYield hops') (some c)] loc
        else do
          let hops' ← exnOps ext none hops
          pure [.mk (.blocks false) rs [] [entry, .mk hps (endYield hops') (some c)] loc]
      | none => do
        let hops' ← exnOps ext none hops
        pure [.mk (.blocks false) rs [] [entry, .mk hps (endYield hops') (some c)] loc]
    | .mk (.blocks p) rs args regs loc =>
      match h with
      | some l =>
        if mayThrowRegions ext regs then do
          let xe ← fresh "x"
          let regs' ← exnRegions ext (some xe) regs
          escape l xe p rs regs' loc
        else do pure [.mk (.blocks p) rs args (← exnRegions ext none regs) loc]
      | none => do pure [.mk (.blocks p) rs args (← exnRegions ext none regs) loc]
    | .mk k rs args regs loc => do pure [.mk k rs args (← exnRegions ext h regs) loc]
  def exnOps (ext : List String) (h : Option String) : List Op → M (List Op)
    | [] => pure []
    | o :: os => do
      let a ← exnOp ext h o
      let b ← exnOps ext h os
      pure (a ++ b)
  def exnRegions (ext : List String) (h : Option String) : List Region → M (List Region)
    | [] => pure []
    | .mk ps ops lbl :: rs => do
      let ops' ← exnOps ext h ops
      let rs' ← exnRegions ext h rs
      pure (.mk ps ops' lbl :: rs')
end

/-- Lower a function's exceptions: `cf.try` becomes `cf.blocks` with the handler as a block, and
in it each throw a jump to the handler and each call that may throw a `func.invoke` of it. Outside
`cf.try`, a throw stays `exn.throw` and a call a `func.call`, which unwind to the caller. -/
def lowerExn (ext : List String) (f : Func) : Except String Func := do
  let (ops, _) ← (exnOps ext none f.body.ops).run 0
  pure { f with body := .mk f.body.params ops f.body.label }

/-! ## Modules -/

/-- Lower a function: scalarize, lower exceptions, then expand. `ext` names the external
functions, which don't unwind. -/
def lowerFunc (sp : SpaceCfg) (ext : List String) (f : Func) : Except String Func := do
  let g ← tryCatch (scalarize sp f >>= lowerExn ext >>= expand sp) fun e =>
    throw s!"in @{f.name}: {e}"
  pure g

/-- Lower an HFIR module to MFIR. Globals and external functions stay as they are. -/
def lowerModule (m : Module) : Except String Module := do
  unless m.layer == .hfir do throw s!"lowering takes an HFIR module, not layer {m.layer.render}"
  let ext := m.externs.map (·.name)
  pure { m with layer := .mfir, funcs := ← m.funcs.mapM (lowerFunc m.space ext) }

end Fir.Lower
