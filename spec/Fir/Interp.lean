import Std.Data.HashMap
import Fir.Basic
import Fir.Syntax
import Fir.Sem

/-!
# Reference interpreter

A small-step machine: `step` runs one op. The machine keeps the environment and an explicit stack
of frames, so every intermediate state can be inspected. `Fir.Behavior` uses that to define
divergence and the `progress` rule precisely.

`freeze` of `poison` picks a value from an *oracle*. The semantics quantifies over every oracle;
the command-line tool uses one that always picks `0`.
-/

namespace Fir

abbrev Env := Std.HashMap String RVal

/-- A stack frame. The top of the stack is always a `block`. -/
inductive Frame where
  /-- The ops left to run in the current region. -/
  | block (ops : List Op)
  /-- A `cf.if` waiting for its region to `cf.yield`. -/
  | ifJoin (results : List Result) (loc : Option Loc)
  /-- A running `cf.loop`. Its body runs in the frames above it. -/
  | loop (progress : Bool) (body : Region) (results : List Result) (loc : Option Loc)

structure Machine where
  env : Env
  stack : List Frame
  rets : List Ty
  oracle : Nat → Int
  /-- How many oracle choices have been used. -/
  choices : Nat

/-- How a run ends: its behavior, and the location of the op that ended it. -/
abbrev Halt := Behavior × Option Loc

abbrev SM := StateT Machine (Except Halt)

def halt (b : Behavior) (loc : Option Loc) : SM α := throw (b, loc)

def lookup (loc : Option Loc) (n : String) : SM RVal := do
  match (← get).env[n]? with
  | some v => pure v
  | none => halt (.stuck s!"%{n} is not defined") loc

def evalOperand (loc : Option Loc) : Operand → SM RVal
  | .var n => lookup loc n
  | .hole n _ => halt (.hole n) loc

def bindAll (loc : Option Loc) : List (String × Ty) → List RVal → SM Unit
  | [], [] => pure ()
  | (n, t) :: ns, v :: vs => do
    if v.w ≠ t.width then halt (.stuck s!"%{n} has type {t} but got an i{v.w}") loc
    modify fun m => { m with env := m.env.insert n v }
    bindAll loc ns vs
  | _, _ => halt (.stuck "wrong number of values") loc

/-- Bind op results, then check their facts: a violated fact is UB. -/
def bindResults (loc : Option Loc) (rs : List Result) (vs : List RVal) : SM Unit := do
  bindAll loc (rs.map fun r => (r.name, r.ty)) vs
  for (r, v) in rs.zip vs do
    for f in r.facts do
      unless f.fact.holds v.v do halt (.ub .fact) loc

def asVal (loc : Option Loc) (w : Nat) (r : RVal) : SM (Val w) :=
  if h : r.w = w then pure (h ▸ r.v)
  else halt (.stuck s!"expected an i{w} but got an i{r.w}") loc

def fromOut (loc : Option Loc) : OpOut w → SM (Val w)
  | .ok v => pure v
  | .trap r => halt (.trap r) loc
  | .ub k => halt (.ub k) loc

/-- Evaluate an op without regions. -/
def evalSimple (loc : Option Loc) (k : OpKind) (rs : List Result) (vs : List RVal) :
    SM (List RVal) :=
  match k, rs, vs with
  | .const n, [r], [] => pure [⟨_, Sem.const r.ty.width n⟩]
  | .poison, [r], [] => pure [⟨r.ty.width, .poison⟩]
  | .freeze, [_], [⟨w, .poison⟩] => do
    let m ← get
    set { m with choices := m.choices + 1 }
    pure [⟨w, .bits (BitVec.ofInt w (m.oracle m.choices))⟩]
  | .freeze, [_], [v] => pure [v]
  | .select, [r], [c, a, b] => do
    let c ← asVal loc 1 c
    let a ← asVal loc r.ty.width a
    let b ← asVal loc r.ty.width b
    pure [⟨_, Sem.select c a b⟩]
  | .arith op ovf, [r], [a, b] => do
    let x ← asVal loc r.ty.width a
    let y ← asVal loc r.ty.width b
    pure [⟨_, ← fromOut loc (Sem.arith op ovf x y)⟩]
  | .bit op, [r], [a, b] => do
    let x ← asVal loc r.ty.width a
    let y ← asVal loc r.ty.width b
    pure [⟨_, Sem.bit op x y⟩]
  | .div op zero ovf, [r], [a, b] => do
    let x ← asVal loc r.ty.width a
    let y ← asVal loc r.ty.width b
    pure [⟨_, ← fromOut loc (Sem.div op zero ovf x y)⟩]
  | .shift op edge, [r], [a, b] => do
    let x ← asVal loc r.ty.width a
    let y ← asVal loc r.ty.width b
    pure [⟨_, ← fromOut loc (Sem.shift op edge x y)⟩]
  | .cmp p, [_], [a, b] => do
    let y ← asVal loc a.w b
    pure [⟨_, Sem.cmp p a.v y⟩]
  | .zext, [r], [a] => pure [⟨_, Sem.zext r.ty.width a.v⟩]
  | .sext, [r], [a] => pure [⟨_, Sem.sext r.ty.width a.v⟩]
  | .trunc mode, [r], [a] => pure [⟨_, Sem.trunc mode r.ty.width a.v⟩]
  | _, _, _ => halt (.stuck "malformed op") loc

def push (f : Frame) : SM Unit := modify fun m => { m with stack := f :: m.stack }

/-- Split the stack at the nearest loop frame. -/
def splitAtLoop : List Frame → Option (Bool × Region × List Result × Option Loc × List Frame)
  | [] => none
  | .loop p body rs loc :: rest => some (p, body, rs, loc, rest)
  | _ :: rest => splitAtLoop rest

/-- Start a loop iteration: bind the loop state and push the body. -/
def enterBody (loc : Option Loc) (body : Region) (vs : List RVal) : SM Unit := do
  bindAll loc body.params vs
  push (.block body.ops)

/-- Run a terminator. The current block has already been popped. -/
def terminate (loc : Option Loc) (k : OpKind) (vs : List RVal) : SM Unit := do
  let m ← get
  match k with
  | .yield =>
    match m.stack with
    | .ifJoin rs loc' :: rest =>
      set { m with stack := rest }
      bindResults loc' rs vs
    | .loop .. :: _ => halt (.stuck "a loop body must end with cf.break or cf.continue") loc
    | _ => halt (.stuck "the function ended without func.ret") loc
  | .brk =>
    match splitAtLoop m.stack with
    | some (_, _, rs, loc', rest) =>
      set { m with stack := rest }
      bindResults loc' rs vs
    | none => halt (.stuck "cf.break outside a loop") loc
  | .cont =>
    match splitAtLoop m.stack with
    | some (p, body, rs, loc', rest) =>
      set { m with stack := .loop p body rs loc' :: rest }
      enterBody loc body vs
    | none => halt (.stuck "cf.continue outside a loop") loc
  | .ret =>
    if vs.map (·.w) == m.rets.map (·.width) then halt (.ret vs) loc
    else halt (.stuck "func.ret values don't match the function's return types") loc
  | _ => halt (.stuck "not a terminator") loc

/-- Run one op. The current block (with the op removed) is on top of the stack. -/
def execOp : Op → SM Unit
  | .mk kind results args regions loc => do
    let vs ← args.mapM (evalOperand loc)
    match kind, regions with
    | .if_, [thn, els] => do
      let c ← asVal loc 1 (vs.headD ⟨0, .poison⟩)
      match c with
      | .poison => halt (.ub .poison) loc
      | .bits b =>
        push (.ifJoin results loc)
        push (.block (if b = 1 then thn else els).ops)
    | .loop p, [body] => do
      push (.loop p body results loc)
      enterBody loc body vs
    | k, [] =>
      if k.isTerminator then do
        modify fun m => { m with stack := m.stack.drop 1 }
        terminate loc k vs
      else
        bindResults loc results (← evalSimple loc k results vs)
    | _, _ => halt (.stuck "malformed op") loc

/-- One step of the machine. -/
def step : SM Unit := do
  let m ← get
  match m.stack with
  | .block [] :: rest =>
    -- Falling off the end of a region is an implicit `cf.yield` with no values.
    set { m with stack := rest }
    terminate none .yield []
  | .block (op :: ops) :: rest =>
    set { m with stack := .block ops :: rest }
    execOp op
  | _ => halt (.stuck "no block to run") none

/-- The machine at the start of a call. -/
def Machine.init (oracle : Nat → Int) (f : Func) (args : List RVal) : Except Halt Machine :=
  let m : Machine := { env := {}, stack := [.block f.body.ops], rets := f.rets, oracle, choices := 0 }
  (bindAll none f.params args).run m |>.map (·.2)

/-- Run `n` steps. An `error` is a halted run. -/
def runSteps : Nat → Machine → Except Halt Machine
  | 0, m => .ok m
  | n + 1, m =>
    match step.run m with
    | .ok ((), m') => runSteps n m'
    | .error h => .error h

/-- The state after `n` steps of a call. -/
def stateAt (oracle : Nat → Int) (f : Func) (args : List RVal) (n : Nat) : Except Halt Machine :=
  (Machine.init oracle f args).bind (runSteps n)

/-- Whether any active loop is a `progress` loop. -/
def Machine.inProgressLoop (m : Machine) : Bool :=
  m.stack.any fun | .loop true .. => true | _ => false

end Fir
