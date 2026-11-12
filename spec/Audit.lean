import Lean
import Fir
import Audit.Claims

/-!
# `fir-audit`: what the proofs prove, and what changed

```
lake exe fir-audit [--lock FILE] [--json] [--update] [--report FILE]
```

Loads the compiled `Fir` environment (it imports `Lean`, which `Fir` itself avoids so that
`fir-ref` stays small) and checks every assurance claim registered in `Audit.Claims`:

* **Exists.** Each claim names a theorem of the environment.
* **Axioms.** Its transitive axioms (Lean's `collectAxioms`) are among the standard foundations
  (`propext`, `Classical.choice`, `Quot.sound`) plus any the claim approves with a reason.
  `sorryAx` is never approved. Separately, no declaration of a `Fir` module may use `sorryAx`
  directly, and none may be an `axiom`.
* **Registered.** Every theorem of a `Fir` module whose docstring opens with a bold headline
  (`**…**`), or whose conclusion is one of the relations proofs are about (`Func.Refines`,
  `Dce.PureKind`, `OpOut.Refines`, `Simulation`, …), must be a claim or listed as a supporting
  lemma, so a new correctness theorem can't go unreported.
* **Bindings.** A claim the Rust code relies on names a binding: a theorem in `Audit.Claims`
  whose statement is written out there and proved by the claim. The two statements must be the
  same expression, so a claim can't drift from what the Rust side was told it says.
* **Changes.** For each claim, the lock file (`docs/assurance/proofs.lock.json`) records its
  statement, a fingerprint of the statement, and fingerprints of the `Fir` definitions it
  depends on (transitively through definitions, inductive types, and theorem statements, not
  proofs). A claim whose statement, assumptions, or semantic dependencies changed since the lock
  was written fails with the differences, as *needing review*: a fingerprint says something
  changed, not whether the new statement is still adequate. `--update` rewrites the lock (and
  the report) after that review; the diff of the lock is what a reviewer reads.

The exit status is 0 only when every check passes. `--json` prints the findings as JSON;
`--report FILE` writes the human-readable report (`docs/assurance/proofs.md`).
-/

open Lean Meta

namespace Fir.Audit

/-- Axioms every claim may use: Lean's foundations. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Relations whose theorems are assurance theorems, by the head of their conclusion. -/
def trackedRelations : List Name :=
  [``Fir.Func.Refines, ``Fir.Dce.PureKind, ``Fir.OpOut.Refines, ``Fir.Simulation,
   ``Fir.SimulationS, ``Fir.Behavior.Refines]

def isFirModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).getRoot == `Fir
  | none => false

/-- The head constant of a statement's conclusion, under its binders and hypotheses. -/
partial def conclusionHead : Expr → Option Name
  | .forallE _ _ b _ => conclusionHead b
  | .mdata _ e => conclusionHead e
  | e => match e.getAppFn with
    | .const n _ => some n
    | _ => none

/-- The `Fir` constants a declaration's meaning depends on: its type, and for definitions,
inductive types, and constructors, their values and constructors. Theorems contribute their
statements only: a proof can change without changing what is claimed. -/
def directDeps (env : Environment) (n : Name) : Array Name := Id.run do
  let some ci := env.find? n | return #[]
  let mut es : Array Expr := #[ci.type]
  match ci with
  | .defnInfo d => es := es.push d.value
  | .opaqueInfo d => es := es.push d.value
  | .inductInfo d =>
    for c in d.ctors do
      if let some cc := env.find? c then es := es.push cc.type
  | .ctorInfo d => es := es.push (mkConst d.induct)
  | _ => pure ()
  let mut out : Array Name := #[]
  for e in es do
    for c in e.getUsedConstants do
      if isFirModule env c && !out.contains c then out := out.push c
  out

/-- The transitive `Fir` dependencies of a statement, sorted. -/
partial def closure (env : Environment) (roots : Array Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      for d in directDeps env n do
        if !seen.contains d then todo := d :: todo
  seen.toArray.qsort Name.lt

/-- A declaration's fingerprint: its type and, for definitions, its value (not a theorem's
proof). -/
def fingerprint (env : Environment) (n : Name) : UInt64 :=
  match env.find? n with
  | some (.defnInfo d) => mixHash d.type.hash d.value.hash
  | some (.opaqueInfo d) => mixHash d.type.hash d.value.hash
  | some (.inductInfo d) => d.ctors.foldl (fun h c =>
      mixHash h (match env.find? c with | some cc => cc.type.hash | none => 0)) d.type.hash
  | some ci => ci.type.hash
  | none => 0

def hex (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- What the audit found about one claim. -/
structure ClaimInfo where
  name : Name
  role : String
  summary : String
  statement : String
  statementHash : String
  assumptions : Nat
  axioms : Array Name
  deps : Array (Name × String)
  depsHash : String
  binding : Option Name

/-- Problems that make the audit fail. -/
structure Findings where
  errors : Array String := #[]
  review : Array String := #[]

def ClaimInfo.toJson (c : ClaimInfo) : Json :=
  Json.mkObj [
    ("name", toString c.name), ("role", c.role), ("summary", c.summary),
    ("statement", c.statement), ("statement_hash", c.statementHash),
    ("hypotheses", c.assumptions),
    ("axioms", Lean.toJson (c.axioms.map toString)),
    ("binding", Lean.toJson (c.binding.map toString)),
    ("dependencies", c.deps.size),
    ("dependencies_hash", c.depsHash)]

/-- How many explicit hypotheses (non-dependent arrows, or instance and explicit binders whose
type is a proposition) a statement has; reported so a change in assumptions stands out. -/
partial def countHyps : Expr → MetaM Nat
  | .forallE n t b bi => do
    let isProp ← (do pure (← inferType t).isProp) <|> pure false
    withLocalDecl n bi t fun x => do
      let rest ← countHyps (b.instantiate1 x)
      pure (if isProp then rest + 1 else rest)
  | _ => pure 0

def ppStatement (e : Expr) : MetaM String := do
  pure ((← ppExpr e).pretty 100)

def auditClaim (env : Environment) (c : Claim) : MetaM (Option ClaimInfo × Array String) := do
  let mut errs := #[]
  let some ci := env.find? c.name
    | return (none, #[s!"{c.name}: registered, but there is no such declaration"])
  unless ci matches .thmInfo _ do
    errs := errs.push s!"{c.name}: registered as a claim, but it is not a theorem"
  let axioms ← collectAxioms c.name
  for ax in axioms do
    if ax == ``sorryAx then
      errs := errs.push s!"{c.name}: depends on sorryAx (an unfinished proof)"
    else if !(standardAxioms.contains ax) && !(c.axioms.any (·.1 == ax)) then
      errs := errs.push s!"{c.name}: depends on the unapproved axiom {ax}"
  if let some b := c.binding then
    match env.find? b with
    | none => errs := errs.push s!"{c.name}: its binding {b} doesn't exist"
    | some bi =>
      unless bi.type == ci.type do
        errs := errs.push s!"{c.name}: its statement differs from the one its binding {b} writes out"
  let deps := closure env (ci.type.getUsedConstants.filter (isFirModule env))
  let depHashes := deps.map fun d => (d, hex (fingerprint env d))
  let depsHash := hex (depHashes.foldl (fun h (n, s) => mixHash h (mixHash n.hash s.hash)) 7)
  let info : ClaimInfo := {
    name := c.name, role := c.role, summary := c.summary,
    statement := ← ppStatement ci.type, statementHash := hex ci.type.hash,
    assumptions := ← countHyps ci.type, axioms, deps := depHashes, depsHash,
    binding := c.binding }
  pure (some info, errs)

/-- Theorems of `Fir` modules that must be registered: bold headlines and tracked conclusions. -/
def mustRegister (env : Environment) : IO (Array Name) := do
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    unless isFirModule env n do continue
    unless ci matches .thmInfo _ do continue
    -- Skip what the compiler generates (`match_1`, `proof_2`, `_eq_1`, …), not what people
    -- write: a private theorem's name is internal too, but its user-facing part isn't.
    if ((privateToUserName? n).getD n).isInternal then continue
    let headline := match ← findDocString? env n with
      | some d => d.trimAscii.toString.startsWith "**"
      | none => false
    let tracked := match conclusionHead ci.type with
      | some h => trackedRelations.contains h
      | none => false
    if headline || tracked then out := out.push n
  pure (out.qsort Name.lt)

/-- No `Fir` declaration may be an axiom or use `sorryAx` directly. -/
def globalScan (env : Environment) : Array String := Id.run do
  let mut errs := #[]
  for (n, ci) in env.constants.toList do
    unless isFirModule env n do continue
    if ci matches .axiomInfo _ then
      errs := errs.push s!"{n}: an axiom declared in a Fir module"
    -- `value?` leaves out theorems' proofs, which is where `sorry` usually is.
    let value := match ci with
      | .thmInfo t => some t.value
      | _ => ci.value? (allowOpaque := true)
    let uses := ci.type.getUsedConstants ++ (value.map (·.getUsedConstants) |>.getD #[])
    if uses.contains ``sorryAx then
      errs := errs.push s!"{n}: uses sorryAx"
  errs

/-- Every definition some claim depends on, with its fingerprint, sorted. -/
def allDeps (infos : Array ClaimInfo) : Array (Name × String) := Id.run do
  let mut m : NameMap String := {}
  for c in infos do
    for (n, h) in c.deps do m := m.insert n h
  m.toArray.qsort (fun a b => Name.lt a.1 b.1)

def lockJson (infos : Array ClaimInfo) : Json :=
  Json.mkObj [
    ("generator", "lake exe fir-audit --update (spec/Audit.lean)"),
    ("lean", Lean.versionString),
    ("note", "Reviewed fingerprints of the registered assurance claims. A change here means a statement, its assumptions, or a definition it depends on changed and was reviewed; it does not by itself say the new statement is adequate."),
    ("claims", Json.mkObj (infos.toList.map fun c => (toString c.name, c.toJson))),
    ("definitions", Json.mkObj (allDeps infos |>.toList.map fun (n, h) => (toString n, Json.str h)))]

/-- Compare with the lock: each difference needs review. -/
def compareLock (infos : Array ClaimInfo) (lock : Json) : Array String := Id.run do
  let mut out := #[]
  let claims := (lock.getObjVal? "claims").toOption.getD (Json.mkObj [])
  let get (j : Json) (k : String) : String := ((j.getObjValAs? String k).toOption).getD ""
  for c in infos do
    match claims.getObjVal? (toString c.name) with
    | .error _ => out := out.push s!"{c.name}: a new claim, not in the lock"
    | .ok old =>
      if get old "statement_hash" != c.statementHash then
        out := out.push s!"{c.name}: its statement changed\n    was: {get old "statement"}\n    now: {c.statement}"
      if (old.getObjValAs? Nat "hypotheses").toOption != some c.assumptions then
        out := out.push s!"{c.name}: its number of hypotheses changed (now {c.assumptions})"
      let oldAx := ((old.getObjValAs? (Array String) "axioms").toOption).getD #[]
      if oldAx != c.axioms.map toString then
        out := out.push s!"{c.name}: its axioms changed: was {oldAx}, now {c.axioms}"
      if get old "dependencies_hash" != c.depsHash then
        let oldDeps := (lock.getObjVal? "definitions").toOption.getD (Json.mkObj [])
        let mut changed := #[]
        for (n, h) in c.deps do
          match (oldDeps.getObjValAs? String (toString n)).toOption with
          | some h' => if h' != h then changed := changed.push s!"{n} (changed)"
          | none => changed := changed.push s!"{n} (new)"
        if changed.isEmpty then changed := changed.push "some it no longer depends on"
        let shown := changed.toList.take 12
        let more := if changed.size > 12 then s!", and {changed.size - 12} more" else ""
        out := out.push s!"{c.name}: definitions it depends on changed: {", ".intercalate shown}{more}"
  if let .obj kvs := claims then
    for (k, _) in kvs.toArray do
      unless infos.any (toString ·.name == k) do
        out := out.push s!"{k}: in the lock, but no longer registered"
  out

def report (infos : Array ClaimInfo) (f : Findings) (supporting : Nat) : String := Id.run do
  let mut s := "# Proof audit\n\nGenerated by `lake exe fir-audit --report` (spec/Audit.lean). Each claim is a theorem\nof the Lean development, with its statement as Lean prints it, its transitive axioms, and how\nmany `Fir` definitions its meaning depends on. A claim is only as strong as its statement:\nread the hypotheses. Open obligations are listed in `docs/assurance/README.md`.\n\n"
  s := s ++ s!"{infos.size} claims; {supporting} supporting lemmas registered; "
  s := s ++ s!"{f.errors.size} errors; {f.review.size} changes needing review.\n\n"
  for c in infos do
    s := s ++ s!"## `{c.name}` ({c.role})\n\n{c.summary}\n\n```lean\n{c.statement}\n```\n\n"
    s := s ++ s!"- axioms: {if c.axioms.isEmpty then "none" else ", ".intercalate (c.axioms.toList.map toString)}\n"
    s := s ++ s!"- hypotheses: {c.assumptions}; `Fir` definitions depended on: {c.deps.size}\n"
    if let some b := c.binding then s := s ++ s!"- bound for the Rust side by `{b}`\n"
    s := s ++ "\n"
  s

def runMeta (env : Environment) (x : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "<fir-audit>", fileMap := default, maxHeartbeats := 0 }
  let (a, _, _) ← x.toIO ctx { env }
  pure a

end Fir.Audit

open Fir.Audit in
unsafe def main (args : List String) : IO UInt32 := do
  let flag (f : String) := args.contains f
  let arg (f : String) : Option String :=
    match args.dropWhile (· != f) with
    | _ :: v :: _ => some v
    | _ => none
  let lockPath := (arg "--lock").getD "../docs/assurance/proofs.lock.json"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Fir }, { module := `Audit.Claims }] {} (loadExts := true)
  let run := runMeta env
  let mut f : Findings := {}
  let mut infos := #[]
  for c in Fir.Audit.claims do
    let (i, errs) ← run (auditClaim env c)
    f := { f with errors := f.errors ++ errs }
    if let some i := i then infos := infos.push i
  f := { f with errors := f.errors ++ globalScan env }
  let registered := Fir.Audit.claims.map (·.name) ++ Fir.Audit.supporting
  for n in ← mustRegister env do
    unless registered.contains n do
      f := { f with errors := f.errors.push s!"{n}: an assurance theorem that isn't registered in spec/Audit/Claims.lean (as a claim or a supporting lemma)" }
  for n in Fir.Audit.supporting do
    unless env.contains n do
      f := { f with errors := f.errors.push s!"{n}: listed as a supporting lemma, but there is no such declaration" }
  if flag "--update" then
    IO.FS.writeFile lockPath ((lockJson infos).pretty (lineWidth := 100) ++ "\n")
  else
    match (← IO.FS.readFile lockPath |>.toBaseIO) with
    | .error _ => f := { f with review := f.review.push s!"no lock file at {lockPath}: run --update after review" }
    | .ok text =>
      match Json.parse text with
      | .error e => f := { f with errors := f.errors.push s!"{lockPath}: not JSON: {e}" }
      | .ok lock => f := { f with review := compareLock infos lock }
  if let some path := arg "--report" then
    IO.FS.writeFile path (report infos f Fir.Audit.supporting.length)
  if flag "--json" then
    IO.println <| (Json.mkObj [
      ("ok", toJson (f.errors.isEmpty && f.review.isEmpty)),
      ("claims", toJson (infos.map (·.toJson))),
      ("errors", toJson f.errors), ("review", toJson f.review),
      ("supporting", toJson (Fir.Audit.supporting.map toString)),
      ("standard_axioms", toJson (standardAxioms.map toString))]).pretty (lineWidth := 100)
  else
    for c in infos do
      IO.println s!"claim {c.name}: axioms [{", ".intercalate (c.axioms.toList.map toString)}], {c.assumptions} hypotheses, {c.deps.size} Fir dependencies"
    for e in f.errors do IO.eprintln s!"error: {e}"
    for r in f.review do IO.eprintln s!"review: {r}"
    IO.println s!"{infos.size} claims, {Fir.Audit.supporting.length} supporting lemmas: {f.errors.size} errors, {f.review.size} changes needing review"
  pure (if f.errors.isEmpty && f.review.isEmpty then 0 else 1)
