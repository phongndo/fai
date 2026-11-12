import Fir

/-!
# `fir-ref`: the FIR-0 reference tool

```
fir-ref run FILE [@FUNC] [ARG...] [--fuel N]   run a function (default @main)
fir-ref check FILE                             verify; list holes
fir-ref fmt FILE [--no-locs] [--unverified]    print canonical text (--unverified: parse only)
fir-ref test PATH...                           run the test files (.fir) under PATH
```

Arguments are integers, `null` (for pointers), or `poison`. Every free choice takes the oracle's
answer `0`: `freeze` gives `0`, allocations succeed, and addresses are assigned first-fit. Every
external call returns zeros (`0`, `null`) and changes nothing (`World.zero`). The outcome line
lists the run's events first, each followed by `; `.

A test file is a `.fir` module with expectations in comments:

```
// run: @f(1, 2) -> returned i32 3
// error: is not defined
```

`run` compares the outcome line exactly. `error` expects parsing or verification to fail with a
message containing the text. Every test file must also print, reparse, and print identically.
-/

open Fir

def defaultFuel : Nat := 1000000

def parseArg (t : Ty) (s : String) : Except String RVal :=
  match t, s with
  | .int w, "poison" => .ok (.int w .poison)
  | .int w, _ => match s.toInt? with
    | some n => .ok (.int w (Sem.const w n))
    | none => .error s!"bad argument '{s}': expected an integer or poison"
  | .ptr, "null" => .ok (.ptr (some .null))
  | .ptr, "poison" => .ok (.ptr none)
  | _, _ => .error s!"bad argument '{s}' for {t}"

partial def drive (m : Machine) (steps limit : Nat) : String :=
  if steps ≥ limit then
    renderRun m.core.trace <|
      s!"out of fuel after {limit} steps" ++ (if m.inProgressLoop then " in a progress loop" else "")
  else
    match step m with
    | .ok m' => drive m' (steps + 1) limit
    | .error h => renderRun m.core.trace (renderHalt h)

/-- Run a function and describe the outcome in one line. -/
def runFunc (m : Module) (name : String) (args : List String) (fuel : Nat) :
    Except String String := do
  let some f := m.find? name | throw s!"no function @{name}"
  if args.length != f.params.length then
    throw s!"@{name} takes {f.params.length} arguments but got {args.length}"
  let vals ← (f.params.zip args).mapM fun (r, a) => parseArg r.ty a
  match Machine.init (fun _ => 0) World.zero m f vals with
  | .error h => pure (renderHalt h)
  | .ok mach => pure (drive mach 0 fuel)

def load (text : String) : Except String (Module × Array Hole) := do
  let m ← parseModule text
  let holes ← verifyModule m
  pure (m, holes)

/-- `@f(1, 2)` → `("f", ["1", "2"])` -/
def parseCall (s : String) : Option (String × List String) := do
  let s := s.trimAscii.toString
  guard (s.startsWith "@")
  let [name, rest] := (s.drop 1).toString.splitOn "(" | none
  let inner := (rest.dropEnd 1).toString
  guard (rest.endsWith ")")
  let args := if inner.trimAscii.isEmpty then [] else
    (inner.splitOn ",").map (·.trimAscii.toString)
  pure (name, args)

inductive Expect where
  | run (name : String) (args : List String) (outcome : String)
  | error (text : String)

def expectations (text : String) : Except String (List Expect) :=
  (text.splitOn "\n").filterMapM fun line =>
    let line := line.trimAscii.toString
    if line.startsWith "// run:" then
      let body := (line.drop 7).toString
      -- The outcome may contain ` -> ` itself (a function type), so split at the first.
      match body.splitOn " -> " with
      | call :: rest@(_ :: _) =>
        let outcome := " -> ".intercalate rest
        match parseCall call with
        | some (name, args) => .ok (some (.run name args outcome.trimAscii.toString))
        | none => .error s!"bad run line: {line}"
      | _ => .error s!"bad run line: {line}"
    else if line.startsWith "// error:" then
      .ok (some (.error (line.drop 9).trimAscii.toString))
    else .ok none

/-- Run one test file. Returns the failures. -/
def testFile (text : String) : Except String (List String) := do
  let exps ← expectations text
  let errs := exps.filterMap fun | .error t => some t | _ => none
  match load text with
  | .error e =>
    if errs.isEmpty then return [s!"unexpected error: {e}"]
    return errs.filterMap fun t => if (e.splitOn t).length > 1 then none
      else some s!"error '{e}' does not contain '{t}'"
  | .ok (m, _) =>
    if !errs.isEmpty then return [s!"expected an error containing '{errs.head!}'"]
    let mut fails := []
    let printed := m.render
    match parseModule printed with
    | .error e => fails := fails ++ [s!"printed text does not parse: {e}"]
    | .ok m2 =>
      if m2.render != printed then fails := fails ++ ["printing is not stable after reparsing"]
    for e in exps do
      if let .run name args want := e then
        let got := match runFunc m name args defaultFuel with
          | .ok s => s
          | .error e => s!"error: {e}"
        if got != want then
          fails := fails ++ [s!"@{name}({", ".intercalate args}): expected '{want}' but got '{got}'"]
    pure fails

partial def firFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let files ← p.walkDir
    pure ((files.filter (·.extension == some "fir")).qsort (·.toString < ·.toString))
  else pure #[p]

def cmdTest (paths : List String) : IO UInt32 := do
  let mut passed := 0
  let mut failed := 0
  for p in paths do
    for file in ← firFiles p do
      let text ← IO.FS.readFile file
      match testFile text with
      | .ok [] => passed := passed + 1
      | .ok fails =>
        failed := failed + 1
        IO.println s!"FAIL {file}"
        for f in fails do IO.println s!"  {f}"
      | .error e =>
        failed := failed + 1
        IO.println s!"FAIL {file}\n  {e}"
  IO.println s!"{passed} passed, {failed} failed"
  pure (if failed == 0 then 0 else 1)

def withModule (file : String) (k : Module → Array Hole → IO UInt32) : IO UInt32 := do
  match load (← IO.FS.readFile file) with
  | .error e => IO.eprintln s!"{file}: {e}"; pure 1
  | .ok (m, holes) => k m holes

def usage : String := "usage:
  fir-ref run FILE [@FUNC] [ARG...] [--fuel N]
  fir-ref check FILE
  fir-ref fmt FILE [--no-locs] [--unverified]
  fir-ref test PATH..."

def main (args : List String) : IO UInt32 := do
  match args with
  | "run" :: file :: rest =>
    let (fuel, rest) := match rest.reverse with
      | n :: "--fuel" :: r => (n.toNat?.getD defaultFuel, r.reverse)
      | _ => (defaultFuel, rest)
    let (name, callArgs) := match rest with
      | f :: r => if f.startsWith "@" then ((f.drop 1).toString, r) else ("main", rest)
      | [] => ("main", [])
    withModule file fun m _ => do
      match runFunc m name callArgs fuel with
      | .ok s => IO.println s; pure 0
      | .error e => IO.eprintln e; pure 1
  | ["check", file] =>
    withModule file fun _ holes => do
      if holes.isEmpty then IO.println "ok"
      else
        for h in holes do
          IO.println s!"hole ?{h.name}: {h.ty} {Loc.render h.loc}"
      pure 0
  | "fmt" :: file :: opts =>
    let print (m : Module) : IO UInt32 := do
      IO.print (m.render (showLocs := !opts.contains "--no-locs"))
      pure 0
    if opts.contains "--unverified" then
      match parseModule (← IO.FS.readFile file) with
      | .error e => IO.eprintln s!"{file}: {e}"; pure 1
      | .ok m => print m
    else withModule file fun m _ => print m
  | "test" :: paths@(_ :: _) => cmdTest paths
  | _ => IO.eprintln usage; pure 2
