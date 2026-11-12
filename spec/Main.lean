import Fir

/-!
# `fir-ref`: the FIR-0 reference tool

```
fir-ref run FILE [@FUNC] [ARG...] [--fuel N]   run a function (default @main)
fir-ref check FILE                             verify; list holes
fir-ref fmt FILE [--no-locs] [--unverified]    print canonical text (--unverified: parse only)
fir-ref test PATH...                           run the test files (.fir) under PATH
fir-ref lower FILE [--no-locs]                 lower an HFIR module to MFIR and print it
```

Arguments are integers, floats (`1.5`, `-inf`, `nan(0x1)`; see `Fir.FloatText`), `null` (for
pointers), or `poison`. Every free choice takes the oracle's
answer `0`: `freeze` gives `0`, allocations succeed, and addresses are assigned first-fit. Every
external call returns zeros (`0`, `null`) and changes nothing (`World.zero`). The outcome line
lists the run's events first, each followed by `; `.

A test file is a `.fir` module with expectations in comments:

```
// run: @f(1, 2) -> returned i32 3
// error: is not defined
// lower-error: cannot lower
```

`run` compares the outcome line exactly. `error` expects parsing or verification to fail with a
message containing the text, and `lower-error` lowering to fail so. Every test file must also print, reparse, and print identically.
An HFIR test file must also lower to MFIR (`Fir.Lower`) that verifies and prints stably, and
every `run` line must give the same outcome on the lowering, unless the HFIR run ends in UB (or
gets stuck), where the lowering must perform the same events first and may then do anything.
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
  | .float f, "poison" => .ok (.float f .poison)
  | .float f, _ => match (Float.parseLit s).bind (·.toBits f.fmt) with
    | some b => .ok (.float f (.bits b))
    | none => .error s!"bad argument '{s}': expected a float like 1.5, inf, nan, or poison"
  | _, _ => .error s!"bad argument '{s}' for {t}"

/-- How a run went: its events, how it ended, and whether that ending lets a refinement do
anything (UB or stuck) or is unknown (out of fuel). -/
structure RunResult where
  events : List Event := []
  ending : String
  absorbing : Bool := false
  outOfFuel : Bool := false
  deriving Inhabited

def RunResult.render (r : RunResult) : String := renderRun r.events r.ending

def RunResult.ofHalt (events : List Event) (h : Halt) : RunResult :=
  { events, ending := renderHalt h, absorbing := h.outcome matches .ub _ | .stuck _ }

partial def drive (m : Machine) (steps limit : Nat) (post : Halt → Halt := id) : RunResult :=
  if steps ≥ limit then
    { events := m.core.trace, outOfFuel := true,
      ending := s!"out of fuel after {limit} steps" ++
        (if m.inProgressLoop then " in a progress loop" else "") }
  else
    match step m with
    | .ok m' => drive m' (steps + 1) limit post
    | .error h => .ofHalt m.core.trace (post h)

/-- Run a function. With `lowerRets`, returned values are shown as the scalars the lowering
returns instead (`Lower.lowerValue`). -/
def runFuncR (m : Module) (name : String) (args : List String) (fuel : Nat)
    (lowerRets := false) : Except String RunResult := do
  let some f := m.find? name | throw s!"no function @{name}"
  if args.length != f.params.length then
    throw s!"@{name} takes {f.params.length} arguments but got {args.length}"
  let vals ← (f.params.zip args).mapM fun (r, a) => parseArg r.ty a
  if m.layer matches .lfir _ then return { ending := AArch64.run m f vals fuel }
  let lowerHalt (h : Halt) : Halt := match h.outcome with
    | .ret vs => if lowerRets then
        { h with outcome := .ret (Lower.lowerValues m.space.addrBits f.rets vs) } else h
    | _ => h
  match Machine.init Oracle.zero World.zero m f vals with
  | .error h => pure (.ofHalt [] h)
  | .ok mach => pure (drive mach 0 fuel lowerHalt)

/-- Run a function and describe the outcome in one line. -/
def runFunc (m : Module) (name : String) (args : List String) (fuel : Nat) :
    Except String String :=
  (runFuncR m name args fuel).map RunResult.render

/-- Whether a run of the lowering `tgt` agrees with the HFIR run `src`: the same outcome line,
unless `src` ends in UB or gets stuck, where `tgt` must have `src`'s events first. A source that
runs out of fuel is not compared. -/
def RunResult.lowersTo (src tgt : RunResult) : Bool :=
  src.outOfFuel || src.render == tgt.render ||
    (src.absorbing && (src.events.map Event.render).isPrefixOf (tgt.events.map Event.render))

/-- The lowering gets more fuel: it takes more steps than the HFIR program. -/
def loweredFuel (fuel : Nat) : Nat := 16 * fuel

/-- Lower a verified HFIR module and check the result. -/
def lowerChecked (m : Module) : Except String Module := do
  let l ← Lower.lowerModule m
  match verifyModule l with
  | .ok _ => pure l
  | .error e => throw s!"the lowering doesn't verify: {e}"

def load (text : String) : Except String (Module × Array Hole) := do
  let m ← parseModule text
  let holes ← verifyModule m
  pure (m, holes)

/-- `@f(1, 2)` → `("f", ["1", "2"])`. An argument may hold parentheses (`nan(0x1)`). -/
def parseCall (s : String) : Option (String × List String) := do
  let s := s.trimAscii.toString
  guard (s.startsWith "@")
  let name :: rest@(_ :: _) := (s.drop 1).toString.splitOn "(" | none
  let rest := "(".intercalate rest
  let inner := (rest.dropEnd 1).toString
  guard (rest.endsWith ")")
  let args := if inner.trimAscii.isEmpty then [] else
    (inner.splitOn ",").map (·.trimAscii.toString)
  pure (name, args)

inductive Expect where
  | run (name : String) (args : List String) (outcome : String)
  | error (text : String)
  | lowerError (text : String)

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
    else if line.startsWith "// lower-error:" then
      .ok (some (.lowerError (line.drop 15).trimAscii.toString))
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
    let lowerErrs := exps.filterMap fun | .lowerError t => some t | _ => none
    if m.layer == .hfir then
      match lowerChecked m with
      | .error e =>
        if lowerErrs.isEmpty then fails := fails ++ [s!"lowering: {e}"]
        for t in lowerErrs do
          unless (e.splitOn t).length > 1 do
            fails := fails ++ [s!"lowering error '{e}' does not contain '{t}'"]
      | .ok l =>
        unless lowerErrs.isEmpty do
          fails := fails ++ [s!"expected lowering to fail with '{lowerErrs.head!}'"]
        let printed := l.render
        match parseModule printed with
        | .error e => fails := fails ++ [s!"the printed lowering does not parse: {e}"]
        | .ok l2 =>
          if l2.render != printed then fails := fails ++ ["printing the lowering is not stable"]
        for e in exps do
          if let .run name args _ := e then
            match runFuncR m name args defaultFuel (lowerRets := true),
                runFuncR l name args (loweredFuel defaultFuel) with
            | .ok src, .ok tgt =>
              unless src.lowersTo tgt do
                fails := fails ++ [s!"@{name}({", ".intercalate args}) lowered: expected '{src.render}' but got '{tgt.render}'"]
            | _, _ => pure ()
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
  fir-ref test PATH...
  fir-ref lower FILE [--no-locs]"

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
  | "lower" :: file :: opts =>
    withModule file fun m _ => do
      match lowerChecked m with
      | .ok l => IO.print (l.render (showLocs := !opts.contains "--no-locs")); pure 0
      | .error e => IO.eprintln s!"{file}: {e}"; pure 1
  | _ => IO.eprintln usage; pure 2
