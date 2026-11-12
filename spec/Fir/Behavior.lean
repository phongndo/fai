import Fir.Refinement
import Fir.Interp

/-!
# Behaviors and program refinement

The set of behaviors of a function call, and what it means for one function to correctly
replace another.

A behavior is a trace: the events (external calls) a run performs, and how it ends. Events live in
the core's `trace`, which only grows (`Fir.Space`), so a run's trace at any step is a prefix of
every later one. A run that halts ends with the trace of its last running state: no step that
halts adds an event. A run that goes on forever has either finitely many events (its trace stops
growing; it diverges silently, or is UB if it is stuck in a `progress` loop) or infinitely many.
-/

namespace Fir

/-- From step `N` on, the frame `d` from the bottom of the stack is always a `progress` loop:
that loop never exits. (Frames below the top change only by being popped, and a loop frame is
replaced only by itself on `cf.continue`, as a `cf.blocks` frame is on a jump, so this is the
same as the frames up to and including the loop never changing.) This is exactly a
`cf.loop progress` that runs forever, including one whose body never returns from a call, and a
`cf.blocks progress` whose jumps never leave it. It makes a run UB only if the run has finitely
many events: a loop that keeps calling external functions makes progress. -/
def StuckInProgressLoop (oracle : Nat → Int) (world : World) (mod : Module) (f : Func)
    (args : List RVal) : Prop :=
  ∃ N d, ∀ n, N ≤ n → ∃ m, stateAt oracle world mod f args n = .ok m ∧ m.inProgressLoopAt d

/-- The run halts with outcome `o` after the events `es`: the call fails to start, or a step from
a running state halts. -/
def Halts (oracle : Nat → Int) (world : World) (mod : Module) (f : Func) (args : List RVal)
    (es : List Event) (o : Outcome) : Prop :=
  (∃ h, Machine.init oracle world mod f args = .error h ∧ es = [] ∧ h.outcome = o) ∨
  (∃ n m h, stateAt oracle world mod f args n = .ok m ∧ step m = .error h ∧
    es = m.core.trace ∧ h.outcome = o)

/-- The run never halts. -/
def RunsForever (oracle : Nat → Int) (world : World) (mod : Module) (f : Func) (args : List RVal) :
    Prop :=
  ∀ n, ∃ m, stateAt oracle world mod f args n = .ok m

/-- The run's events are exactly `es`: every state's trace is a prefix of `es`, and some state's
is `es`. -/
def FinalTrace (oracle : Nat → Int) (world : World) (mod : Module) (f : Func) (args : List RVal)
    (es : List Event) : Prop :=
  (∀ n m, stateAt oracle world mod f args n = .ok m → m.core.trace <+: es) ∧
  ∃ n m, stateAt oracle world mod f args n = .ok m ∧ m.core.trace = es

/-- Event `i` of the run is `e`. -/
def EventAt (oracle : Nat → Int) (world : World) (mod : Module) (f : Func) (args : List RVal)
    (i : Nat) (e : Event) : Prop :=
  ∃ n m, stateAt oracle world mod f args n = .ok m ∧ m.core.trace[i]? = some e

/-- Calling `f` (in module `mod`) with `args`, in the world `world`, with the oracle `oracle`, has
behavior `b`. A run either halts, or runs forever with finitely many events (diverging, or UB if it
never leaves a `progress` loop), or runs forever with infinitely many. -/
def BehavesWith (oracle : Nat → Int) (world : World) (mod : Module) (f : Func) (args : List RVal) :
    Behavior → Prop
  | .fin es o =>
    Halts oracle world mod f args es o ∨
    (RunsForever oracle world mod f args ∧ FinalTrace oracle world mod f args es ∧
      ((StuckInProgressLoop oracle world mod f args ∧ o = .ub .noProgress) ∨
       (¬ StuckInProgressLoop oracle world mod f args ∧ o = .diverge)))
  | .inf es => RunsForever oracle world mod f args ∧ ∀ i, EventAt oracle world mod f args i (es i)

/-- `Behaves world mod f args b`: calling `f` (in module `mod`) with `args`, in the world `world`,
can have behavior `b`, for some choice of the oracle's answers. -/
def Behaves (world : World) (mod : Module) (f : Func) (args : List RVal) (b : Behavior) : Prop :=
  ∃ oracle : Nat → Int, BehavesWith oracle world mod f args b

/-- `t.Refines s`: what an external function is shown, refined: the same function, arguments
and memory that refine the source's. -/
def Call.Refines (t s : Call) : Prop :=
  t.callee = s.callee ∧ t.rets = s.rets ∧ RVal.RefinesList t.args s.args ∧
    Forall2 (fun x y => x.1 = y.1 ∧ Forall2 Byte.Refines x.2 y.2) t.mem s.mem

/-- A world whose answers don't depend on what `poison` is: anything it may answer to a call or
history, it may answer to a refined one. The real world never sees `poison` (it sees some value),
so the worlds programs run in are monotone. -/
def World.Monotone (w : World) : Prop :=
  ∀ ht hs ct cs k, Events.Refines ht hs → ct.Refines cs → ∃ k', w.answer ht ct k = w.answer hs cs k'

/-- The world `fir-ref run` uses is monotone: its answer depends only on the result types. -/
theorem World.zero_monotone : World.zero.Monotone :=
  fun _ _ _ _ k _ hc => ⟨k, by simp only [World.zero, hc.2.1]⟩

/-- `tgt.Refines src`: `tgt` correctly replaces `src` in module `mod`. In every monotone world, for
all arguments (including `poison`), every behavior of `tgt` refines some behavior of `src`.
Allocation ids, tags, and addresses are oracle choices, so `src` can match the ones `tgt` picks
even when `tgt` allocates less. The world is the same for both: it answers each external call,
so a source must have every target event with the same results. -/
def Func.Refines (mod : Module) (tgt src : Func) : Prop :=
  ∀ world, world.Monotone → ∀ args b, Behaves world mod tgt args b →
    ∃ b', Behaves world mod src args b' ∧ b.Refines b'

/-- No run of `f` reaches a choice the reference semantics doesn't decide. -/
def Func.Decided (mod : Module) (f : Func) : Prop :=
  ∀ world, world.Monotone → ∀ args es, ¬ Behaves world mod f args (.fin es .ambiguous)

theorem Func.Refines.refl (mod : Module) (f : Func) (h : f.Decided mod) : f.Refines mod f :=
  fun world hw args b hb => ⟨b, hb, Behavior.Refines.refl b (by rintro es rfl; exact h world hw args es hb)⟩

theorem Func.Refines.trans {mod : Module} {a b c : Func} :
    a.Refines mod b → b.Refines mod c → a.Refines mod c := by
  intro hab hbc world hw args x hx
  obtain ⟨y, hy, hxy⟩ := hab world hw args x hx
  obtain ⟨z, hz, hyz⟩ := hbc world hw args y hy
  exact ⟨z, hz, Behavior.Refines.trans hxy hyz⟩

end Fir
