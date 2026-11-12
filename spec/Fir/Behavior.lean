import Fir.Refinement
import Fir.Interp

/-!
# Behaviors and program refinement

The set of behaviors of a function call, and what it means for one function to correctly
replace another.
-/

namespace Fir

/-- From step `N` on, the frame `d` from the bottom of the stack is always a `progress` loop:
that loop never exits. (Frames below the top change only by being popped, and a loop frame is
replaced only by itself on `cf.continue`, as a `cf.blocks` frame is on a jump, so this is the
same as the frames up to and including the loop never changing.) This is exactly a
`cf.loop progress` that runs forever, including one whose body never returns from a call, and a
`cf.blocks progress` whose jumps never leave it. -/
def StuckInProgressLoop (oracle : Nat → Int) (mod : Module) (f : Func) (args : List RVal) :
    Prop :=
  ∃ N d, ∀ n, N ≤ n → ∃ m, stateAt oracle mod f args n = .ok m ∧ m.inProgressLoopAt d

/-- `Behaves mod f args b`: calling `f` (in module `mod`) with `args` can have behavior `b`, for
some choice of the oracle's answers. A run either halts, or runs forever; running forever inside
a `progress` loop is UB. -/
def Behaves (mod : Module) (f : Func) (args : List RVal) (b : Behavior) : Prop :=
  ∃ oracle : Nat → Int,
    (∃ n h, stateAt oracle mod f args n = .error h ∧ h.behavior = b) ∨
    ((∀ n, ∃ m, stateAt oracle mod f args n = .ok m) ∧
      ((StuckInProgressLoop oracle mod f args ∧ b = .ub .noProgress) ∨
       (¬ StuckInProgressLoop oracle mod f args ∧ b = .diverge)))

/-- `tgt.Refines src`: `tgt` correctly replaces `src` in module `mod`. For all arguments
(including `poison`), every behavior of `tgt` refines some behavior of `src`. Allocation ids,
tags, and addresses are oracle choices, so `src` can match the ones `tgt` picks even when `tgt`
allocates less. -/
def Func.Refines (mod : Module) (tgt src : Func) : Prop :=
  ∀ args b, Behaves mod tgt args b → ∃ b', Behaves mod src args b' ∧ b.Refines b'

/-- No run of `f` reaches a choice the reference semantics doesn't decide. -/
def Func.Decided (mod : Module) (f : Func) : Prop :=
  ∀ args, ¬ Behaves mod f args .ambiguous

theorem Func.Refines.refl (mod : Module) (f : Func) (h : f.Decided mod) : f.Refines mod f :=
  fun args b hb => ⟨b, hb, Behavior.Refines.refl b (by rintro rfl; exact h args hb)⟩

theorem Func.Refines.trans {mod : Module} {a b c : Func} :
    a.Refines mod b → b.Refines mod c → a.Refines mod c := by
  intro hab hbc args x hx
  obtain ⟨y, hy, hxy⟩ := hab args x hx
  obtain ⟨z, hz, hyz⟩ := hbc args y hy
  exact ⟨z, hz, Behavior.Refines.trans hxy hyz⟩

end Fir
