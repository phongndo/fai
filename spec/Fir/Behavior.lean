import Fir.Refinement
import Fir.Interp

/-!
# Behaviors and program refinement

The set of behaviors of a function call, and what it means for one function to correctly
replace another.
-/

namespace Fir

/-- From step `N` on, the machine never leaves some `progress` loop: the frames from the bottom of
the stack up to and including that loop never change again. Since FIR-0 has no side effects, this
is exactly a `cf.loop progress` that never exits. Once memory and I/O exist, the condition also
requires that the loop performs no effects. -/
def StuckInProgressLoop (oracle : Nat → Int) (mod : Module) (f : Func) (args : List RVal) :
    Prop :=
  ∃ N d mN, stateAt oracle mod f args N = .ok mN ∧
    ∀ n, N ≤ n → ∃ m, stateAt oracle mod f args n = .ok m ∧
      (∃ body rs loc, m.stack.reverse[d]? = some (.loop true body rs loc)) ∧
      m.stack.reverse.take (d + 1) = mN.stack.reverse.take (d + 1)

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

theorem Func.Refines.refl (mod : Module) (f : Func) : f.Refines mod f :=
  fun _ b h => ⟨b, h, Behavior.Refines.refl b⟩

theorem Func.Refines.trans {mod : Module} {a b c : Func} :
    a.Refines mod b → b.Refines mod c → a.Refines mod c := by
  intro hab hbc args x hx
  obtain ⟨y, hy, hxy⟩ := hab args x hx
  obtain ⟨z, hz, hyz⟩ := hbc args y hy
  exact ⟨z, hz, Behavior.Refines.trans hxy hyz⟩

end Fir
