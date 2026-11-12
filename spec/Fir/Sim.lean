import Fir.Behavior

/-!
# Simulation

The tool for proving that one function refines another: relate the target machine's states to
the source machine's, and show that each target step is matched by source steps.

`Simulation.refines` turns a step-by-step simulation into `Func.Refines`. It handles everything
about whole runs (halting, divergence, and `progress` loops that never exit), so a proof about a
rewrite only reasons about single steps.

Each target step is matched by one or more source steps (a source may take extra steps, as when
it runs a store the target deleted), or by the source halting with UB or getting stuck, after
which anything goes. Matching source states must agree with the target on which frames are
`progress` loops, so a target that never leaves such a loop has a source that never leaves one
either.
-/

namespace Fir

theorem Except.ok_bind (a : α) (f : α → Except ε β) : (Except.ok a).bind f = f a := rfl

theorem Except.error_bind (e : ε) (f : α → Except ε β) :
    (Except.error e : Except ε α).bind f = .error e := rfl

/-! ## Runs -/

theorem runSteps_add (a b : Nat) (m : Machine) :
    runSteps (a + b) m = (runSteps a m).bind (runSteps b) := by
  induction a generalizing m with
  | zero => simp [runSteps, Except.ok_bind]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [runSteps]
    cases step m with
    | ok m' => exact ih m'
    | error h => rfl

theorem runSteps_one (m : Machine) : runSteps 1 m = step m := by
  simp only [runSteps]
  cases step m <;> rfl

theorem runSteps_ok_of_le {n j : Nat} {m x : Machine} (h : runSteps n m = .ok x) (hj : j ≤ n) :
    ∃ y, runSteps j m = .ok y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [runSteps_add] at h
  cases e : runSteps j m with
  | ok y => exact ⟨y, rfl⟩
  | error e' => rw [e, Except.error_bind] at h; cases h

/-- A run that halts halted at some step that started from a running state. -/
theorem runSteps_first_error {n : Nat} {m : Machine} {h : Halt} (e : runSteps n m = .error h) :
    ∃ i mi, runSteps i m = .ok mi ∧ step mi = .error h := by
  induction n generalizing m with
  | zero => simp [runSteps] at e
  | succ n ih =>
    simp only [runSteps] at e
    cases es : step m with
    | ok m' =>
      rw [es] at e
      obtain ⟨i, mi, h1, h2⟩ := ih e
      exact ⟨i + 1, mi, by simp [runSteps, es, h1], h2⟩
    | error h' =>
      rw [es] at e
      cases e
      exact ⟨0, m, rfl, es⟩

/-! ## Simulations -/

/-- From `m`, the source halts with a behavior that every target behavior refines (UB or stuck),
or with `ambiguous` (which `Func.Decided` rules out). -/
def Escapes (m : Machine) : Prop :=
  ∃ j h, runSteps j m = .error h ∧ (h.behavior.Absorbing ∨ h.behavior = .ambiguous)

theorem Escapes.back {s : Nat} {m m' : Machine} (hs : runSteps s m = .ok m') :
    Escapes m' → Escapes m
  | ⟨j, h, e, hb⟩ => ⟨s + j, h, by rw [runSteps_add, hs, Except.ok_bind]; exact e, hb⟩

/-- How source state `ms` matches target state `mt`'s next step. If the target steps to `mt'`,
the source takes `k + 1` steps to a state related to `mt'`, and the states it passes through
have the same `progress` loops as `mt`. If the target halts, the source halts with a behavior
the target's refines. Either way, the source may instead escape. -/
def StepMatch (R : Machine → Machine → Prop) (mt ms : Machine) : Prop :=
  (∀ mt', step mt = .ok mt' → Escapes ms ∨
    ∃ k ms', runSteps (k + 1) ms = .ok ms' ∧ R mt' ms' ∧
      ∀ j mj, j ≤ k → runSteps j ms = .ok mj → mj.shape = mt.shape) ∧
  (∀ ht, step mt = .error ht → Escapes ms ∨
    ∃ j hs, runSteps j ms = .error hs ∧ ht.behavior.Refines hs.behavior)

/-- A step match for one relation is one for a weaker relation, where that holds of the states the
source reaches. -/
theorem StepMatch.mono {R1 R2 : Machine → Machine → Prop} {mt ms : Machine} (h : StepMatch R1 mt ms)
    (hr : ∀ mt' k ms', runSteps (k + 1) ms = .ok ms' → R1 mt' ms' → R2 mt' ms') :
    StepMatch R2 mt ms := by
  refine ⟨fun mt' e => ?_, h.2⟩
  rcases h.1 mt' e with hesc | ⟨k, ms', ek, hR, hsh⟩
  · exact .inl hesc
  · exact .inr ⟨k, ms', ek, hr mt' k ms' ek hR, hsh⟩

/-- `R` relates target states to source states, and every related pair matches. -/
def Simulation (R : Machine → Machine → Prop) : Prop :=
  ∀ mt ms, R mt ms → StepMatch R mt ms

/-- After `n` target steps, the source has run some `s ≥ n` steps to a related state, and every
source state before it has the same `progress` loops as some target state so far. -/
theorem Simulation.run {R : Machine → Machine → Prop} (sim : Simulation R) {mt ms : Machine}
    (hR : R mt ms) (n : Nat) {mtn : Machine} (e : runSteps n mt = .ok mtn) :
    Escapes ms ∨ ∃ s msn, n ≤ s ∧ runSteps s ms = .ok msn ∧ R mtn msn ∧
      ∀ j mj, j < s → runSteps j ms = .ok mj →
        ∃ i mti, i ≤ n ∧ runSteps i mt = .ok mti ∧ mj.shape = mti.shape := by
  induction n generalizing mtn with
  | zero =>
    simp only [runSteps, Except.ok.injEq] at e
    subst e
    exact .inr ⟨0, ms, Nat.le_refl _, rfl, hR, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    rw [runSteps_add n 1] at e
    cases en : runSteps n mt with
    | error h => rw [en, Except.error_bind] at e; cases e
    | ok mtn0 =>
      rw [en, Except.ok_bind, runSteps_one] at e
      rcases ih en with hesc | ⟨s, msn, hns, es, hR', cover⟩
      · exact .inl hesc
      rcases (sim _ _ hR').1 mtn e with hesc | ⟨k, ms', ek, hR'', inter⟩
      · exact .inl (hesc.back es)
      refine .inr ⟨s + (k + 1), ms', by omega, by rw [runSteps_add, es, Except.ok_bind]; exact ek,
        hR'', ?_⟩
      intro j mj hj ej
      by_cases hjs : j < s
      · obtain ⟨i, mti, hi, ei, hsh⟩ := cover j mj hjs ej
        exact ⟨i, mti, by omega, ei, hsh⟩
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hjs)
        rw [runSteps_add, es, Except.ok_bind] at ej
        exact ⟨n, mtn0, by omega, en, inter j' mj (by omega) ej⟩

/-- How the starting states of the target and source calls match. -/
def InitMatch (R : Machine → Machine → Prop) (it is : Except Halt Machine) : Prop :=
  (∃ hs, is = .error hs ∧ (hs.behavior.Absorbing ∨ hs.behavior = .ambiguous)) ∨
  (∃ mt ms, it = .ok mt ∧ is = .ok ms ∧ R mt ms) ∨
  (∃ ht hs, it = .error ht ∧ is = .error hs ∧ ht.behavior.Refines hs.behavior)

theorem inProgressLoopAt_of_shape {m m' : Machine} {d : Nat} (h : m.shape = m'.shape) :
    m'.inProgressLoopAt d → m.inProgressLoopAt d := by
  simp only [Machine.inProgressLoopAt, h]
  exact id

/-- A simulation from every starting state proves refinement, for a source that never reaches
an undecided choice. The source may use different oracle answers than the target. -/
theorem Simulation.refines {R : Machine → Machine → Prop} (sim : Simulation R) {mod : Module}
    {tgt src : Func}
    (init : ∀ oracle args, ∃ oracle',
      InitMatch R (Machine.init oracle mod tgt args) (Machine.init oracle' mod src args))
    (dec : src.Decided mod) : tgt.Refines mod src := by
  intro args b ⟨oracle, hb⟩
  obtain ⟨oracle', hinit⟩ := init oracle args
  -- A source run that halts with an absorbing behavior matches anything.
  have halted : ∀ n hs, stateAt oracle' mod src args n = .error hs →
      (hs.behavior.Absorbing ∨ hs.behavior = .ambiguous) →
      ∃ b', Behaves mod src args b' ∧ b.Refines b' := by
    intro n hs e hb'
    rcases hb' with hab | hamb
    · exact ⟨hs.behavior, ⟨oracle', .inl ⟨n, hs, e, rfl⟩⟩, .of_absorbing hab⟩
    · exact absurd ⟨oracle', .inl ⟨n, hs, e, hamb⟩⟩ (dec args)
  rcases hinit with ⟨hs, eis, hesc⟩ | ⟨mt, ms, eit, eis, hR⟩ | ⟨ht, hs, eit, eis, href⟩
  · exact halted 0 hs (by simp [stateAt, eis, Except.error_bind]) hesc
  · have st : ∀ n, stateAt oracle mod tgt args n = runSteps n mt := fun n => by
      simp [stateAt, eit, Except.ok_bind]
    have ss : ∀ n, stateAt oracle' mod src args n = runSteps n ms := fun n => by
      simp [stateAt, eis, Except.ok_bind]
    by_cases hesc : Escapes ms
    · obtain ⟨j, hs, e, hb'⟩ := hesc
      exact halted j hs (by rw [ss]; exact e) hb'
    rcases hb with ⟨n, h, e, rfl⟩ | ⟨hall, hcase⟩
    · -- The target halts.
      rw [st] at e
      obtain ⟨i, mti, ei, hstep⟩ := runSteps_first_error e
      rcases sim.run hR i ei with hesc' | ⟨s, msn, _, es, hR', _⟩
      · exact absurd hesc' hesc
      rcases (sim _ _ hR').2 h hstep with hesc' | ⟨j, hs, ej, href⟩
      · exact absurd (hesc'.back es) hesc
      refine ⟨hs.behavior, ⟨oracle', .inl ⟨s + j, hs, ?_, rfl⟩⟩, href⟩
      rw [ss, runSteps_add, es, Except.ok_bind]
      exact ej
    · -- The target runs forever, so the source does too.
      have tall : ∀ n, ∃ m, runSteps n mt = .ok m := fun n => by
        obtain ⟨m, e⟩ := hall n
        exact ⟨m, by rw [← st]; exact e⟩
      have sall : ∀ n, ∃ m, stateAt oracle' mod src args n = .ok m := by
        intro n
        obtain ⟨mtn, en⟩ := tall n
        rcases sim.run hR n en with hesc' | ⟨s, msn, hns, es, _⟩
        · exact absurd hesc' hesc
        obtain ⟨y, ey⟩ := runSteps_ok_of_le es hns
        exact ⟨y, by rw [ss]; exact ey⟩
      by_cases hsp : StuckInProgressLoop oracle' mod src args
      · exact ⟨.ub .noProgress, ⟨oracle', .inr ⟨sall, .inl ⟨hsp, rfl⟩⟩⟩, by simp [Behavior.Refines]⟩
      refine ⟨.diverge, ⟨oracle', .inr ⟨sall, .inr ⟨hsp, rfl⟩⟩⟩, ?_⟩
      rcases hcase with ⟨⟨N, d, hN⟩, rfl⟩ | ⟨_, rfl⟩
      · -- A target stuck in a `progress` loop has a source stuck in one too.
        exfalso
        apply hsp
        obtain ⟨mtN, eN, _⟩ := hN N (Nat.le_refl _)
        rw [st] at eN
        rcases sim.run hR N eN with hesc' | ⟨s0, ms0, _, es0, hR0, _⟩
        · exact absurd hesc' hesc
        refine ⟨s0, d, fun j hj => ?_⟩
        obtain ⟨x, ex⟩ := tall (N + (j - s0 + 1))
        rw [runSteps_add, eN, Except.ok_bind] at ex
        rcases sim.run hR0 (j - s0 + 1) ex with hesc' | ⟨s', _, hs', es', _, cover⟩
        · exact absurd (hesc'.back es0) hesc
        obtain ⟨mj, ej⟩ := runSteps_ok_of_le es' (show j - s0 ≤ s' by omega)
        obtain ⟨i, mti, _, ei, hsh⟩ := cover (j - s0) mj (by omega) ej
        obtain ⟨m', e', hp⟩ := hN (N + i) (by omega)
        rw [st, runSteps_add, eN, Except.ok_bind, ei, Except.ok.injEq] at e'
        subst e'
        refine ⟨mj, ?_, inProgressLoopAt_of_shape hsh hp⟩
        rw [ss, show j = s0 + (j - s0) by omega, runSteps_add, es0, Except.ok_bind]
        exact ej
      · simp [Behavior.Refines]
  · -- Both calls halt before running.
    rcases hb with ⟨n, h, e, rfl⟩ | ⟨hall, _⟩
    · simp only [stateAt, eit, Except.error_bind, Except.error.injEq] at e
      subst e
      exact ⟨hs.behavior, ⟨oracle', .inl ⟨0, hs, by simp [stateAt, eis, Except.error_bind], rfl⟩⟩,
        href⟩
    · obtain ⟨m, e⟩ := hall 0
      simp [stateAt, eit, Except.error_bind] at e

end Fir
