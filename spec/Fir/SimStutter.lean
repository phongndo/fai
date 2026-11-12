import Fir.Sim

/-!
# Simulation with expansion

`Simulation.refines` matches every target step with one or more source steps. A lowering does
the opposite too: it expands one source op into several target ops, so several target steps match
one source step. `SimulationS.refines` allows that: a target step may also be matched by no
source step at all (the target *stutters*), provided the related states' index, a natural number,
decreases. So the target can't stutter forever, and a target that runs forever has a source that
does too.

The proof follows `Simulation.refines`, replacing "the source has taken at least as many steps as
the target" by `SimulationS.progress`: from related states, a target that runs forever eventually
makes the source take a step.
-/

namespace Fir

/-- `StepMatch` for states related at index `n`, where a target step may also be matched by no
source step if the index decreases. -/
def StepMatchS (R : Nat → Machine → Machine → Prop) (n : Nat) (mt ms : Machine) : Prop :=
  (∀ mt', step mt = .ok mt' → Escapes mt.core.trace ms ∨ (∃ n', n' < n ∧ R n' mt' ms) ∨
    ∃ k ms', runSteps (k + 1) ms = .ok ms' ∧ (∃ n', R n' mt' ms') ∧
      ∀ j mj, j ≤ k → runSteps j ms = .ok mj → mj.shape = mt.shape) ∧
  (∀ ht, step mt = .error ht → Escapes mt.core.trace ms ∨
    ∃ j mj hs, runSteps j ms = .ok mj ∧ step mj = .error hs ∧
      (Behavior.fin mt.core.trace ht.outcome).Refines (.fin mj.core.trace hs.outcome))

/-- Every step match is one with stuttering. -/
theorem StepMatch.stutter {R : Nat → Machine → Machine → Prop} {n : Nat} {mt ms : Machine}
    (h : StepMatch (fun mt ms => ∃ n, R n mt ms) mt ms) : StepMatchS R n mt ms :=
  ⟨fun mt' e => (h.1 mt' e).imp_right .inr, h.2⟩

/-- `R` relates target states to source states at an index, and every related pair matches. -/
def SimulationS (R : Nat → Machine → Machine → Prop) : Prop :=
  ∀ n mt ms, R n mt ms → StepMatchS R n mt ms

/-- After `n` target steps, the source has run some `s` steps to a related state, and every
source state before it has the same `progress` loops as some target state so far. Or the source
escapes, below the target's events after some `i ≤ n` steps. -/
theorem SimulationS.run {R : Nat → Machine → Machine → Prop} (sim : SimulationS R)
    {mt ms : Machine} {v : Nat} (hR : R v mt ms) (n : Nat) {mtn : Machine}
    (e : runSteps n mt = .ok mtn) :
    (∃ i mti, i ≤ n ∧ runSteps i mt = .ok mti ∧ Escapes mti.core.trace ms) ∨
    ∃ s msn, runSteps s ms = .ok msn ∧ (∃ v', R v' mtn msn) ∧
      ∀ j mj, j < s → runSteps j ms = .ok mj →
        ∃ i mti, i ≤ n ∧ runSteps i mt = .ok mti ∧ mj.shape = mti.shape := by
  induction n generalizing mtn with
  | zero =>
    simp only [runSteps, Except.ok.injEq] at e
    subst e
    exact .inr ⟨0, ms, rfl, ⟨v, hR⟩, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    rw [runSteps_add n 1] at e
    cases en : runSteps n mt with
    | error h => rw [en, Except.error_bind] at e; cases e
    | ok mtn0 =>
      rw [en, Except.ok_bind, runSteps_one] at e
      rcases ih en with ⟨i, mti, hi, ei, hesc⟩ | ⟨s, msn, es, ⟨v', hR'⟩, cover⟩
      · exact .inl ⟨i, mti, by omega, ei, hesc⟩
      rcases (sim _ _ _ hR').1 mtn e with hesc | ⟨n', -, hR''⟩ | ⟨k, ms', ek, hR'', inter⟩
      · exact .inl ⟨n, mtn0, by omega, en, hesc.back es⟩
      · exact .inr ⟨s, msn, es, ⟨n', hR''⟩, fun j mj hj ej =>
          let ⟨i, mti, hi, ei, hsh⟩ := cover j mj hj ej; ⟨i, mti, by omega, ei, hsh⟩⟩
      refine .inr ⟨s + (k + 1), ms', by rw [runSteps_add, es, Except.ok_bind]; exact ek,
        hR'', ?_⟩
      intro j mj hj ej
      by_cases hjs : j < s
      · obtain ⟨i, mti, hi, ei, hsh⟩ := cover j mj hjs ej
        exact ⟨i, mti, by omega, ei, hsh⟩
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hjs)
        rw [runSteps_add, es, Except.ok_bind] at ej
        exact ⟨n, mtn0, by omega, en, inter j' mj (by omega) ej⟩

/-- Every source state before step `s` has the same `progress` loops as some target state up to
step `n`. -/
def Cover (mt ms : Machine) (n s : Nat) : Prop :=
  ∀ j mj, j < s → runSteps j ms = .ok mj →
    ∃ i mti, i ≤ n ∧ runSteps i mt = .ok mti ∧ mj.shape = mti.shape

/-- From related states, a target that runs forever without the source escaping makes the
source take at least one step: the target can stutter only as long as the measure decreases. -/
theorem SimulationS.progress {R : Nat → Machine → Machine → Prop} (sim : SimulationS R) :
    ∀ (v : Nat) {mt ms : Machine}, R v mt ms →
    (∀ n, ∃ m, runSteps n mt = .ok m) →
    (¬ ∃ i mti, runSteps i mt = .ok mti ∧ Escapes mti.core.trace ms) →
    ∃ n mtn s msn, 0 < s ∧ runSteps n mt = .ok mtn ∧ runSteps s ms = .ok msn ∧
      (∃ v', R v' mtn msn) ∧ Cover mt ms n s := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
  intro mt ms hR hall hno
  obtain ⟨mt1, e1⟩ := hall 1
  rw [runSteps_one] at e1
  have hall' : ∀ n, ∃ m, runSteps n mt1 = .ok m := fun n => by
    obtain ⟨m, e⟩ := hall (1 + n)
    rw [runSteps_add, runSteps_one, e1, Except.ok_bind] at e
    exact ⟨m, e⟩
  have run1 : runSteps 1 mt = .ok mt1 := by rw [runSteps_one, e1]
  rcases (sim _ _ _ hR).1 mt1 e1 with hesc | ⟨v1, hlt, hR1⟩ | ⟨k, ms', ek, hR1, inter⟩
  · exact absurd ⟨0, mt, rfl, hesc⟩ hno
  · obtain ⟨n, mtn, s, msn, hs, en, es, hRn, cover⟩ := ih _ hlt hR1 hall'
      fun ⟨i, mti, ei, he⟩ => hno ⟨1 + i, mti, by rw [runSteps_add, run1, Except.ok_bind]; exact ei, he⟩
    refine ⟨1 + n, mtn, s, msn, hs, by rw [runSteps_add, run1, Except.ok_bind]; exact en, es, hRn,
      fun j mj hj ej => ?_⟩
    obtain ⟨i, mti, hi, ei, hsh⟩ := cover j mj hj ej
    exact ⟨1 + i, mti, by omega, by rw [runSteps_add, run1, Except.ok_bind]; exact ei, hsh⟩
  · refine ⟨1, mt1, k + 1, ms', by omega, run1, ek, hR1, fun j mj hj ej => ?_⟩
    exact ⟨0, mt, by omega, rfl, inter j mj (by omega) ej⟩

/-- From related states, a target that runs forever without the source escaping makes the
source take at least `S` steps, for any `S`. -/
theorem SimulationS.far {R : Nat → Machine → Machine → Prop} (sim : SimulationS R) :
    ∀ (S : Nat) {mt ms : Machine}, (∃ v, R v mt ms) →
    (∀ n, ∃ m, runSteps n mt = .ok m) →
    (¬ ∃ i mti, runSteps i mt = .ok mti ∧ Escapes mti.core.trace ms) →
    ∃ n mtn s msn, S ≤ s ∧ runSteps n mt = .ok mtn ∧ runSteps s ms = .ok msn ∧
      (∃ v', R v' mtn msn) ∧ Cover mt ms n s
  | 0, mt, ms, hR, _, _ =>
    ⟨0, mt, 0, ms, Nat.le_refl _, rfl, rfl, hR, fun _ _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | S + 1, mt, ms, ⟨v, hR⟩, hall, hno => by
    obtain ⟨n, mtn, s, msn, hs, en, es, hRn, cover⟩ := sim.progress _ hR hall hno
    have hall' : ∀ i, ∃ m, runSteps i mtn = .ok m := fun i => by
      obtain ⟨m, e⟩ := hall (n + i)
      rw [runSteps_add, en, Except.ok_bind] at e
      exact ⟨m, e⟩
    have hno' : ¬ ∃ i mti, runSteps i mtn = .ok mti ∧ Escapes mti.core.trace msn :=
      fun ⟨i, mti, ei, he⟩ =>
        hno ⟨n + i, mti, by rw [runSteps_add, en, Except.ok_bind]; exact ei, he.back es⟩
    obtain ⟨n', mtn', s', msn', hs', en', es', hR', cover'⟩ := SimulationS.far sim S hRn hall' hno'
    refine ⟨n + n', mtn', s + s', msn', by omega, by rw [runSteps_add, en, Except.ok_bind]; exact en',
      by rw [runSteps_add, es, Except.ok_bind]; exact es', hR', fun j mj hj ej => ?_⟩
    by_cases hjs : j < s
    · obtain ⟨i, mti, hi, ei, hsh⟩ := cover j mj hjs ej
      exact ⟨i, mti, by omega, ei, hsh⟩
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hjs)
      rw [runSteps_add, es, Except.ok_bind] at ej
      obtain ⟨i, mti, hi, ei, hsh⟩ := cover' j' mj (by omega) ej
      exact ⟨n + i, mti, by omega, by rw [runSteps_add, en, Except.ok_bind]; exact ei, hsh⟩

/-- **The simulation theorem, with stuttering.** As `Simulation.refines`, for a simulation whose
target may take steps the source doesn't, as long as a measure decreases. -/
theorem SimulationS.refines {R : Nat → Machine → Machine → Prop} (sim : SimulationS R)
    (htr : ∀ n mt ms, R n mt ms → Events.Refines mt.core.trace ms.core.trace) {mod : Module}
    {tgt src : Func}
    (init : ∀ oracle world args, ∃ oracle', InitMatch (fun mt ms => ∃ n, R n mt ms)
      (Machine.init oracle world mod tgt args) (Machine.init oracle' world mod src args))
    (dec : src.Decided mod) : tgt.Refines mod src := by
  have htr' : ∀ mt ms, (∃ n, R n mt ms) → Events.Refines mt.core.trace ms.core.trace :=
    fun mt ms ⟨n, h⟩ => htr n mt ms h
  intro world hw args b ⟨oracle, hb⟩
  obtain ⟨oracle', hinit⟩ := init oracle world args
  have halts : ∀ n m h, stateAt oracle' world mod src args n = .ok m → step m = .error h →
      Behaves world mod src args (.fin m.core.trace h.outcome) :=
    fun n m h e sh => ⟨oracle', .inl (.inr ⟨n, m, h, e, sh, rfl, rfl⟩)⟩
  have notAmb : ∀ es, ¬ Behaves world mod src args (.fin es .ambiguous) := dec world hw args
  rcases hinit with ⟨hs, eis, hesc⟩ | ⟨mt, ms, eit, eis, ⟨v0, hR⟩⟩ | ⟨ht, hs, eit, eis, href⟩
  · have hsb : Behaves world mod src args (.fin [] hs.outcome) :=
      ⟨oracle', .inl (.inl ⟨hs, eis, rfl, rfl⟩)⟩
    rcases hesc with hab | hamb
    · refine ⟨_, hsb, .of_extends (tr := []) ?_ trivial hab⟩
      cases b with
      | fin => exact List.nil_prefix
      | inf => intro k e he; simp at he
    · exact absurd (hamb ▸ hsb) (notAmb [])
  · have st : ∀ n, stateAt oracle world mod tgt args n = runSteps n mt := fun n => by
      simp [stateAt, eit, Except.ok_bind]
    have ss : ∀ n, stateAt oracle' world mod src args n = runSteps n ms := fun n => by
      simp [stateAt, eis, Except.ok_bind]
    have hext : ∀ i mi, runSteps i mt = .ok mi → b.Extends mi.core.trace := by
      intro i mi ei
      cases b with
      | fin es o =>
        rcases hb with (⟨h, e, -⟩ | ⟨n, m, h, e, sh, rfl, -⟩) | ⟨-, ⟨hpre, -⟩, -⟩
        · rw [eit] at e; cases e
        · rw [st] at e
          exact runSteps_trace_le ei e (runSteps_le_of_halt e sh ei)
        · exact hpre i mi (by rw [st]; exact ei)
      | inf es =>
        intro k e he
        obtain ⟨n', m', e', hk⟩ := hb.2 k
        rw [st] at e'
        exact (runSteps_trace_agree ei e' he hk).symm
    have escaped : ∀ i mti, runSteps i mt = .ok mti → Escapes mti.core.trace ms →
        ∃ b', Behaves world mod src args b' ∧ b.Refines b' := by
      intro i mti ei ⟨j, mj, h, ej, sj, hb'⟩
      have hsb := halts j mj h (by rw [ss]; exact ej) sj
      rcases hb' with hamb | ⟨hab, hrel⟩
      · exact absurd (hamb ▸ hsb) (notAmb _)
      · exact ⟨_, hsb, .of_extends (hext i mti ei) hrel hab⟩
    by_cases hesc : ∃ i mti, runSteps i mt = .ok mti ∧ Escapes mti.core.trace ms
    · obtain ⟨i, mti, ei, he⟩ := hesc
      exact escaped i mti ei he
    have run : ∀ n mtn, runSteps n mt = .ok mtn → ∃ s msn, runSteps s ms = .ok msn ∧
        (∃ v, R v mtn msn) ∧ ∀ j mj, j < s → runSteps j ms = .ok mj →
          ∃ i mti, i ≤ n ∧ runSteps i mt = .ok mti ∧ mj.shape = mti.shape := by
      intro n mtn en
      rcases sim.run hR n en with ⟨i, mti, -, ei, he⟩ | h
      · exact absurd ⟨i, mti, ei, he⟩ hesc
      · exact h
    -- A target that runs forever takes the source arbitrarily far.
    have far : (∀ n, ∃ m, runSteps n mt = .ok m) → ∀ S, ∃ n mtn s msn, S ≤ s ∧
        runSteps n mt = .ok mtn ∧ runSteps s ms = .ok msn ∧ (∃ v, R v mtn msn) ∧
        Cover mt ms n s :=
      fun hall S => sim.far S ⟨v0, hR⟩ hall hesc
    have forever : RunsForever oracle world mod tgt args → RunsForever oracle' world mod src args := by
      intro hall n
      have hall' : ∀ n, ∃ m, runSteps n mt = .ok m := fun n => by
        obtain ⟨m, e⟩ := hall n
        exact ⟨m, by rw [← st]; exact e⟩
      obtain ⟨_, _, s, msn, hns, _, es, _, _⟩ := far hall' n
      obtain ⟨y, ey⟩ := runSteps_ok_of_le es hns
      exact ⟨y, by rw [ss]; exact ey⟩
    cases b with
    | fin es o =>
      rcases hb with (⟨h, e, -⟩ | ⟨n, m, h, e, sh, rfl, rfl⟩) | ⟨hall, ⟨hpre, N, mN, eN, rfl⟩, hcase⟩
      · rw [eit] at e; cases e
      · rw [st] at e
        obtain ⟨s, msn, es, ⟨v', hR'⟩, _⟩ := run n m e
        rcases (sim _ _ _ hR').2 h sh with hesc' | ⟨j, mj, hs, ej, sj, href⟩
        · exact absurd ⟨n, m, e, hesc'.back es⟩ hesc
        refine ⟨_, halts (s + j) mj hs ?_ sj, href⟩
        rw [ss, runSteps_add, es, Except.ok_bind]
        exact ej
      · have tall : ∀ n, ∃ m, runSteps n mt = .ok m := fun n => by
          obtain ⟨m, e⟩ := hall n
          exact ⟨m, by rw [← st]; exact e⟩
        rw [st] at eN
        obtain ⟨s0, ms0, es0, hR0, _⟩ := run N mN eN
        have hrel0 := htr' _ _ hR0
        have sall := forever hall
        have sfin : FinalTrace oracle' world mod src args ms0.core.trace := by
          refine ⟨fun k mk ek => ?_, s0, ms0, by rw [ss]; exact es0, rfl⟩
          rw [ss] at ek
          rcases Nat.le_total k s0 with hk | hk
          · exact runSteps_trace_le ek es0 hk
          · obtain ⟨nk, mtk, sk, msk, hksk, etk, esk, hRk, _⟩ := far tall k
            have hle : mk.core.trace.length ≤ ms0.core.trace.length := by
              have h1 := (runSteps_trace_le ek esk hksk).length_le
              have h2 := (hpre nk mtk (by rw [st]; exact etk)).length_le
              rw [Forall2.length_eq (htr' _ _ hRk), Forall2.length_eq hrel0] at h2
              exact Nat.le_trans h1 h2
            have hp := runSteps_trace_le es0 ek hk
            rw [hp.eq_of_length (Nat.le_antisymm hp.length_le hle)]
            exact List.prefix_refl _
        by_cases hsp : StuckInProgressLoop oracle' world mod src args
        · exact ⟨.fin ms0.core.trace (.ub .noProgress),
            ⟨oracle', Or.inr ⟨sall, sfin, .inl ⟨hsp, rfl⟩⟩⟩, Or.inl ⟨hrel0, trivial⟩⟩
        refine ⟨.fin ms0.core.trace .diverge, ⟨oracle', Or.inr ⟨sall, sfin, .inr ⟨hsp, rfl⟩⟩⟩,
          Or.inl ⟨hrel0, ?_⟩⟩
        rcases hcase with ⟨⟨N, d, hN⟩, rfl⟩ | ⟨_, rfl⟩
        · exfalso
          apply hsp
          obtain ⟨mtN, eN', _⟩ := hN N (Nat.le_refl _)
          rw [st] at eN'
          obtain ⟨s0, ms0, es0, hR0, _⟩ := run N mtN eN'
          have hallN : ∀ n, ∃ m, runSteps n mtN = .ok m := fun n => by
            obtain ⟨m, e⟩ := tall (N + n)
            rw [runSteps_add, eN', Except.ok_bind] at e
            exact ⟨m, e⟩
          have hnoN : ¬ ∃ i mti, runSteps i mtN = .ok mti ∧ Escapes mti.core.trace ms0 :=
            fun ⟨i, mti, ei, he⟩ =>
              hesc ⟨N + i, mti, by rw [runSteps_add, eN', Except.ok_bind]; exact ei, he.back es0⟩
          refine ⟨s0, d, fun j hj => ?_⟩
          obtain ⟨n', mtn', s', ms', hs', en', es', hR', cover⟩ :=
            sim.far (j - s0 + 1) hR0 hallN hnoN
          obtain ⟨mj, ej⟩ := runSteps_ok_of_le es' (show j - s0 ≤ s' by omega)
          have hj' : j - s0 < s' := by omega
          obtain ⟨i, mti, _, ei, hsh⟩ := cover (j - s0) mj hj' ej
          obtain ⟨m', e', hp⟩ := hN (N + i) (by omega)
          rw [st, runSteps_add, eN', Except.ok_bind, ei, Except.ok.injEq] at e'
          subst e'
          refine ⟨mj, ?_, inProgressLoopAt_of_shape hsh hp⟩
          rw [ss, show j = s0 + (j - s0) by omega, runSteps_add, es0, Except.ok_bind]
          exact ej
        · trivial
    | inf es =>
      obtain ⟨hall, hev⟩ := hb
      have hsrc : ∀ i, ∃ e, (es i).Refines e ∧ EventAt oracle' world mod src args i e := by
        intro i
        obtain ⟨n, m, en, hi⟩ := hev i
        rw [st] at en
        obtain ⟨s, msn, es', hR', _⟩ := run n m en
        obtain ⟨e, he, hre⟩ := Forall2.getElem?_left (htr' _ _ hR') hi
        exact ⟨e, hre, s, msn, by rw [ss]; exact es', he⟩
      refine ⟨.inf fun i => (hsrc i).choose, ⟨oracle', forever hall, fun i => (hsrc i).choose_spec.2⟩,
        fun i => (hsrc i).choose_spec.1⟩
  · cases b with
    | fin es o =>
      rcases hb with (⟨h, e, rfl, rfl⟩ | ⟨n, m, h, e, -⟩) | ⟨hall, -⟩
      · rw [eit] at e; cases e
        exact ⟨.fin [] hs.outcome, ⟨oracle', Or.inl (Or.inl ⟨hs, eis, rfl, rfl⟩)⟩,
          Or.inl ⟨trivial, href⟩⟩
      · simp [stateAt, eit, Except.error_bind] at e
      · obtain ⟨m, e⟩ := hall 0
        simp [stateAt, eit, Except.error_bind] at e
    | inf es =>
      obtain ⟨m, e⟩ := hb.1 0
      simp [stateAt, eit, Except.error_bind] at e

end Fir
