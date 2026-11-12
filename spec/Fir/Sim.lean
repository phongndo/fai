import Fir.Space

/-!
# Simulation

The tool for proving that one function refines another: relate the target machine's states to
the source machine's, and show that each target step is matched by source steps.

`Simulation.refines` turns a step-by-step simulation into `Func.Refines`. It handles everything
about whole runs (halting, divergence through loops or jumps, and `progress` loops and blocks
that never exit), so a proof about a rewrite only reasons about single steps.

Each target step is matched by one or more source steps (a source may take extra steps, as when
it runs a store the target deleted), or by the source halting with UB or getting stuck, after
which anything goes, provided the target has already matched the source's events. Matching source
states must agree with the target on which frames are `progress` loops, so a target that never
leaves such a loop has a source that never leaves one either. Related states must have traces
that match event by event, so the traces of whole runs do too, whether they are finite or
infinite.
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

/-- From `m`, the source halts with an outcome that every target outcome refines (UB or stuck),
after events that the target's events so far, `tt`, refine one by one: the target has already done
everything the source did before its UB, so it may do anything from here. Or the source reaches an
undecided choice, which `Func.Decided` rules out. -/
def Escapes (tt : List Event) (m : Machine) : Prop :=
  ∃ j mj h, runSteps j m = .ok mj ∧ step mj = .error h ∧
    (h.outcome = .ambiguous ∨ (h.outcome.Absorbing ∧ Events.Refines tt mj.core.trace))

theorem Escapes.back {tt : List Event} {s : Nat} {m m' : Machine} (hs : runSteps s m = .ok m') :
    Escapes tt m' → Escapes tt m
  | ⟨j, mj, h, e, sj, hb⟩ => ⟨s + j, mj, h, by rw [runSteps_add, hs, Except.ok_bind]; exact e, sj, hb⟩

/-- The source escapes in its next step, with no new events. -/
theorem Escapes.one {tt : List Event} {m : Machine} {h : Halt} (e : runSteps 1 m = .error h)
    (hb : h.outcome.Absorbing ∨ h.outcome = .ambiguous) (htt : Events.Refines tt m.core.trace) :
    Escapes tt m := by
  rw [runSteps_one] at e
  rcases hb with hb | hb
  · exact ⟨0, m, h, rfl, e, .inr ⟨hb, htt⟩⟩
  · exact ⟨0, m, h, rfl, e, .inl hb⟩

/-- How source state `ms` matches target state `mt`'s next step. If the target steps to `mt'`,
the source takes `k + 1` steps to a state related to `mt'`, and the states it passes through
have the same `progress` loops as `mt`. If the target halts, the source halts from a later state
with a behavior the target's refines. Either way, the source may instead escape. -/
def StepMatch (R : Machine → Machine → Prop) (mt ms : Machine) : Prop :=
  (∀ mt', step mt = .ok mt' → Escapes mt.core.trace ms ∨
    ∃ k ms', runSteps (k + 1) ms = .ok ms' ∧ R mt' ms' ∧
      ∀ j mj, j ≤ k → runSteps j ms = .ok mj → mj.shape = mt.shape) ∧
  (∀ ht, step mt = .error ht → Escapes mt.core.trace ms ∨
    ∃ j mj hs, runSteps j ms = .ok mj ∧ step mj = .error hs ∧
      (Behavior.fin mt.core.trace ht.outcome).Refines (.fin mj.core.trace hs.outcome))

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
source state before it has the same `progress` loops as some target state so far. Or the source
escapes, below the target's events after some `i ≤ n` steps. -/
theorem Simulation.run {R : Machine → Machine → Prop} (sim : Simulation R) {mt ms : Machine}
    (hR : R mt ms) (n : Nat) {mtn : Machine} (e : runSteps n mt = .ok mtn) :
    (∃ i mti, i ≤ n ∧ runSteps i mt = .ok mti ∧ Escapes mti.core.trace ms) ∨
    ∃ s msn, n ≤ s ∧ runSteps s ms = .ok msn ∧ R mtn msn ∧
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
      rcases ih en with ⟨i, mti, hi, ei, hesc⟩ | ⟨s, msn, hns, es, hR', cover⟩
      · exact .inl ⟨i, mti, by omega, ei, hesc⟩
      rcases (sim _ _ hR').1 mtn e with hesc | ⟨k, ms', ek, hR'', inter⟩
      · exact .inl ⟨n, mtn0, by omega, en, hesc.back es⟩
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
  (∃ hs, is = .error hs ∧ (hs.outcome.Absorbing ∨ hs.outcome = .ambiguous)) ∨
  (∃ mt ms, it = .ok mt ∧ is = .ok ms ∧ R mt ms) ∨
  (∃ ht hs, it = .error ht ∧ is = .error hs ∧ ht.outcome.Refines hs.outcome)

theorem inProgressLoopAt_of_shape {m m' : Machine} {d : Nat} (h : m.shape = m'.shape) :
    m'.inProgressLoopAt d → m.inProgressLoopAt d := by
  simp only [Machine.inProgressLoopAt, h]
  exact id

/-! ## Traces of runs -/

/-- Along one run, an earlier state's trace is a prefix of a later one's. -/
theorem runSteps_trace_le {m a b : Machine} {i j : Nat} (ei : runSteps i m = .ok a)
    (ej : runSteps j m = .ok b) (hij : i ≤ j) : a.core.trace <+: b.core.trace := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [runSteps_add, ei, Except.ok_bind] at ej
  exact runSteps_trace ej

/-- Along one run, any two states' traces agree where both have an event. -/
theorem runSteps_trace_agree {m a b : Machine} {i j k : Nat} {x y : Event}
    (ei : runSteps i m = .ok a) (ej : runSteps j m = .ok b) (hx : a.core.trace[k]? = some x)
    (hy : b.core.trace[k]? = some y) : x = y := by
  rcases Nat.le_total i j with h | h
  · obtain ⟨t, ht⟩ := runSteps_trace_le ei ej h
    rw [← ht, getElem?_append_some hx] at hy
    exact Option.some.inj hy
  · obtain ⟨t, ht⟩ := runSteps_trace_le ej ei h
    rw [← ht, getElem?_append_some hy] at hx
    exact (Option.some.inj hx).symm

/-- A run that halts after state `n` has no state after it. -/
theorem runSteps_le_of_halt {m a b : Machine} {n i : Nat} {h : Halt} (en : runSteps n m = .ok a)
    (sh : step a = .error h) (ei : runSteps i m = .ok b) : i ≤ n := by
  refine Nat.le_of_not_lt fun hlt => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  rw [show n + k + 1 = (n + 1) + k by omega, runSteps_add, runSteps_add, en, Except.ok_bind,
    runSteps_one, sh, Except.error_bind] at ei
  cases ei

/-- What a behavior's trace starts with: a finite trace has `tr` as a prefix; an infinite one
agrees with it on every event `tr` has. -/
def Behavior.Extends : Behavior → List Event → Prop
  | .fin es _, tr => tr <+: es
  | .inf es, tr => ∀ k e, tr[k]? = some e → es k = e

/-- A behavior whose trace starts with events that refine the source's, followed by UB in the
source, refines it. -/
theorem Behavior.Refines.of_extends {b : Behavior} {tr es : List Event} {o : Outcome}
    (hx : b.Extends tr) (h : Events.Refines tr es) (ho : o.Absorbing) : b.Refines (.fin es o) := by
  cases b with
  | fin et ot =>
    obtain ⟨post, rfl⟩ := hx
    exact .inr ⟨ho, tr, post, rfl, h⟩
  | inf et =>
    refine ⟨ho, fun k e he => ?_⟩
    obtain ⟨a, ha, hae⟩ := Forall2.getElem? h he
    rw [hx k a ha]
    exact hae

theorem Forall2.getElem?_left {r : α → β → Prop} : ∀ {as : List α} {bs : List β},
    Forall2 r as bs → ∀ {i : Nat} {a : α}, as[i]? = some a → ∃ b, bs[i]? = some b ∧ r a b
  | [], [], _, _, _, e => by simp at e
  | _ :: _, b :: _, ⟨hab, _⟩, 0, _, e => by simp at e; subst e; exact ⟨b, rfl, hab⟩
  | _ :: _, _ :: _, ⟨_, h⟩, i + 1, _, e => by
    simpa using Forall2.getElem?_left h (i := i) (by simpa using e)

/-- **The simulation theorem.** A simulation from every starting state, whose related states have
traces that match event by event, proves refinement, for a source that never reaches an undecided
choice. The source may use different oracle answers than the target; the world is the same. -/
theorem Simulation.refines {R : Machine → Machine → Prop} (sim : Simulation R)
    (htr : ∀ mt ms, R mt ms → Events.Refines mt.core.trace ms.core.trace) {mod : Module}
    {tgt src : Func}
    (init : ∀ oracle world args, ∃ oracle',
      InitMatch R (Machine.init oracle world mod tgt args) (Machine.init oracle' world mod src args))
    (dec : src.Decided mod) : tgt.Refines mod src := by
  intro world hw args b ⟨oracle, hb⟩
  obtain ⟨oracle', hinit⟩ := init oracle world args
  -- A source run that halts from a running state.
  have halts : ∀ n m h, stateAt oracle' world mod src args n = .ok m → step m = .error h →
      Behaves world mod src args (.fin m.core.trace h.outcome) :=
    fun n m h e sh => ⟨oracle', .inl (.inr ⟨n, m, h, e, sh, rfl, rfl⟩)⟩
  have notAmb : ∀ es, ¬ Behaves world mod src args (.fin es .ambiguous) := dec world hw args
  rcases hinit with ⟨hs, eis, hesc⟩ | ⟨mt, ms, eit, eis, hR⟩ | ⟨ht, hs, eit, eis, href⟩
  · -- The source fails to start, with UB.
    have hsb : Behaves world mod src args (.fin [] hs.outcome) :=
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
    -- Where the target's trace starts.
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
    -- A source escape matches anything the target does.
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
    have run : ∀ n mtn, runSteps n mt = .ok mtn → ∃ s msn, n ≤ s ∧ runSteps s ms = .ok msn ∧
        R mtn msn ∧ ∀ j mj, j < s → runSteps j ms = .ok mj →
          ∃ i mti, i ≤ n ∧ runSteps i mt = .ok mti ∧ mj.shape = mti.shape := by
      intro n mtn en
      rcases sim.run hR n en with ⟨i, mti, -, ei, he⟩ | h
      · exact absurd ⟨i, mti, ei, he⟩ hesc
      · exact h
    -- A target that runs forever has a source that does too.
    have forever : RunsForever oracle world mod tgt args → RunsForever oracle' world mod src args := by
      intro hall n
      obtain ⟨mtn, en⟩ := hall n
      rw [st] at en
      obtain ⟨s, msn, hns, es, -⟩ := run n mtn en
      obtain ⟨y, ey⟩ := runSteps_ok_of_le es hns
      exact ⟨y, by rw [ss]; exact ey⟩
    cases b with
    | fin es o =>
      rcases hb with (⟨h, e, -⟩ | ⟨n, m, h, e, sh, rfl, rfl⟩) | ⟨hall, ⟨hpre, N, mN, eN, rfl⟩, hcase⟩
      · rw [eit] at e; cases e
      · -- The target halts.
        rw [st] at e
        obtain ⟨s, msn, _, es, hR', _⟩ := run n m e
        rcases (sim _ _ hR').2 h sh with hesc' | ⟨j, mj, hs, ej, sj, href⟩
        · exact absurd ⟨n, m, e, hesc'.back es⟩ hesc
        refine ⟨_, halts (s + j) mj hs ?_ sj, href⟩
        rw [ss, runSteps_add, es, Except.ok_bind]
        exact ej
      · -- The target runs forever with finitely many events, so the source does too.
        rw [st] at eN
        obtain ⟨s0, ms0, _, es0, hR0, _⟩ := run N mN eN
        have hrel0 := htr _ _ hR0
        have sall := forever hall
        -- The source's events stop where the target's do.
        have sfin : FinalTrace oracle' world mod src args ms0.core.trace := by
          refine ⟨fun k mk ek => ?_, s0, ms0, by rw [ss]; exact es0, rfl⟩
          rw [ss] at ek
          rcases Nat.le_total k s0 with hk | hk
          · exact runSteps_trace_le ek es0 hk
          · obtain ⟨mtk, etk⟩ := hall k
            rw [st] at etk
            obtain ⟨sk, msk, hksk, esk, hRk, _⟩ := run k mtk etk
            have hle : mk.core.trace.length ≤ ms0.core.trace.length := by
              have h1 := (runSteps_trace_le ek esk hksk).length_le
              have h2 := (hpre k mtk (by rw [st]; exact etk)).length_le
              rw [Forall2.length_eq (htr _ _ hRk), Forall2.length_eq hrel0] at h2
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
        · -- A target stuck in a `progress` loop has a source stuck in one too.
          exfalso
          apply hsp
          have tall : ∀ n, ∃ m, runSteps n mt = .ok m := fun n => by
            obtain ⟨m, e⟩ := hall n
            exact ⟨m, by rw [← st]; exact e⟩
          obtain ⟨mtN, eN', _⟩ := hN N (Nat.le_refl _)
          rw [st] at eN'
          obtain ⟨s0, ms0, _, es0, hR0, _⟩ := run N mtN eN'
          refine ⟨s0, d, fun j hj => ?_⟩
          obtain ⟨x, ex⟩ := tall (N + (j - s0 + 1))
          rw [runSteps_add, eN', Except.ok_bind] at ex
          rcases sim.run hR0 (j - s0 + 1) ex with ⟨i, mti, -, ei, he⟩ | ⟨s', _, hs', es', _, cover⟩
          · exact absurd ⟨N + i, mti, by rw [runSteps_add, eN', Except.ok_bind]; exact ei,
              he.back es0⟩ hesc
          obtain ⟨mj, ej⟩ := runSteps_ok_of_le es' (show j - s0 ≤ s' by omega)
          obtain ⟨i, mti, _, ei, hsh⟩ := cover (j - s0) mj (by omega) ej
          obtain ⟨m', e', hp⟩ := hN (N + i) (by omega)
          rw [st, runSteps_add, eN', Except.ok_bind, ei, Except.ok.injEq] at e'
          subst e'
          refine ⟨mj, ?_, inProgressLoopAt_of_shape hsh hp⟩
          rw [ss, show j = s0 + (j - s0) by omega, runSteps_add, es0, Except.ok_bind]
          exact ej
        · trivial
    | inf es =>
      -- The target has infinitely many events, so the source does too, one for one.
      obtain ⟨hall, hev⟩ := hb
      have hsrc : ∀ i, ∃ e, (es i).Refines e ∧ EventAt oracle' world mod src args i e := by
        intro i
        obtain ⟨n, m, en, hi⟩ := hev i
        rw [st] at en
        obtain ⟨s, msn, _, es', hR', _⟩ := run n m en
        obtain ⟨e, he, hre⟩ := Forall2.getElem?_left (htr _ _ hR') hi
        exact ⟨e, hre, s, msn, by rw [ss]; exact es', he⟩
      refine ⟨.inf fun i => (hsrc i).choose, ⟨oracle', forever hall, fun i => (hsrc i).choose_spec.2⟩,
        fun i => (hsrc i).choose_spec.1⟩
  · -- Both calls halt before running.
    cases b with
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
