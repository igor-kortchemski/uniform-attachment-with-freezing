module

public import Freezing1.SIRClockChoiceTransition
public import Freezing1.SIRClockRaceSemantics

/-!
# The actual static-array residual law after every finite event word

The conditional product law is proved by induction from the original
independent preassigned array. It is not assumed as a memorylessness or
conditional-independence premise.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem restricted_pushforward_through {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (mu : Measure X) {f : X → Y} (hf : Measurable f) {phi : Y → Z} (hphi : Measurable phi)
    (E : Set X) (hE : MeasurableSet E) (A : Set Y) (hA : MeasurableSet A)
    (g : X → Z) (hg : ∀ x ∈ E ∩ f ⁻¹' A, g x = phi (f x)) :
    (mu.restrict (E ∩ f ⁻¹' A)).map g =
      (((mu.restrict E).map f).restrict A).map phi := by
  calc
    _ = (mu.restrict (E ∩ f ⁻¹' A)).map (phi ∘ f) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (hE.inter (hA.preimage hf))] with x hx
      exact hg x hx
    _ = _ := by
      rw [Measure.restrict_map hf hA, Measure.map_map hphi hf,
        Measure.restrict_restrict (hA.preimage hf), Set.inter_comm (f ⁻¹' A) E]

theorem frame_choice_of_population_eq {n : ℕ} {F : ClockFrame n} {z : PopulationState n}
    (hz : F.population = z) (omega : ClockArray n) :
    firstLiveClock F.population (remainingClock F omega) =
      relevantFirstLive z (fun c : RelevantCoordinate z => relevantClockView F omega c.val) := by
  subst z
  exact (relevantFirstLive_static F omega).symm

theorem clockPrefixEvent_choice {n : ℕ} {omega : ClockArray n} {w : ClockWord n}
    (hw : omega ∈ clockPrefixEvent n w) :
    preassignedEvent n omega w.length =
      relevantFirstLive (replayPopulation n w) (clockPrefixResidual n w omega) :=
  frame_choice_of_population_eq (population_eq_replay_of_prefix hw) omega

theorem clockPrefixEvent_cons_relevant (n : ℕ) (choice : ClockChoice n) (w : ClockWord n) :
    clockPrefixEvent n (choice :: w) = clockPrefixEvent n w ∩
      clockPrefixResidual n w ⁻¹' relevantChoiceEvent (replayPopulation n w) choice := by
  rw [clockPrefixEvent_cons]
  ext omega
  constructor
  · rintro ⟨hw, hc⟩
    refine ⟨hw, ?_⟩
    change relevantFirstLive (replayPopulation n w) (clockPrefixResidual n w omega) = choice
    rw [← clockPrefixEvent_choice hw]
    exact hc
  · rintro ⟨hw, hc⟩
    refine ⟨hw, ?_⟩
    change preassignedEvent n omega w.length = choice
    rw [clockPrefixEvent_choice hw]
    exact hc

theorem splitRelevantClocks_static {n : ℕ} {F : ClockFrame n}
    (hf : F.population.Valid) (omega : ClockArray n) :
    splitRelevantClocks F.population
      (fun c : RelevantCoordinate F.population => relevantClockView F omega c.val) =
      (frameLiveClockValues F omega, frameUnusedClockValues F omega) := by
  apply Prod.ext
  · funext c
    exact relevantClockView_of_live F omega c.property
  · funext c
    exact relevantClockView_of_unused hf omega c.property

theorem nextResidualForChoice_static {n : ℕ} {F : ClockFrame n} {z : PopulationState n}
    (hz : z.Valid) (hpop : F.population = z) (omega : ClockArray n) (choice : ClockChoice n)
    (hc : firstLiveClock F.population (remainingClock F omega) = choice) :
    (fun c : RelevantCoordinate (optionPopulationStep z choice) =>
      relevantClockView (clockFrameStep F omega) omega c.val) =
      nextResidualForChoice hz choice
        (fun c : RelevantCoordinate z => relevantClockView F omega c.val) := by
  subst z
  cases choice with
  | none =>
    rw [clockFrameStep, hc]
    rfl
  | some winner =>
    have hw := ((firstLiveClock_some_iff _ _ _).mp hc).1
    rw [clockFrameStep, hc]
    funext c
    simp only [nextResidualForChoice, dite_eq_left hw]
    change relevantClockView (advanceClockFrame F omega winner) omega c.val =
      (populationNextClockView hz hw (splitRelevantClocks F.population
        (fun c : RelevantCoordinate F.population => relevantClockView F omega c.val))).2 c
    rw [splitRelevantClocks_static hz omega]
    exact ((populationNextClockView_static hz omega hw).2 c).symm

theorem clockPrefixResidual_cons_of_event {n : ℕ} {omega : ClockArray n}
    {choice : ClockChoice n} {w : ClockWord n}
    (hw : omega ∈ clockPrefixEvent n (choice :: w)) :
    clockPrefixResidual n (choice :: w) omega =
      nextResidualForChoice (replayPopulation_valid n w) choice (clockPrefixResidual n w omega) := by
  have hp : omega ∈ clockPrefixEvent n w ∧ preassignedEvent n omega w.length = choice := by
    simpa only [clockPrefixEvent_cons, Set.mem_inter_iff, Set.mem_ofPred_eq] using hw
  unfold clockPrefixResidual
  simpa only [List.length_cons, preassignedRun, replayPopulation] using
    nextResidualForChoice_static (replayPopulation_valid n w)
      (population_eq_replay_of_prefix hp.1) omega choice hp.2

/-- The residual product after each actual finite word is derived from the
original independent array. The word mass is part of the conclusion. -/
theorem preassigned_clock_prefix_residual_law {r : ℝ} (hr : 0 < r) (n : ℕ) (w : ClockWord n) :
    ((preassignedClockLaw r n).restrict (clockPrefixEvent n w)).map (clockPrefixResidual n w) =
      clockWordWeight r n w • relevantClockLaw r (replayPopulation n w) := by
  induction w with
  | nil =>
    rw [clockPrefixEvent_nil, Measure.restrict_univ]
    change (preassignedClockLaw r n).map
      (fun omega : ClockArray n => fun c : RelevantCoordinate (initialPopulation n) =>
        relevantClockView (initialClockFrame n) omega c.val) =
      1 • relevantClockLaw r (initialPopulation n)
    rw [one_smul]
    exact preassigned_initial_relevant_law hr n
  | cons choice w ih =>
    rw [clockPrefixEvent_cons_relevant]
    have hh := restricted_pushforward_through (preassignedClockLaw r n)
      (measurable_clockPrefixResidual n w)
      (measurable_nextResidualForChoice (replayPopulation_valid n w) choice)
      (clockPrefixEvent n w) (measurableSet_clockPrefixEvent n w)
      (relevantChoiceEvent (replayPopulation n w) choice)
      (measurableSet_relevantChoiceEvent _ choice) (clockPrefixResidual n (choice :: w))
      (by
        intro omega homega
        apply clockPrefixResidual_cons_of_event
        rw [clockPrefixEvent_cons_relevant]
        exact homega)
    rw [hh, ih, Measure.restrict_smul,
      Measure.map_smul _ (measurable_nextResidualForChoice (replayPopulation_valid n w) choice).aemeasurable,
      relevant_clock_choice_transition (replayPopulation_valid n w) hr choice,
      smul_smul]
    rfl

theorem preassigned_clock_word_probability {r : ℝ} (hr : 0 < r) (n : ℕ) (w : ClockWord n) :
    preassignedClockLaw r n (clockPrefixEvent n w) = clockWordWeight r n w := by
  have : IsProbabilityMeasure (relevantClockLaw r (replayPopulation n w)) :=
    relevantClockLaw_probability hr _
  have hh := congrArg (fun mu : Measure (RelevantCoordinate (replayPopulation n w) → ℝ) => mu univ)
    (preassigned_clock_prefix_residual_law hr n w)
  rw [Measure.map_apply (measurable_clockPrefixResidual n w) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] at hh
  exact hh

end Freezing1.SIR
