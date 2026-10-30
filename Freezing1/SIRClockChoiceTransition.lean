module

public import Freezing1.SIRClockEventWords

/-!
# Every event choice transports the current relevant product correctly

Legal events use the genuine exponential residual law; impossible events
have zero measure; absorption holds the same clocks. This unified statement
is the one-event input to the static event-word history induction.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def relevantClockLaw {n : ℕ} (r : ℝ) (z : PopulationState n) :
    Measure (RelevantCoordinate z → ℝ) :=
  Measure.pi (fun c : RelevantCoordinate z => expMeasure (clockSlotRate (n := n) r c.val))

theorem relevantClockLaw_probability {n : ℕ} {r : ℝ} (hr : 0 < r) (z : PopulationState n) :
    IsProbabilityMeasure (relevantClockLaw r z) := by
  have : ∀ c : RelevantCoordinate z,
      IsProbabilityMeasure (expMeasure (clockSlotRate (n := n) r c.val)) :=
    fun c => isProbabilityMeasure_expMeasure (clockSlotRate_pos hr c.val)
  unfold relevantClockLaw
  infer_instance

def relevantChoiceEvent {n : ℕ} (z : PopulationState n) (choice : ClockChoice n) :
    Set (RelevantCoordinate z → ℝ) := {x | relevantFirstLive z x = choice}

theorem measurableSet_relevantChoiceEvent {n : ℕ} (z : PopulationState n) (choice : ClockChoice n) :
    MeasurableSet (relevantChoiceEvent z choice) :=
  (measurableSet_singleton choice).preimage (measurable_relevantFirstLive z)

noncomputable def nextResidualForChoice {n : ℕ} {z : PopulationState n} (hz : z.Valid) :
    (choice : ClockChoice n) → (RelevantCoordinate z → ℝ) →
      (RelevantCoordinate (optionPopulationStep z choice) → ℝ)
  | none => fun x => x
  | some c => if hc : c ∈ z.liveSlots then
      fun x => (populationNextRelevantView hz hc x).2 else fun _ _ => 0

theorem measurable_nextResidualForChoice {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) (choice : ClockChoice n) : Measurable (nextResidualForChoice hz choice) := by
  cases choice with
  | none => exact measurable_id
  | some c =>
    by_cases hc : c ∈ z.liveSlots
    · simpa only [nextResidualForChoice, dite_eq_left hc, optionPopulationStep,
        Option.elim_some, Function.comp_def] using
        measurable_snd.comp (measurable_populationNextRelevantView hz hc)
    · simpa only [nextResidualForChoice, dite_eq_right hc, optionPopulationStep,
        Option.elim_some] using
        (measurable_const : Measurable (fun _ : RelevantCoordinate z → ℝ =>
          fun _ : RelevantCoordinate (populationStep z c) => (0 : ℝ)))

theorem relevant_clock_choice_transition {n : ℕ} {z : PopulationState n}
    (hz : z.Valid) {r : ℝ} (hr : 0 < r) (choice : ClockChoice n) :
    ((relevantClockLaw r z).restrict (relevantChoiceEvent z choice)).map
      (nextResidualForChoice hz choice) =
        clockChoiceWeight r z choice • relevantClockLaw r (optionPopulationStep z choice) := by
  cases choice with
  | none =>
    by_cases ha : z.active = ∅
    · have he : relevantChoiceEvent z none = univ := by
        ext x
        simp [relevantChoiceEvent, relevantFirstLive_none_of_active_empty ha]
      rw [he, Measure.restrict_univ]
      simp [nextResidualForChoice, clockChoiceWeight, ha, optionPopulationStep]
    · have hn : relevantClockLaw r z (relevantChoiceEvent z none) = 0 :=
        relevantFirstLive_none_null hz hr (Finset.nonempty_iff_ne_empty.mpr ha)
      rw [Measure.restrict_eq_zero.mpr hn, Measure.map_zero]
      simp [clockChoiceWeight, ha]
  | some c =>
    by_cases hc : c ∈ z.liveSlots
    · have he : relevantChoiceEvent z (some c) = populationRelevantWinner z hc := by
        ext x
        exact relevantFirstLive_some_iff z x hc
      rw [he]
      simpa only [nextResidualForChoice, dite_eq_left hc, clockChoiceWeight,
        ite_eq_left hc, optionPopulationStep, Option.elim_some, relevantClockLaw] using
        population_relevant_winner_residual_law hz hr hc
    · have he : relevantChoiceEvent z (some c) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact relevantFirstLive_not_invalid z x hc hx
      rw [he, Measure.restrict_empty, Measure.map_zero]
      simp [clockChoiceWeight, hc]

end Freezing1.SIR
