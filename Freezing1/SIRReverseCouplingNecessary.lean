module

public import Freezing1.SIRReverseCouplingFormulation

/-! A necessary unconditional probability bound for the genuine source
coupling. This does not assert that the coupling exists or that a reverse
conditional transition probability is bounded by epsilon. -/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Classical

theorem iid_negative_coordinate_probability (ε : unitInterval) (j : ℕ) :
    (ForwardAnnealed.iidSignLaw (unitInterval.symm ε)) {x | x j = false} =
      (unitInterval.toNNReal ε : ℝ≥0∞) := by
  have hmap := (ForwardAnnealed.iidSignLaw_coordinate (unitInterval.symm ε) j).map_eq
  calc
    _ = ((ForwardAnnealed.iidSignLaw (unitInterval.symm ε)).map (fun x => x j)) {false} :=
      (Measure.map_apply (measurable_pi_apply j) (measurableSet_singleton false)).symm
    _ = (ForwardAnnealed.signLaw (unitInterval.symm ε)) {false} := by rw [hmap]
    _ = _ := by simp [ForwardAnnealed.signLaw, bernoulliMeasure_def]

theorem SourceReverseIidCoupling.bad_coordinate_le (rate : ℝ≥0) (n : ℕ) (ε : unitInterval)
    (hc : SourceReverseIidCoupling rate n ε) (j : ℕ) :
    (countsFullLaw rate n) (sourceReverseBadEvent rate n ε j) ≤
      (unitInterval.toNNReal ε : ℝ≥0∞) := by
  obtain ⟨γ, hfirst, hsecond, hdom⟩ := hc
  have haux : MeasurableSet {x : SignSequence | x j = false} :=
    ((measurable_pi_apply j).eq measurable_const).setOf
  have hle :
      ((γ : Measure ((ℕ → Counts) × SignSequence)).map Prod.fst)
          (sourceReverseBadEvent rate n ε j) ≤
        ((γ : Measure ((ℕ → Counts) × SignSequence)).map Prod.snd) {x | x j = false} := by
    rw [Measure.map_apply measurable_fst (measurableSet_sourceReverseBadEvent rate n ε j),
      Measure.map_apply measurable_snd haux]
    exact measure_mono_ae (hdom.mono fun p hp hbad => hp j hbad)
  rw [hfirst, hsecond, iid_negative_coordinate_probability] at hle
  exact hle

end Freezing1.SIR
