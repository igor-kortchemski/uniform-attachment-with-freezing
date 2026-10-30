module

import Freezing1.SIRReverseHalfWindow

/-! Author's explicit actual-endpoint and source half-window checks. -/

open Filter MeasureTheory
open scoped Topology BigOperators NNReal
open Freezing1 Freezing1.SIR

example (n : ℕ) : Measurable (boundedExtinctionIndex n) := measurable_boundedExtinctionIndex n

example (rate : ℝ≥0) (n : ℕ) : ∀ᵐ H ∂countsFullLaw rate n,
    boundedExtinctionIndex n H ≤ 2 * n + 1 ∧
      (H (boundedExtinctionIndex n H)).infectious = 0 ∧
      ∀ i < boundedExtinctionIndex n H, 0 < (H i).infectious :=
  countsFullLaw_boundedExtinctionIndex_firstZero rate n

example (H : ℕ → Counts) (n τ : ℕ) :
    intervalBirthCharge H (τ - min (n / 2) (τ - n)) τ =
      ∑ j ∈ Finset.Icc 1 (min (n / 2) (τ - n)),
        if (H (τ - j + 1)).susceptible < (H (τ - j)).susceptible then
          1 / ((H (τ - j)).infectious : ℝ) else 0 :=
  intervalBirthCharge_lastHalf_reverse H n τ

example (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real {H |
      ε ≤ intervalBirthCharge H n
        (boundedExtinctionIndex n H - min (n / 2) (boundedExtinctionIndex n H - n)) /
          Real.log (n : ℝ)}) atTop (𝓝 0) :=
  countsFullLaw_actualHalfWindow_early_tendsto_zero rate hstrong hε

#print axioms measurable_boundedExtinctionIndex
#print axioms countsFullLaw_boundedExtinctionIndex_firstZero
#print axioms reverseHalfWindow_early_charge_le_all
#print axioms countsFullLaw_reverseHalfWindow_early_tendsto_zero
#print axioms intervalBirthCharge_lastHalf_reverse
#print axioms countsFullLaw_actualHalfWindow_early_tendsto_zero
#print axioms countsFullLaw_late_charge_reduced_to_lastHalf
