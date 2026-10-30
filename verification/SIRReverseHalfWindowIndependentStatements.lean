module

import Freezing1.SIRReverseHalfWindow

open Filter MeasureTheory
open Freezing1 Freezing1.SIR
open scoped Classical NNReal BigOperators Topology

-- Independently reconstructed carrier: actual first zero, with no survival premise.
example (r : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂countsFullLaw r n,
      boundedExtinctionIndex n H ≤ 2 * n + 1 ∧
      (H (boundedExtinctionIndex n H)).infectious = 0 ∧
      ∀ i < boundedExtinctionIndex n H, 0 < (H i).infectious :=
  countsFullLaw_boundedExtinctionIndex_firstZero r n

-- The finite reversed sum has exactly min(floor(n/2),tau-n) terms.
example (H : ℕ → Counts) (n τ : ℕ) :
    intervalBirthCharge H (τ - min (n / 2) (τ - n)) τ =
      ∑ j ∈ Finset.Icc 1 (min (n / 2) (τ - n)),
        if (H (τ - j + 1)).susceptible < (H (τ - j)).susceptible then
          1 / ((H (τ - j)).infectious : ℝ) else 0 :=
  intervalBirthCharge_lastHalf_reverse H n τ

-- The only event in the deterministic bound is a true triangle-profile event.
example (H : ℕ → Counts) {n τ : ℕ} (hn : 8 ≤ n) (hτ : τ ≤ 2 * n + 1)
    (hgood : ∀ k ≤ 2 * n,
      |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)| < (n : ℝ) / 8) :
    (∑ i ∈ Finset.Ico n (τ - min (n / 2) (τ - n)),
      if (H (i + 1)).susceptible < (H i).susceptible then
        1 / ((H i).infectious : ℝ) else 0) ≤ 16 :=
  reverseHalfWindow_early_charge_le_all H hn hτ hgood

-- The early actual charge is negligible, by the genuine stopped fluid theorem.
example (r : ℕ → ℝ≥0)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * r n) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (countsFullLaw (r n) n).real {H |
      ε ≤ intervalBirthCharge H n
          (boundedExtinctionIndex n H -
            min (n / 2) (boundedExtinctionIndex n H - n)) / Real.log (n : ℝ)})
      atTop (𝓝 0) :=
  countsFullLaw_actualHalfWindow_early_tendsto_zero r hr hε

-- This is explicitly a sufficiency reduction, not a proof of its last-window premise.
example (r : ℕ → ℝ≥0)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * r n) atTop atTop)
    (hlast : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
      (countsFullLaw (r n) n).real {H |
        ε ≤ intervalBirthCharge H
            (boundedExtinctionIndex n H - min (n / 2) (boundedExtinctionIndex n H - n))
            (boundedExtinctionIndex n H) / Real.log (n : ℝ)}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
      (countsFullLaw (r n) n).real {H |
        ε ≤ intervalBirthCharge H n (boundedExtinctionIndex n H) / Real.log (n : ℝ)})
      atTop (𝓝 0) :=
  countsFullLaw_late_charge_reduced_to_lastHalf r hr hlast

#print axioms boundedExtinctionIndex
#print axioms measurable_boundedExtinctionIndex
#print axioms countsFullLaw_boundedExtinctionIndex_firstZero
#print axioms intervalBirthCharge_reverse
#print axioms intervalBirthCharge_lastHalf_reverse
#print axioms reverseHalfWindow_early_charge_le_all
#print axioms countsFullLaw_reverseHalfWindow_early_tendsto_zero
#print axioms countsFullLaw_actualHalfWindow_early_tendsto_zero
#print axioms countsFullLaw_late_charge_reduced_to_lastHalf
#print axioms printed_reverse_attachment_identity_counterexample
