module

import Freezing1.IidHalfSlope

/-! Author's exact-source checks; independence from a reversed epidemic
is deliberately not an input or conclusion. -/

open Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open Freezing1 Freezing1.ForwardAnnealed Freezing1.ForwardAnnealed.HalfSlope

example (p : unitInterval) {θ : ℝ} (hθ : 0 < θ)
    (hp : (1 - (p : ℝ)) * (Real.exp θ - 1) ≤ θ / 8) :
    (iidSignLaw p) {x | ¬∀ n : ℕ, (n : ℝ) / 2 ≤
      ∑ i ∈ Finset.range n, if x (i + 1) then (1 : ℝ) else -1} ≤
      ENNReal.ofReal (Real.exp (-θ / 8)) *
        (1 - ENNReal.ofReal (Real.exp (-θ / 8)))⁻¹ :=
  whole_time_failure_bound p hθ hp

example : Tendsto (fun ε : unitInterval => (iidSignLaw (unitInterval.symm ε)).real
    {x | ∀ n : ℕ, (n : ℝ) / 2 ≤
      ∑ i ∈ Finset.range n, if x (i + 1) then (1 : ℝ) else -1})
      (𝓝 (0 : unitInterval)) (𝓝 1) :=
  auxiliary_halfSlope_probability_tendsto_one

example (ε : unitInterval) (m : ℕ) :
    (∫ x, ∑ i ∈ Finset.range m, 2 / ((i : ℝ) + 1) *
        (if x (i + 1) then (0 : ℝ) else 1) ∂iidSignLaw (unitInterval.symm ε)) =
      2 * (ε : ℝ) * ∑ i ∈ Finset.range m, 1 / ((i : ℝ) + 1) :=
  expected_auxiliary_harmonic_failures ε m

#print axioms failures_hasLaw
#print axioms failure_tail
#print axioms whole_time_failure_bound
#print axioms whole_time_failure_small
#print axioms auxiliary_halfSlope_probability_tendsto_one
#print axioms expected_auxiliary_harmonic_failures
