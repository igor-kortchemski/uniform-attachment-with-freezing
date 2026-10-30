module

import Freezing1.IidHalfSlope

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal Classical

noncomputable section

namespace Freezing1.ForwardAnnealed.HalfSlope.IndependentStatementAudit

theorem positive_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, f j) = ∑ i ∈ Finset.range n, f (i + 1) := by
  symm
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    have hh := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i hi j hj he
    omega
  · intro j hj
    obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.mp hj
    exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rfl

/-- The exact source small-negative-probability walk, over positive indices. -/
example : Tendsto (fun ε : unitInterval => (iidSignLaw (unitInterval.symm ε)).real
    {x | ∀ n : ℕ, (n : ℝ) / 2 ≤
      ∑ j ∈ Finset.Icc 1 n, if x j then (1 : ℝ) else -1})
    (𝓝 (0 : unitInterval)) (𝓝 1) := by
  have he : {x : SignSequence | ∀ n : ℕ, (n : ℝ) / 2 ≤
      ∑ j ∈ Finset.Icc 1 n, if x j then (1 : ℝ) else -1} = good := by
    ext x
    simp only [Set.mem_ofPred_eq, good]
    exact forall_congr' (fun n => by rw [positive_sum])
  rw [he]
  exact auxiliary_halfSlope_probability_tendsto_one

/-- All-time control includes time zero; no cutoff or eventual-time event. -/
example (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : unitInterval, (ε : ℝ) ≤ ε₀ →
      1 - δ ≤ (iidSignLaw (unitInterval.symm ε)).real
        {x | ∀ n : ℕ, (n : ℝ) / 2 ≤
          ∑ i ∈ Finset.range n, if x (i + 1) then (1 : ℝ) else -1} := by
  obtain ⟨ε₀, hε₀, hbound⟩ := whole_time_good_small_error hδ
  refine ⟨ε₀, hε₀, fun ε hε => ?_⟩
  exact hbound (unitInterval.symm ε) (by simpa only [unitInterval.coe_symm_eq, sub_sub_cancel] using hε)

example (ε : unitInterval) (θ : ℝ) (hθ : 0 < θ)
    (hcoef : (ε : ℝ) * (Real.exp θ - 1) ≤ θ / 8) (n : ℕ) :
    (iidSignLaw (unitInterval.symm ε)).real
      {x | (∑ i ∈ Finset.range n, if x (i + 1) then (1 : ℝ) else -1) < (n : ℝ) / 2} ≤
        Real.exp (-θ / 8 * n) :=
  failure_tail (unitInterval.symm ε) hθ
    (by simpa only [unitInterval.coe_symm_eq, sub_sub_cancel] using hcoef) n

/-- The literal finite harmonic expectation with the source cutoff. -/
example (ε : unitInterval) (n : ℕ) :
    (∫ x, (∑ j ∈ Finset.Icc 1 (n / 2),
      2 / (j : ℝ) * (if x j then (0 : ℝ) else 1)) ∂iidSignLaw (unitInterval.symm ε)) =
        2 * (ε : ℝ) * ∑ j ∈ Finset.Icc 1 (n / 2), 1 / (j : ℝ) := by
  simp_rw [positive_sum]
  simpa only [failures, Nat.cast_add, Nat.cast_one] using
    expected_auxiliary_harmonic_failures ε (n / 2)

#print axioms failures_independent
#print axioms failures_hasLaw
#print axioms failure_tail
#print axioms whole_time_failure_bound
#print axioms whole_time_failure_small
#print axioms whole_time_good_small_error
#print axioms auxiliary_halfSlope_probability_tendsto_one
#print axioms expected_auxiliary_harmonic_failures

end Freezing1.ForwardAnnealed.HalfSlope.IndependentStatementAudit
