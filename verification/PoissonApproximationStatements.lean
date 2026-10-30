module

import Freezing1.PoissonApproximation
import Freezing1.BlockAttachmentParameters

open Freezing1 MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators Classical

-- Reconstruct the actual probability-event form, with the mean mismatch explicit.
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → unitInterval) (s : Finset ι) (rate : ℝ≥0) (E : Set ℕ) :
    |(bernoulliPartialSumLaw p s).real E - (poissonMeasure rate).real E| ≤
      (∑ i ∈ s, (p i : ℝ) ^ 2) + |(∑ i ∈ s, (p i : ℝ)) - (rate : ℝ)| :=
  bernoulliPartialSumLaw_poisson_parameter_event p s rate E

-- The exact interval is (a,b], whose Fin b coordinates are a ≤ i.val < b.
example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (a b : ℕ) (hbn : b ≤ n) :
    (∑ i ∈ (Finset.univ.filter fun i : Fin b => a ≤ i.val),
      (Reverse.attachmentParameter x n hn ⟨i.val, i.isLt.trans_le hbn⟩ : ℝ)) =
      ∑ j ∈ Finset.Ico a b, if x (j+1) then 1/(activeCount x (j+1) : ℝ) else 0 :=
  sum_blockAttachmentParameter x n hn a b hbn

#print axioms Freezing1.BoundedTestError
#print axioms Freezing1.unit_test_integrable
#print axioms Freezing1.unit_test_integral_bounds
#print axioms Freezing1.BoundedTestError.refl
#print axioms Freezing1.BoundedTestError.symm
#print axioms Freezing1.BoundedTestError.trans
#print axioms Freezing1.BoundedTestError.event
#print axioms Freezing1.BoundedTestError.conv_right
#print axioms Freezing1.BoundedTestError.conv_left
#print axioms Freezing1.bernoulliRate
#print axioms Freezing1.bernoulliRate_coe
#print axioms Freezing1.poisson_integral_ge_zero_one
#print axioms Freezing1.bernoulli_poisson_integral_sub_le
#print axioms Freezing1.bernoulli_poisson_boundedTestError
#print axioms Freezing1.BoundedTestError.mono
#print axioms Freezing1.poissonMeasure_zero_eq_dirac
#print axioms Freezing1.bernoulliPartialSumLaw_poisson_boundedTestError
#print axioms Freezing1.bernoulliPartialSumLaw_poisson_event
#print axioms Freezing1.boundedTestError_dirac_zero
#print axioms Freezing1.poisson_dirac_boundedTestError
#print axioms Freezing1.poisson_boundedTestError_of_le
#print axioms Freezing1.poisson_parameter_boundedTestError
#print axioms Freezing1.bernoulliPartialSumLaw_poisson_parameter_event
#print axioms Freezing1.blockAttachmentParameter
#print axioms Freezing1.blockAttachmentIndices
#print axioms Freezing1.blockAttachmentParameter_coe
#print axioms Freezing1.sum_blockAttachmentParameter
#print axioms Freezing1.blockAttachmentParameter_le_of_population_lower
#print axioms Freezing1.sum_sq_blockAttachmentParameter_le
#print axioms Freezing1.sum_sq_blockAttachmentParameter_le_linear
