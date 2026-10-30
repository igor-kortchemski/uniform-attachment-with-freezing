module

import Freezing1.BernoulliReciprocalParameters

open Freezing1 MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → unitInterval) (s : Finset ι) (E : Set ℕ) :
    |(bernoulliPartialSumLaw p s).real E - (bernoulliPartialSumLaw q s).real E| ≤
      ∑ i ∈ s, |(p i : ℝ) - (q i : ℝ)| :=
  bernoulliPartialSumLaw_parameter_event p q s E

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (a b : ℕ) (hbn : b ≤ n) (ha : 1 ≤ a) {c : ℝ} (hc : 0 < c)
    (herr : ∀ j ∈ Finset.Icc a b, |(activeCount x j : ℝ)/j-c| ≤ c/2)
    (E : Set ℕ) :
    |(bernoulliPartialSumLaw (blockAttachmentParameter x n hn b hbn)
        (blockAttachmentIndices a b)).real E -
      (bernoulliPartialSumLaw
        (fun i : Fin b => enlargedAttachmentParameter x n hn ⟨i.val, i.isLt.trans_le hbn⟩)
        (blockAttachmentIndices a b)).real E| ≤
      (4/(c*a))*heightInterval x a b :=
  block_enlarged_parameter_event_le_linear x n hn a b hbn ha hc herr E

#print axioms Freezing1.bernoulli_parameter_boundedTestError
#print axioms Freezing1.bernoulliPartialSumLaw_parameter_boundedTestError
#print axioms Freezing1.bernoulliPartialSumLaw_parameter_event
#print axioms Freezing1.bernoulliPartialSumLaw_parameter_event_of_le
#print axioms Freezing1.reciprocal_parameter_difference
#print axioms Freezing1.reciprocal_parameter_difference_le
#print axioms Freezing1.enlargedAttachmentParameter
#print axioms Freezing1.enlargedAttachmentParameter_coe
#print axioms Freezing1.attachmentParameter_le_enlarged
#print axioms Freezing1.attachmentParameter_enlarged_difference_le
#print axioms Freezing1.block_enlarged_parameter_event
#print axioms Freezing1.block_enlarged_parameter_event_le_linear
#print axioms Freezing1.uniform_geometricBlock_enlarged_parameter_error
