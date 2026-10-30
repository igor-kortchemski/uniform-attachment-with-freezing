module

import Freezing1.LinearBlockLowerTail

open Freezing1 MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators Classical

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (a b : ℕ) (hbn : b ≤ n) (ha : 1 ≤ a) {c : ℝ} (hc : 0 < c)
    (herr : ∀ j ∈ Finset.Icc a b, |(activeCount x j : ℝ)/j-c| ≤ c/2)
    (rate : ℝ≥0) (E : Set ℕ) :
    |(bernoulliPartialSumLaw (blockAttachmentParameter x n hn b hbn)
        (blockAttachmentIndices a b)).real E - (poissonMeasure rate).real E| ≤
      (2/(c*a))*heightInterval x a b + |heightInterval x a b-(rate:ℝ)| :=
  block_bernoulli_poisson_event_error x n hn a b hbn ha hc herr rate E

#print axioms Freezing1.block_bernoulli_poisson_event_error
#print axioms Freezing1.geometricBlock_le_horizon
#print axioms Freezing1.uniform_geometricBlock_poisson_approximation
#print axioms Freezing1.exists_uniform_geometricBlock_weighted_tail_lower
