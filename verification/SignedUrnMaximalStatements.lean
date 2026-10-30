module

import Freezing1.SignedUrnInfinite

open Freezing1 Freezing1.SignedUrn MeasureTheory ProbabilityTheory

/-- Exact source tail constants, with the stronger full path-law condition
written out rather than hidden in a bundled hypothesis. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℤ) (Z : ℕ → ℤ)
    (hlaw : ∀ k, HasLaw (SignedUrn.record U 0 k) (SignedUrn.pathLaw Z 0 k 1) μ)
    (hZ : ∀ i, 0 < Z i)
    (hz : ∀ i, Z (i + 1) - Z i = 1 ∨ Z (i + 1) - Z i = -1)
    (hsum : Summable (fun i : ℕ => ((Z i : ℝ)⁻¹) ^ 2))
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | ∃ i : ℕ, 1 ≤ i ∧ t / (Z 0 : ℝ) <
      |(U i ω : ℝ) / Z i - (Z 0 : ℝ)⁻¹|} ≤
      2 * Real.exp (-((t ^ 2 / 4) * (Z 0 : ℝ)⁻¹) /
        ((∑' i : ℕ, ((Z (i + 1) : ℝ)⁻¹) ^ 2) +
          t * max (∑' i : ℕ, ((Z (i + 1) : ℝ)⁻¹) ^ 2)
            (sSup (Set.range fun i : ℕ => (Z (i + 1) : ℝ)⁻¹)))) :=
  SignedUrn.infinite_maximal_summable U Z hlaw hZ hz hsum ht

#print axioms Freezing1.SignedUrn.parameter_eq
#print axioms Freezing1.SignedUrn.transitionLaw_valid
#print axioms Freezing1.SignedUrn.normalized_mean
#print axioms Freezing1.SignedUrn.backward_exponential_step
#print axioms Freezing1.SignedUrn.continuationLaw_exponential_le
#print axioms Freezing1.SignedUrn.continuationLaw_upper_tail_optimized
#print axioms Freezing1.SignedUrn.crossingProbability_succ
#print axioms Freezing1.SignedUrn.crossingProbability_le
#print axioms Freezing1.SignedUrn.deviates_iff_exists
#print axioms Freezing1.SignedUrn.pathLaw_maximal_optimized
#print axioms Freezing1.SignedUrn.infinite_maximal_of_pathLaws
#print axioms Freezing1.SignedUrn.maximumReciprocal_attained
#print axioms Freezing1.SignedUrn.infinite_maximal_summable
