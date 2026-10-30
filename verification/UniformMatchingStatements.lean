module

import Freezing1.UniformPermutationGrowth
import Freezing1.SummableFailureChain

open Freezing1 MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

example {ι : Type*} [Fintype ι] (G : Finset ι) (w : ι → ℝ) :
    (∫ σ, ∑ i, w i * (if σ i ∈ G then (1 : ℝ) else 0)
      ∂uniformPermutationLaw ι) =
      (G.card : ℝ) / Fintype.card ι * ∑ i, w i :=
  integral_weightedPermutationCount G w

example {ι : Type*} [Fintype ι] (G : Finset ι) (w : ι → ℝ) (M : ℝ)
    (h0 : ∀ i, 0 ≤ w i) (hM : ∀ i, w i ≤ M) :
    variance (fun σ => ∑ i, w i * (if σ i ∈ G then (1 : ℝ) else 0))
      (uniformPermutationLaw ι) ≤
        M * ∫ σ, ∑ i, w i * (if σ i ∈ G then (1 : ℝ) else 0)
          ∂uniformPermutationLaw ι :=
  variance_weightedPermutationCount_le G w h0 hM

example {ι : Type*} [Fintype ι] (G : Finset ι) (w : ι → ℝ)
    (a b M : ℝ) (ha : 3 ≤ a) (hb : 0 < b)
    (hm : (Fintype.card ι : ℝ) ≤ a + 1) (hg : b ≤ G.card)
    (hweight : 4 * a ≤ ∑ i, w i) (hM : 0 ≤ M)
    (h0 : ∀ i, 0 ≤ w i) (hcap : ∀ i, w i ≤ M) :
    (uniformPermutationLaw ι).real
      {σ | (∑ i, w i * (if σ i ∈ G then (1 : ℝ) else 0)) < 2 * b} ≤ 3 * M / b :=
  uniformPermutation_growth_failure_le G w ha hb hm hg hweight hM h0 hcap

#print axioms Freezing1.integral_permutationIndicator
#print axioms Freezing1.integral_permutationIndicator_pair_mul
#print axioms Freezing1.integral_permutationIndicator_pair_le
#print axioms Freezing1.integral_weightedPermutationCount
#print axioms Freezing1.variance_weightedPermutationCount_le
#print axioms Freezing1.uniformPermutation_growth_failure_le
#print axioms Freezing1.tendsto_failure_chain_zero
