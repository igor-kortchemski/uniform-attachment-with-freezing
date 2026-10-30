module

import Freezing1.MainConditionalGoodChain

open Freezing1 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical Topology

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (r : ℝ) (hr : 0 ≤ r)
    (h : μ.real (A ∩ B) ≤ r * μ.real A) :
    (ProbabilityTheory.cond μ A).real B ≤ r :=
  Forward.cond_real_le_of_inter_le_mul μ A B hA hr h

example
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hnear : NearOriginLimsup x A (c : ℝ)) (hbulk : BulkLiminf x)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      ∃ Δ : ℝ, 0 < Δ ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
        ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ ε * n / C →
          (ProbabilityTheory.cond (Forward.treeLaw (x n) n)
            {q | (2 : ℝ) ^ k ≤ ((Forward.goodSet (Forward.truncateAt q (C ^ k)) C
              (chainLowerIndex C A n) k
              ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η))).card : ℝ)}).real
            {q | ((Forward.goodSet (Forward.truncateAt q (C ^ (k + 1))) C
              (chainLowerIndex C A n) (k + 1)
              ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η))).card : ℝ) <
                (2 : ℝ) ^ (k + 1)} ≤ Δ / (k : ℝ) ^ 2 :=
  linear_conditional_goodChain_failure_bound x A c hτ hA hAinf hnear hbulk hη

#print axioms Freezing1.Forward.treeLaw_prefix_inter_event_le
#print axioms Freezing1.Forward.treeLaw_goodChain_failure_inter_le
#print axioms Freezing1.Forward.cond_real_le_of_inter_le_mul
#print axioms Freezing1.Forward.treeLaw_cond_goodChain_failure_le
#print axioms Freezing1.Forward.treeLaw_cond_two_prefix_event_real
#print axioms Freezing1.eventually_geometricChainError_le_inv_sq
#print axioms Freezing1.linear_conditional_goodChain_failure_bound
