module

import Freezing1.MainConditionalGoodChainForest

/- Authored source-route statement reconstruction; independent review is separate. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal Topology
open Freezing1 Freezing1.Forward

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

example (x : SignSequence) {C k₀ k : ℕ} (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hτ : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : 3 ≤ C ^ k) {t : ℝ} (ht : 0 ≤ t) {target cap : ℝ}
    (hTarget : 0 < target) (hCap : 0 ≤ cap) :
    (ProbabilityTheory.cond (treeLaw x (C ^ (k + 1)))
      {q | target ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ)}).real
      {q | ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * target} ≤
      (treeLaw x (C ^ (k + 1))).real {q |
        (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) ≤ 4 * ((C ^ k : ℕ) : ℝ)} +
      (treeLaw x (C ^ (k + 1))).real {q | cap < (componentMaximum q (C ^ k) : ℝ)} +
      3 * cap / target :=
  treeLaw_cond_goodChain_failure_le_from_forest x hC hk hτ ha ht hTarget hCap

example (x : SignSequence) {n C k₀ k : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hend : C ^ (k + 1) ≤ n) (ha : 3 ≤ C ^ k)
    {t : ℝ} (ht : 0 ≤ t) {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M) :
    (ProbabilityTheory.cond (treeLaw x n)
      {q | b ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ)}).real
      {q | ((goodSet (truncateAt q (C ^ (k + 1))) C k₀ (k + 1) t).card : ℝ) < 2 * b} ≤
      (treeLaw x n).real {q |
        (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) ≤ 4 * (C ^ k : ℕ)} +
      (treeLaw x (C ^ (k + 1))).real {q | M < (componentMaximum q (C ^ k) : ℝ)} +
      3 * M / b :=
  treeLaw_cond_goodChain_failure_le_terminal_from_forest x hn hC hk hend ha ht hb hM

example
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hnear : NearOriginLimsup x A (c : ℝ)) (hbulk : BulkLiminf x)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      ∃ Δ : ℝ, 0 < Δ ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
        ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ ε * n / C →
          (ProbabilityTheory.cond (Forward.treeLaw (x n) n)
            {q | (2 : ℝ) ^ k ≤ ((Forward.goodSet (Forward.truncateAt q (C ^ k)) C
              (max 1 (chainLowerIndex C A n)) k
              ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η))).card : ℝ)}).real
            {q | ((Forward.goodSet (Forward.truncateAt q (C ^ (k + 1))) C
              (max 1 (chainLowerIndex C A n)) (k + 1)
              ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η))).card : ℝ) <
                (2 : ℝ) ^ (k + 1)} ≤ Δ / (k : ℝ) ^ 2 :=
  linear_conditional_goodChain_failure_bound_from_forest x A c hτ hA hAinf hnear hbulk hη hη1

#print axioms real_inter_le_of_observed_condExp
#print axioms treeLaw_favorable_goodChain_failure_le_from_forest
#print axioms treeLaw_goodChain_failure_inter_le_from_forest
#print axioms treeLaw_cond_goodChain_failure_le_from_forest
#print axioms treeLaw_cond_goodChain_failure_le_terminal_from_forest
#print axioms exists_uniform_conditional_goodChain_failure_bound_from_forest
#print axioms linear_conditional_goodChain_failure_bound_from_forest
