module

public import Freezing1.ForwardForestConditionalGrowth
public import Freezing1.MainConditionalGoodChain
public import Freezing1.GeometricChainPositiveCutoff
public import Freezing1.ForwardGoodChainJoint
public import Freezing1.GeometricChainErrorRate
public import Freezing1.GeometricChainSourceIndices
public import Freezing1.MainForwardBlockConcentration
public import Freezing1.MainLinearComponentMaximum

/-! The source conditional one-step bound through the complete-forest
conditional mean, variance, Chebyshev and tower argument. The original
positive-index cutoff is exact also in the finite definitions. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal Topology

namespace Forward

theorem treeLaw_cond_goodChain_failure_le_terminal_from_forest (x : SignSequence) {n C k₀ k : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hend : C ^ (k + 1) ≤ n) (ha : 3 ≤ C ^ k)
    {t : ℝ} (ht : 0 ≤ t) {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M) :
    (ProbabilityTheory.cond (treeLaw x n)
      {q | b ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ)}).real
      {q | ((goodSet (truncateAt q (C ^ (k + 1))) C k₀ (k + 1) t).card : ℝ) < 2 * b} ≤
      (treeLaw x n).real {q |
        (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) ≤ 4 * (C ^ k : ℕ)} +
      (treeLaw x (C ^ (k + 1))).real {q | M < (componentMaximum q (C ^ k) : ℝ)} +
      3 * M / b := by
  have haz : C ^ k ≤ C ^ (k + 1) := pow_le_pow_right₀ hC (Nat.le_succ k)
  have hzτ : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hend : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ n).trans hn
  have he := treeLaw_cond_two_prefix_event_real x hn haz hend
    {q | b ≤ ((goodSet q C k₀ k t).card : ℝ)}
    {q | ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * b}
  simp only [Set.mem_ofPred_eq] at he
  rw [he]
  have hh := treeLaw_cond_goodChain_failure_le_from_forest x hC hk hzτ ha ht hb hM
  rw [treeLaw_blockTallCount_cdf_prefix x hn hend t] at hh
  exact hh

end Forward

theorem exists_uniform_conditional_goodChain_failure_bound_from_forest
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hτ : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hnear : NearOriginLinear x A (c : ℝ)) (hbulk : BulkLowerBound x)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      ∃ Δ : ℝ, 0 < Δ ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
        ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ ε * n / C →
          (ProbabilityTheory.cond (Forward.treeLaw (x n) n)
            {q | (2 : ℝ) ^ k ≤ ((Forward.goodSet (Forward.truncateAt q (C ^ k)) C
              (positiveChainLowerIndex C A n) k
              ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η))).card : ℝ)}).real
            {q | ((Forward.goodSet (Forward.truncateAt q (C ^ (k + 1))) C
              (positiveChainLowerIndex C A n) (k + 1)
              ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η))).card : ℝ) <
                (2 : ℝ) ^ (k + 1)} ≤ Δ / (k : ℝ) ^ 2 := by
  obtain ⟨C, hC, hsize, L, hL, ε, hε, hε1, hN⟩ :=
    exists_forward_geometricBlock_fewTallRoots_probability x A c hτ hAinf hnear hη
  have hC2 : 2 ≤ C := by omega
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (eventually_geometricChainError_le_inv_sq C hC2 L 1 hL.le)
  refine ⟨C, hC, hsize, L + 4, by linarith, ε, hε, hε1, ?_⟩
  filter_upwards [hN,
    uniform_geometric_componentMaximum_tail x A c.property.1 hAinf hnear hbulk hτ C hC.le,
    eventually_positiveChainLowerIndex_eq C hC A hAinf,
    hAinf.eventually_gt_atTop (((C ^ (max K 2) : ℕ) : ℝ))] with n hNn hMn hcutoff hAn
  intro k hAk hupper
  have hlarge : max K 2 ≤ k := by
    by_contra hh
    have hle : k ≤ max K 2 := by omega
    have hp := pow_le_pow_right₀ hC.le hle
    have hpR : ((C ^ k : ℕ) : ℝ) ≤ (C ^ max K 2 : ℕ) := by exact_mod_cast hp
    exact (not_le_of_gt hAn) (hAk.trans hpR)
  have hkK : K ≤ k := (le_max_left _ _).trans hlarge
  have hk2 : 2 ≤ k := (le_max_right _ _).trans hlarge
  obtain ⟨haz, hend⟩ := geometricBlock_window_bounds hC hε1.le hupper
  have hk₀ : positiveChainLowerIndex C A n ≤ k := by
    rw [hcutoff]
    exact (chainLowerIndex_le_iff C hC A n k (hA n)).mpr hAk
  have hpow : 3 ≤ C ^ k := by
    have hp : 3 ≤ C ^ k := by
      calc
        3 ≤ 2 ^ 2 := by norm_num
        _ ≤ C ^ 2 := pow_le_pow_left' hC2 2
        _ ≤ C ^ k := pow_le_pow_right₀ hC.le hk2
    exact hp
  have ht : 0 ≤ (linearPoissonRate c C : ℝ) * (linearHeightFactor c - η) := by
    exact mul_nonneg (NNReal.coe_nonneg _) (by have hf := one_lt_linearHeightFactor c; linarith)
  have hstep := Forward.treeLaw_cond_goodChain_failure_le_terminal_from_forest (x n) (hτ n) hC.le hk₀
    hend hpow ht
    (b := (2 : ℝ) ^ k) (M := (k : ℝ) ^ 3) (by positivity) (by positivity)
  have hM' := hMn k hAk (by simpa only [pow_succ] using hend)
  simp only [← pow_succ] at hM'
  have hbound : _ ≤ geometricChainError C L 1 1 k :=
    hstep.trans (by
      have hh := add_le_add (add_le_add (hNn k hAk hupper) hM')
        (le_refl (3 * (k : ℝ) ^ 3 / (2 : ℝ) ^ k))
      simpa only [geometricChainError, one_mul, Nat.cast_pow] using hh)
  have hfinal := hbound.trans (hK k hkK)
  simpa only [pow_succ, mul_comm (2 : ℝ), show L + 1 + 3 = L + 4 by ring] using hfinal

/-- The uniform source conditional estimate, using the literal limsup and
liminf hypotheses. Conditioning on a null event gives zero. -/
theorem linear_conditional_goodChain_failure_bound_from_forest
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
              (positiveChainLowerIndex C A n) k
              ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η))).card : ℝ)}).real
            {q | ((Forward.goodSet (Forward.truncateAt q (C ^ (k + 1))) C
              (positiveChainLowerIndex C A n) (k + 1)
              ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η))).card : ℝ) <
                (2 : ℝ) ^ (k + 1)} ≤ Δ / (k : ℝ) ^ 2 := by
  have hs : ∀ n, PositiveThrough (x n) n := fun n =>
    (lt_extinctionTime_iff (x n) n).mp (hτ n)
  exact exists_uniform_conditional_goodChain_failure_bound_from_forest x A c
    (fun n => (hτ n).le) hA hAinf
    ((nearOriginLimsup_iff x A hA c.property.1.le c.property.2 hs).mp hnear)
    ((bulkLiminf_iff x hs).mp hbulk) hη hη1

end Freezing1
