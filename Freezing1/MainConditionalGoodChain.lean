module

public import Freezing1.ForwardConditionalGoodChain
public import Freezing1.ForwardGoodChainJoint
public import Freezing1.GeometricChainErrorRate
public import Freezing1.GeometricChainSourceIndices
public import Freezing1.MainForwardBlockConcentration
public import Freezing1.MainLinearComponentMaximum

/-!
# The original uniform conditional good-chain bound

The conditional probability is read from two prefixes of the same terminal
tree. The threshold is the source's original `2^k`; its separate initial
population argument still requires the corrected `c/4` base used by the main
height proof. The uniform inverse-square bound follows from the actual block
estimates and the exact independence of `(N,M)` from the earlier tree.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal Topology

namespace Forward

theorem treeLaw_cond_two_prefix_event_real (x : SignSequence) {n a b : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hab : a ≤ b) (hb : b ≤ n)
    (A B : Set State) :
    (ProbabilityTheory.cond (treeLaw x n) {q | truncateAt q a ∈ A}).real
        {q | truncateAt q b ∈ B} =
      (ProbabilityTheory.cond (treeLaw x b) {q | truncateAt q a ∈ A}).real B := by
  have hbτ : (b : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hb : (b : ℕ∞) ≤ n).trans hn
  have hfirst : (treeLaw x n) {q | truncateAt q a ∈ A} =
      (treeLaw x b) {q | truncateAt q a ∈ A} := by
    rw [treeLaw_prefix_event x hn (hab.trans hb), treeLaw_prefix_event x hbτ hab]
  have hpair := treeLaw_two_prefix_event x hn hab hb (fun s q => s ∈ A ∧ q ∈ B)
  change ((ProbabilityTheory.cond (treeLaw x n) {q | truncateAt q a ∈ A})
      {q | truncateAt q b ∈ B}).toReal =
    ((ProbabilityTheory.cond (treeLaw x b) {q | truncateAt q a ∈ A}) B).toReal
  rw [cond_apply (by trivial), cond_apply (by trivial), hfirst]
  congr 2

theorem treeLaw_cond_goodChain_failure_le_terminal (x : SignSequence) {n C k₀ k : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hend : C ^ (k + 1) ≤ n) (ha : (3 : ℝ) ≤ (C ^ k : ℕ))
    (t : ℝ) {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M) :
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
  have hh := treeLaw_cond_goodChain_failure_le x hC hk hzτ ha t hb hM
  rw [treeLaw_blockTallCount_cdf_prefix x hn hend t] at hh
  exact hh

end Forward

theorem exists_uniform_conditional_goodChain_failure_bound
    (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hτ : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hnear : NearOriginLinear x A (c : ℝ)) (hbulk : BulkLowerBound x)
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
                (2 : ℝ) ^ (k + 1)} ≤ Δ / (k : ℝ) ^ 2 := by
  obtain ⟨C, hC, hsize, L, hL, ε, hε, hε1, hN⟩ :=
    exists_forward_geometricBlock_fewTallRoots_probability x A c hτ hAinf hnear hη
  have hC2 : 2 ≤ C := by omega
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (eventually_geometricChainError_le_inv_sq C hC2 L 1 hL.le)
  refine ⟨C, hC, hsize, L + 4, by linarith, ε, hε, hε1, ?_⟩
  filter_upwards [hN,
    uniform_geometric_componentMaximum_tail x A c.property.1 hAinf hnear hbulk hτ C hC.le,
    hAinf.eventually_gt_atTop (((C ^ (max K 2) : ℕ) : ℝ))] with n hNn hMn hAn
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
  have hk₀ : chainLowerIndex C A n ≤ k :=
    (chainLowerIndex_le_iff C hC A n k (hA n)).mpr hAk
  have hpow : (3 : ℝ) ≤ (C ^ k : ℕ) := by
    have hp : 3 ≤ C ^ k := by
      calc
        3 ≤ 2 ^ 2 := by norm_num
        _ ≤ C ^ 2 := pow_le_pow_left' hC2 2
        _ ≤ C ^ k := pow_le_pow_right₀ hC.le hk2
    exact_mod_cast hp
  have hstep := Forward.treeLaw_cond_goodChain_failure_le_terminal (x n) (hτ n) hC.le hk₀
    hend hpow ((linearPoissonRate c C : ℝ) * (linearHeightFactor c - η))
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
theorem linear_conditional_goodChain_failure_bound
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
                (2 : ℝ) ^ (k + 1)} ≤ Δ / (k : ℝ) ^ 2 := by
  have hs : ∀ n, PositiveThrough (x n) n := fun n =>
    (lt_extinctionTime_iff (x n) n).mp (hτ n)
  exact exists_uniform_conditional_goodChain_failure_bound x A c
    (fun n => (hτ n).le) hA hAinf
    ((nearOriginLimsup_iff x A hA c.property.1.le c.property.2 hs).mp hnear)
    ((bulkLiminf_iff x hs).mp hbulk) hη

end Freezing1
