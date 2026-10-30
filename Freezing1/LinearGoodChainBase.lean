module

public import Freezing1.GeometricChainCutoffs
public import Freezing1.LinearRegimeAssumptions
public import Freezing1.ForwardGoodChains
public import Freezing1.ForwardTruncationLaw

/-!
# The actual initial population for the good-chain argument

At its first scale the good set is the whole active set. Near-origin linear
growth gives the required population with coefficient `c/4`, retaining every
integer base `C ≥ 2`. No tall-root event is required at the initial scale.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology

theorem eventually_chain_base_population (x : ℕ → SignSequence) (A : ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hnear : NearOriginLinear x A c) (C : ℕ) (hC : 2 ≤ C) :
    ∀ᶠ n in atTop,
      C ^ chainLowerIndex C A n ≤ n ∧
      c / 4 * (2 : ℝ) ^ chainLowerIndex C A n ≤
        (activeCount (x n) (C ^ chainLowerIndex C A n) : ℝ) := by
  obtain ⟨ε, hε, hε1, hbound⟩ := hnear (c / 2) (by positivity)
  have hC1 : 1 < C := by omega
  have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC1.le
  filter_upwards [hbound, eventually_chain_cutoff_bounds C hC1 hA hAinf hsmall hε hε1]
    with n hn hcut
  let k := chainLowerIndex C A n
  have hwindow := hcut.2.2.2.2 k le_rfl hcut.2.1
  have han : C ^ k ≤ n :=
    (Nat.le_mul_of_pos_right _ (by omega : 0 < C)).trans hwindow.2.2
  refine ⟨han, ?_⟩
  have hupper : ((C ^ k : ℕ) : ℝ) ≤ ε * n :=
    hwindow.2.1.trans (div_le_self (mul_nonneg hε.le (Nat.cast_nonneg n)) hCR)
  have he := hn (C ^ k) hwindow.1 hupper
  have ha : (0 : ℝ) < (C ^ k : ℕ) := by
    exact_mod_cast pow_pos (by omega : 0 < C) k
  have hlo : c / 2 ≤ (activeCount (x n) (C ^ k) : ℝ) / (C ^ k : ℕ) := by
    have hh := (abs_le.mp he).1
    linarith
  have hcount := (le_div_iff₀ ha).mp hlo
  have hpow : (2 : ℝ) ^ k ≤ (C ^ k : ℕ) := by
    simpa only [Nat.cast_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (by exact_mod_cast hC : (2 : ℝ) ≤ C) k
  calc
    c / 4 * (2 : ℝ) ^ k ≤ c / 4 * (C ^ k : ℕ) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ c / 2 * (C ^ k : ℕ) := mul_le_mul_of_nonneg_right (by linarith) ha.le
    _ ≤ _ := hcount

namespace Forward

theorem PhaseData.goodSet_base_card {x : SignSequence} {a : ℕ} {s : State}
    (hs : PhaseData x a s) (C k₀ : ℕ) (t : ℝ) :
    ((goodSet s C k₀ k₀ t).card : ℝ) = (activeCount x a : ℝ) := by
  rw [goodSet_base]
  exact_mod_cast hs.count

/-- The actual terminal tree, truncated at the first geometric scale, has
the required initial good population almost surely, eventually in n. -/
theorem eventually_treeLaw_goodSet_base (x : ℕ → SignSequence) (A : ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hnear : NearOriginLinear x A c) (C : ℕ) (hC : 2 ≤ C) (t : ℝ)
    (hτ : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n)) :
    ∀ᶠ n in atTop, ∀ᵐ s ∂treeLaw (x n) n,
      c / 4 * (2 : ℝ) ^ chainLowerIndex C A n ≤
        ((goodSet (truncateAt s (C ^ chainLowerIndex C A n)) C
          (chainLowerIndex C A n) (chainLowerIndex C A n) t).card : ℝ) := by
  filter_upwards [eventually_chain_base_population x A hc hA hAinf hsmall hnear C hC]
    with n hn
  filter_upwards [treeLaw_historyShape (x n) n (hτ n)] with s hs
  rw [(hs.prefix_phaseData hn.1).goodSet_base_card]
  exact hn.2

end Forward
end Freezing1
