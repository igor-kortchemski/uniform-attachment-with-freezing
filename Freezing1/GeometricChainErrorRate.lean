module

public import Freezing1.GeometricChainErrors

/-!
# An explicit inverse-square bound for the original good-chain errors

The two exponentially small terms are bounded using their actual scalar
limits. The original population threshold 2^k corresponds to rho = 1.
-/

@[expose] public section

namespace Freezing1

open Filter
open scoped Topology

theorem eventually_geometricChainError_le_inv_sq (C : ℕ) (hC : 2 ≤ C)
    (L J : ℝ) (hL : 0 ≤ L) :
    ∀ᶠ k in atTop, geometricChainError C L J 1 k ≤ (L + J + 3) / (k : ℝ) ^ 2 := by
  have hCR : (1 : ℝ) < C := by exact_mod_cast (show 1 < C by omega)
  have htwo := tendsto_pow_const_div_const_pow_of_one_lt 2 hCR
  have hfive := tendsto_pow_const_div_const_pow_of_one_lt 5 (by norm_num : (1 : ℝ) < 2)
  filter_upwards [htwo.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    hfive.eventually_lt_const (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop 1]
    with k hk2 hk5 hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkpow : 0 < (k : ℝ) ^ 2 := pow_pos hk0 2
  have hCpow : 0 < (C : ℝ) ^ k := pow_pos (by linarith) k
  have h2pow : 0 < (2 : ℝ) ^ k := by positivity
  have hb2 : (k : ℝ) ^ 2 ≤ (C : ℝ) ^ k := (div_le_one hCpow).mp hk2.le
  have hb5 : (k : ℝ) ^ 5 ≤ (2 : ℝ) ^ k := (div_le_one h2pow).mp hk5.le
  have hfirst : L / (C : ℝ) ^ k ≤ L / (k : ℝ) ^ 2 := by
    exact (div_le_div_iff₀ hCpow hkpow).mpr (mul_le_mul_of_nonneg_left hb2 hL)
  have hthird : 3 * (k : ℝ) ^ 3 / (2 : ℝ) ^ k ≤ 3 / (k : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ h2pow hkpow).mpr
    nlinarith
  calc
    geometricChainError C L J 1 k =
        L / (C : ℝ) ^ k + J / (k : ℝ) ^ 2 + 3 * (k : ℝ) ^ 3 / (2 : ℝ) ^ k := by
      simp only [geometricChainError, one_mul]
    _ ≤ L / (k : ℝ) ^ 2 + J / (k : ℝ) ^ 2 + 3 / (k : ℝ) ^ 2 :=
      add_le_add (add_le_add hfirst le_rfl) hthird
    _ = _ := by ring

theorem exists_geometricChainError_inv_sq_bound (C : ℕ) (hC : 2 ≤ C)
    (L J : ℝ) (hL : 0 ≤ L) (hJ : 0 ≤ J) :
    ∃ Δ > 0, ∀ᶠ k in atTop, geometricChainError C L J 1 k ≤ Δ / (k : ℝ) ^ 2 := by
  exact ⟨L + J + 3, by linarith, eventually_geometricChainError_le_inv_sq C hC L J hL⟩

end Freezing1
