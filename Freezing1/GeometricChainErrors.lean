module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Summable errors for geometric good-chain growth

The three terms respectively bound the tall-root failure, the component-size
failure, and the finite-permutation growth failure. Their sum is summable as
written; no asymptotic replacement by an inverse-square estimate is needed.
-/

@[expose] public section

namespace Freezing1

/-- The exact error used by the actual good-chain transition estimate. -/
noncomputable def geometricChainError (C : ℕ) (L J ρ : ℝ) (k : ℕ) : ℝ :=
  L / (C : ℝ) ^ k + J / (k : ℝ) ^ 2 +
    3 * (k : ℝ) ^ 3 / (ρ * (2 : ℝ) ^ k)

theorem geometricChainError_nonneg (C : ℕ) {L J ρ : ℝ}
    (hL : 0 ≤ L) (hJ : 0 ≤ J) (hρ : 0 < ρ) (k : ℕ) :
    0 ≤ geometricChainError C L J ρ k := by
  unfold geometricChainError
  positivity

theorem summable_geometricChainError (C : ℕ) (hC : 2 ≤ C) (L J ρ : ℝ) :
    Summable (geometricChainError C L J ρ) := by
  have hC1 : (1 : ℝ) < C := by exact_mod_cast (show 1 < C by omega)
  have hgeom : Summable (fun k : ℕ => (1 / (C : ℝ)) ^ k) :=
    summable_geometric_of_abs_lt_one (by
      rw [abs_of_pos (one_div_pos.mpr (by linarith))]
      exact (div_lt_one (by linarith)).mpr hC1)
  have hfirst : Summable (fun k : ℕ => L / (C : ℝ) ^ k) := by
    apply (hgeom.mul_left L).congr
    intro k
    rw [div_pow, one_pow]
    ring
  have hsecond : Summable (fun k : ℕ => J / (k : ℝ) ^ 2) := by
    have hh := (Real.summable_one_div_nat_pow.mpr (show 1 < 2 by omega)).mul_left J
    exact hh.congr (fun k => by ring)
  have hpoly : Summable (fun k : ℕ => (k : ℝ) ^ 3 * (1 / 2 : ℝ) ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 3 (by norm_num)
  have hthird : Summable (fun k : ℕ => 3 * (k : ℝ) ^ 3 / (ρ * (2 : ℝ) ^ k)) := by
    apply (hpoly.mul_left (3 / ρ)).congr
    intro k
    rw [div_pow, one_pow]
    ring
  exact (hfirst.add hsecond).add hthird

end Freezing1
