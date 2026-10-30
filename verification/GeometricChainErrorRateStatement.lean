module

import Freezing1.GeometricChainErrorRate

open Freezing1 Filter

example (C : ℕ) (hC : 2 ≤ C) (L J : ℝ) (hL : 0 ≤ L) (hJ : 0 ≤ J) :
    ∃ Δ > 0, ∀ᶠ (k : ℕ) in atTop,
      L / (C : ℝ) ^ k + J / (k : ℝ) ^ 2 + 3 * (k : ℝ) ^ 3 / (2 : ℝ) ^ k ≤
        Δ / (k : ℝ) ^ 2 := by
  simpa only [geometricChainError, one_mul] using
    exists_geometricChainError_inv_sq_bound C hC L J hL hJ

#print axioms Freezing1.eventually_geometricChainError_le_inv_sq
#print axioms Freezing1.exists_geometricChainError_inv_sq_bound
