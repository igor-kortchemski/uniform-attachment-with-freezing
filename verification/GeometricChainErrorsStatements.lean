module

import Freezing1.GeometricChainErrors

open Freezing1

example (C : ℕ) (hC : 2 ≤ C) (L J ρ : ℝ) :
    Summable (fun k : ℕ => L / (C : ℝ) ^ k + J / (k : ℝ) ^ 2 +
      3 * (k : ℝ) ^ 3 / (ρ * (2 : ℝ) ^ k)) :=
  summable_geometricChainError C hC L J ρ

example (C : ℕ) (L J ρ : ℝ) (hL : 0 ≤ L) (hJ : 0 ≤ J) (hρ : 0 < ρ) (k : ℕ) :
    0 ≤ L / (C : ℝ) ^ k + J / (k : ℝ) ^ 2 +
      3 * (k : ℝ) ^ 3 / (ρ * (2 : ℝ) ^ k) :=
  geometricChainError_nonneg C hL hJ hρ k

#print axioms Freezing1.geometricChainError
#print axioms Freezing1.geometricChainError_nonneg
#print axioms Freezing1.summable_geometricChainError
