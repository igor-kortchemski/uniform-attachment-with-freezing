module

import Freezing1.GeometricChainSourceIndices

open Freezing1
open scoped Classical

example (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ) (n ell : ℕ) (hA : 0 < A n) :
    Nat.ceil (Real.log (A n) / Real.log (C : ℝ)) ≤ ell ↔
      A n ≤ ((C ^ ell : ℕ) : ℝ) :=
  chainLowerIndex_le_iff C hC A n ell hA

example (s : Forward.State) (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ)
    (n k : ℕ) (t : ℝ) (hA : 0 < A n)
    (hk₀ : 1 ≤ Nat.ceil (Real.log (A n) / Real.log (C : ℝ))) :
    Forward.goodSet s C (Nat.ceil (Real.log (A n) / Real.log (C : ℝ))) k t =
      s.active.filter fun v => ∀ ell : ℕ, 1 ≤ ell → ell < k →
        A n ≤ ((C ^ ell : ℕ) : ℝ) →
        t < (Forward.blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ) :=
  Forward.goodSet_eq_source_filter s C hC A n k t hA hk₀

#print axioms Freezing1.chainLowerIndex_le_iff
#print axioms Freezing1.mem_chainInterval_iff_source
#print axioms Freezing1.chainInterval_eq_source_filter
#print axioms Freezing1.Forward.goodSet_eq_source_filter
