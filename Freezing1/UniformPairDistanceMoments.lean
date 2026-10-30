module

public import Freezing1.UniformPairDistance

/-!
# Exponential moments of the distance of two uniform vertices

Distance is bounded by the sum of the two heights. The elementary arithmetic
mean bound handles their dependence and gives the required uniform moments.
-/

@[expose] public section

namespace Freezing1.CanonicalTree

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

theorem pairCoalescenceLaw_height_bounds (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ z ∂pairCoalescenceLaw x n, z.1 ≤ n ∧ z.2.1 ≤ n := by
  have h1 : ∀ᵐ z ∂pairCoalescenceLaw x n, z.1 ≤ n := by
    apply (ae_map_iff (f := fun z : PairCoalescenceData => z.1)
      (p := fun k : ℕ => k ≤ n) (by fun_prop) (by measurability)).mp
    rw [pairCoalescenceLaw_map_first x n hn]
    exact Forward.uniformHeightLaw_le x n
  have h2 : ∀ᵐ z ∂pairCoalescenceLaw x n, z.2.1 ≤ n := by
    apply (ae_map_iff (f := fun z : PairCoalescenceData => z.2.1)
      (p := fun k : ℕ => k ≤ n) (by fun_prop) (by measurability)).mp
    rw [pairCoalescenceLaw_map_second x n hn]
    exact Forward.uniformHeightLaw_le x n
  exact h1.and h2

theorem pairCoalescenceLaw_distance_bound (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ z ∂pairCoalescenceLaw x n, (z.2.2.1 : ℝ) ≤ 2 * n := by
  filter_upwards [pairCoalescenceLaw_height_bounds x n hn,
    pairCoalescenceLaw_geometry x n hn] with z hz hg
  have h1 : (z.1 : ℝ) ≤ n := by exact_mod_cast hz.1
  have h2 : (z.2.1 : ℝ) ≤ n := by exact_mod_cast hz.2
  linarith [hg.1]

theorem pairCoalescenceLaw_integrable_exp_distance (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (θ : ℝ) :
    Integrable (fun z => Real.exp (θ * (z.2.2.1 : ℝ))) (pairCoalescenceLaw x n) := by
  let := pairCoalescenceLaw_probability x n hn
  apply (integrable_const (Real.exp (|θ| * (2 * n)))).mono' (by fun_prop)
  filter_upwards [pairCoalescenceLaw_distance_bound x n hn] with z hz
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_right (le_abs_self θ) (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hz (abs_nonneg _))

theorem pairCoalescenceLaw_integrable_first (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (f : ℕ → ℝ) :
    Integrable (fun z => f z.1) (pairCoalescenceLaw x n) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mp
  rw [pairCoalescenceLaw_map_first x n hn]
  exact Forward.uniformHeightLaw_integrable x n f

theorem pairCoalescenceLaw_integrable_second (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (f : ℕ → ℝ) :
    Integrable (fun z => f z.2.1) (pairCoalescenceLaw x n) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mp
  rw [pairCoalescenceLaw_map_second x n hn]
  exact Forward.uniformHeightLaw_integrable x n f

/-- No independence between heights is needed for this pointwise estimate. -/
theorem exp_add_le_exp_double (a b : ℝ) :
    Real.exp (a + b) ≤ (Real.exp (2 * a) + Real.exp (2 * b)) / 2 := by
  rw [Real.exp_add]
  have ha : Real.exp (2 * a) = Real.exp a ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  have hb : Real.exp (2 * b) = Real.exp b ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  rw [ha, hb]
  nlinarith [sq_nonneg (Real.exp a - Real.exp b)]

theorem pairCoalescenceLaw_distance_mgf_le (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) < extinctionTime x) :
    mgf (fun z => (z.2.2.1 : ℝ)) (pairCoalescenceLaw x n) 1 ≤
      Real.exp 2 * Real.exp (heightScale x n * (Real.exp 2 - 1)) := by
  have hi1 := pairCoalescenceLaw_integrable_first x n hn.le
    (fun k => Real.exp (2 * (k : ℝ)))
  have hi2 := pairCoalescenceLaw_integrable_second x n hn.le
    (fun k => Real.exp (2 * (k : ℝ)))
  have h1 : (∫ z, Real.exp (2 * (z.1 : ℝ)) ∂pairCoalescenceLaw x n) =
      mgf (fun k : ℕ => (k : ℝ)) (Forward.uniformHeightLaw x n) 2 := by
    rw [← pairCoalescenceLaw_map_first x n hn.le, mgf,
      integral_map (by fun_prop) (by fun_prop)]
  have h2 : (∫ z, Real.exp (2 * (z.2.1 : ℝ)) ∂pairCoalescenceLaw x n) =
      mgf (fun k : ℕ => (k : ℝ)) (Forward.uniformHeightLaw x n) 2 := by
    rw [← pairCoalescenceLaw_map_second x n hn.le, mgf,
      integral_map (by fun_prop) (by fun_prop)]
  calc
    _ ≤ ∫ z, (Real.exp (2 * (z.1 : ℝ)) + Real.exp (2 * (z.2.1 : ℝ))) / 2
        ∂pairCoalescenceLaw x n := by
      apply integral_mono_ae (pairCoalescenceLaw_integrable_exp_distance x n hn.le 1)
        ((hi1.add hi2).div_const 2)
      filter_upwards [pairCoalescenceLaw_geometry x n hn.le] with z hz
      simp only [one_mul]
      exact (Real.exp_le_exp.mpr (by linarith [hz.1])).trans
        (exp_add_le_exp_double _ _)
    _ = mgf (fun k : ℕ => (k : ℝ)) (Forward.uniformHeightLaw x n) 2 := by
      rw [integral_div, integral_add hi1 hi2, h1, h2]
      ring
    _ ≤ _ := Forward.uniformHeightLaw_mgf_upper x n hn (by norm_num)

end Freezing1.CanonicalTree
