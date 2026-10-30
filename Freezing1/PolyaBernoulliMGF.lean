module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

/-!
# Exponential estimates for the signed Pólya urn

The small centered-Bernoulli bound is the analytic step in the backward MGF
argument cited for L13. It holds for either sign of the normalized increment,
as required when the urn includes removals. This module alone does not assert
the maximal inequality or supply the stochastic urn construction.
-/

@[expose] public section

namespace Freezing1

/-- A rational Taylor bound, valid on both sides of zero. -/
theorem exp_le_quadratic_small {c : ℝ} (hc : |c| ≤ 5 / 16) :
    Real.exp c ≤ 1 + c + (16 / 25 : ℝ) * c ^ 2 := by
  have ht := (abs_le.mp (Real.exp_bound (x := c) (by linarith : |c| ≤ 1)
    (n := 3) (by norm_num))).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  have hcub : |c| ^ 3 ≤ (5 / 16 : ℝ) * c ^ 2 := by
    calc
      |c| ^ 3 = |c| * c ^ 2 := by rw [pow_succ, sq_abs]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg c)
  nlinarith [sq_nonneg c]

/-- Centered Bernoulli exponential control with the coefficient used in the
source's cited urn argument, including negative exponential parameters. -/
theorem centeredBernoulli_exponential_small {x c : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hc : |c| ≤ 5 / 16) :
    x * Real.exp (c * (1 - x)) + (1 - x) * Real.exp (-c * x) ≤
      Real.exp ((16 / 25 : ℝ) * c ^ 2 * x) := by
  have hc1 : |c * (1 - x)| ≤ 5 / 16 := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - x)]
    nlinarith [mul_nonneg (abs_nonneg c) hx0]
  have hc0 : |-c * x| ≤ 5 / 16 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hx0]
    nlinarith [mul_nonneg (abs_nonneg c) (sub_nonneg.mpr hx1)]
  have h1 := mul_le_mul_of_nonneg_left (exp_le_quadratic_small hc1) hx0
  have h0 := mul_le_mul_of_nonneg_left (exp_le_quadratic_small hc0) (sub_nonneg.mpr hx1)
  calc
    _ ≤ x * (1 + c * (1 - x) + (16 / 25 : ℝ) * (c * (1 - x)) ^ 2) +
        (1 - x) * (1 + -c * x + (16 / 25 : ℝ) * (-c * x) ^ 2) := add_le_add h1 h0
    _ = 1 + (16 / 25 : ℝ) * c ^ 2 * x * (1 - x) := by ring
    _ ≤ 1 + (16 / 25 : ℝ) * c ^ 2 * x := by
      have hh : 0 ≤ (16 / 25 : ℝ) * c ^ 2 * x ^ 2 := by positivity
      nlinarith
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp ((16 / 25 : ℝ) * c ^ 2 * x)

/-- The normalized urn has next value `x+δ*(1-x)` with probability `x`
and `x-δ*x` otherwise; the same bound works for additions and removals. -/
theorem polya_exponential_step_le {x γ δ : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hsmall : |γ * δ| ≤ 5 / 16) :
    x * Real.exp (γ * (x + δ * (1 - x))) +
        (1 - x) * Real.exp (γ * (x - δ * x)) ≤
      Real.exp ((γ + (16 / 25 : ℝ) * γ ^ 2 * δ ^ 2) * x) := by
  have h := mul_le_mul_of_nonneg_left
    (centeredBernoulli_exponential_small hx0 hx1 hsmall) (Real.exp_pos (γ * x)).le
  calc
    _ = Real.exp (γ * x) *
        (x * Real.exp ((γ * δ) * (1 - x)) + (1 - x) * Real.exp (-(γ * δ) * x)) := by
      rw [show γ * (x + δ * (1 - x)) = γ * x + (γ * δ) * (1 - x) by ring,
        show γ * (x - δ * x) = γ * x + -(γ * δ) * x by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := h
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Backward MGF parameters grow by at most a factor `5/4` when their
remaining square-increment budget is at most `1/4`. -/
theorem polya_backward_parameter_abs {θ B : ℝ} (hB : 0 ≤ B)
    (hbudget : |θ| * B ≤ 1 / 4) :
    |θ * (1 + θ * B)| ≤ (5 / 4 : ℝ) * |θ| := by
  calc
    _ = |θ| * |1 + θ * B| := abs_mul _ _
    _ ≤ |θ| * (1 + |θ| * B) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg θ)
      simpa only [abs_one, abs_mul, abs_of_nonneg hB] using abs_add_le 1 (θ * B)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hbudget (abs_nonneg θ)]

theorem polya_backward_parameter_sq {θ B : ℝ} (hB : 0 ≤ B)
    (hbudget : |θ| * B ≤ 1 / 4) :
    (16 / 25 : ℝ) * (θ * (1 + θ * B)) ^ 2 ≤ θ ^ 2 := by
  have hh := polya_backward_parameter_abs hB hbudget
  have hs := mul_self_le_mul_self (abs_nonneg (θ * (1 + θ * B))) hh
  nlinarith [sq_abs (θ * (1 + θ * B)), sq_abs θ]

/-- One complete backward induction step, with the remaining quadratic
budget explicit. No restriction to positive urn increments is used. -/
theorem polya_backward_exponential_step {x θ δ B : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hB : 0 ≤ B)
    (hbudget : |θ| * B ≤ 1 / 4) (hincrement : |θ * δ| ≤ 1 / 4) :
    x * Real.exp ((θ * (1 + θ * B)) * (x + δ * (1 - x))) +
        (1 - x) * Real.exp ((θ * (1 + θ * B)) * (x - δ * x)) ≤
      Real.exp ((θ * (1 + θ * (B + δ ^ 2))) * x) := by
  have hsmall : |(θ * (1 + θ * B)) * δ| ≤ 5 / 16 := by
    calc
      _ = |θ * (1 + θ * B)| * |δ| := abs_mul _ _
      _ ≤ ((5 / 4 : ℝ) * |θ|) * |δ| :=
        mul_le_mul_of_nonneg_right (polya_backward_parameter_abs hB hbudget) (abs_nonneg δ)
      _ = (5 / 4 : ℝ) * |θ * δ| := by rw [abs_mul]; ring
      _ ≤ _ := by linarith
  calc
    _ ≤ Real.exp ((θ * (1 + θ * B) +
        (16 / 25 : ℝ) * (θ * (1 + θ * B)) ^ 2 * δ ^ 2) * x) :=
      polya_exponential_step_le hx0 hx1 hsmall
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ hx0
      have hh := mul_le_mul_of_nonneg_right (polya_backward_parameter_sq hB hbudget) (sq_nonneg δ)
      nlinarith

end Freezing1
