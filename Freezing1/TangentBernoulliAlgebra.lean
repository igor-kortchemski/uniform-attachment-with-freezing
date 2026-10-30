module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Tactic

/-!
# The algebraic absolute-value step in tangent's Bernoulli formula

These helpers turn the separately established complex coefficient identity
into the nonnegative real expression in the paper. The coefficient identity
is an explicit premise here; the final enumeration consumer must supply it.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

theorem tangent_even_power_difference_norm (n : ℕ) :
    ‖(2 * Complex.I) ^ (2 * n) - (4 * Complex.I) ^ (2 * n)‖ =
      (4 : ℝ) ^ n * ((4 : ℝ) ^ n - 1) := by
  have h2 : (2 * Complex.I) ^ 2 = (-4 : ℂ) := by norm_num [mul_pow, Complex.I_sq]
  have h4 : (4 * Complex.I) ^ 2 = (-16 : ℂ) := by norm_num [mul_pow, Complex.I_sq]
  have hf : (2 * Complex.I) ^ (2 * n) - (4 * Complex.I) ^ (2 * n) =
      (-4 : ℂ) ^ n * (1 - (4 : ℂ) ^ n) := by
    rw [pow_mul, pow_mul, h2, h4, show (-16 : ℂ) = -4 * 4 by norm_num, mul_pow]
    ring
  have hreal : (1 - (4 : ℂ) ^ n) = ((1 - (4 : ℝ) ^ n : ℝ) : ℂ) := by
    push_cast
    rfl
  have hpow : 1 ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  rw [hf, norm_mul, norm_pow, hreal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : 1 - (4 : ℝ) ^ n ≤ 0)]
  norm_num

theorem tangent_coefficient_absolute_formula (n : ℕ) (hn : 0 < n) (b : ℚ) (d : ℝ)
    (hd : 0 ≤ d)
    (hidentity : (d : ℂ) = ((2 * n - 1).factorial : ℂ) *
      ((2 * Complex.I) ^ (2 * n) - (4 * Complex.I) ^ (2 * n)) *
        algebraMap ℚ ℂ (b / (2 * n).factorial)) :
    d = (4 : ℝ) ^ n * ((4 : ℝ) ^ n - 1) * |(b : ℝ)| / (2 * n) := by
  have hnzero : 2 * n ≠ 0 := by omega
  have hfzero : ((2 * n - 1).factorial : ℝ) ≠ 0 := by positivity
  have hnf : ((2 * n).factorial : ℝ) = (2 * n) * ((2 * n - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred hnzero).symm
  have hq : algebraMap ℚ ℂ (b / (2 * n).factorial) =
      (b : ℂ) / ((2 * n).factorial : ℂ) := by
    simp
  have hh := congrArg norm hidentity
  rw [Complex.norm_of_nonneg hd, norm_mul, norm_mul, Complex.norm_natCast,
    tangent_even_power_difference_norm, hq, norm_div, Complex.norm_ratCast,
    Complex.norm_natCast, hnf] at hh
  rw [hh]
  field_simp

theorem tangent_bernoulli_absolute_formula (n : ℕ) (hn : 0 < n) (d : ℝ) (hd : 0 ≤ d)
    (hidentity : (d : ℂ) = ((2 * n - 1).factorial : ℂ) *
      ((2 * Complex.I) ^ (2 * n) - (4 * Complex.I) ^ (2 * n)) *
        algebraMap ℚ ℂ (bernoulli (2 * n) / (2 * n).factorial)) :
    d = (4 : ℝ) ^ n * ((4 : ℝ) ^ n - 1) * |(bernoulli (2 * n) : ℝ)| / (2 * n) :=
  tangent_coefficient_absolute_formula n hn (bernoulli (2 * n)) d hd hidentity

end Freezing1.BinaryBijection
