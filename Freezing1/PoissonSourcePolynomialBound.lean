module

public import Freezing1.PoissonSourcePolynomial
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The source cubic prefactor is valid for the actual strict Poisson
tail, despite the invalid printed ceiling-mass proof. Small thresholds
are handled by their genuine mass at three. -/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped NNReal

set_option backward.isDefEq.respectTransparency false

theorem poisson_rounding_prefactor_ge_cubic {r u : ℝ} (hr : 2 ≤ r) (hu : 3 ≤ u) :
    1 / u ^ 3 ≤ r / (Real.exp 1 * (u + 1) ^ 2) := by
  have hu0 : 0 < u := by linarith
  have hp : 0 ≤ (u - 3) * (2 * u ^ 2 + 3 * u + 3) :=
    mul_nonneg (by linarith) (by positivity)
  have hru := mul_le_mul_of_nonneg_right hr (pow_nonneg hu0.le 3)
  have he := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (sq_nonneg (u + 1))
  apply (div_le_div_iff₀ (pow_pos hu0 3) (by positivity)).mpr
  nlinarith

theorem poisson_three_mass_lower (rate : ℝ≥0) (hr2 : (2 : ℝ) ≤ rate)
    (hr3 : (rate : ℝ) ≤ 3) :
    (1 / 8 : ℝ) ≤ (poissonMeasure rate).real {3} := by
  have hr0 : (0 : ℝ) < rate := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hr0)
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hr0.ne'] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hr0.le
  have he : (rate : ℝ) * (2 / (rate : ℝ) - 1) = 2 - rate := by field_simp
  rw [he] at hm
  have hld : 0 ≤ Real.log (rate : ℝ) - Real.log 2 :=
    sub_nonneg.mpr (Real.log_le_log (by norm_num) hr2)
  have hstep := mul_le_mul_of_nonneg_right hr3 hld
  have hval : -(2 : ℝ) + 3 * Real.log 2 ≤ -(rate : ℝ) + 3 * Real.log (rate : ℝ) := by
    nlinarith
  have hmass : Real.exp (-2) * (2 : ℝ) ^ 3 ≤ Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ 3 := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_exp,
      Real.log_pow, Real.log_pow]
    exact hval
  have he2 : Real.exp 2 < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 1, Real.exp_one_lt_three]
  calc
    (1 / 8 : ℝ) ≤ (4 / 3) / Real.exp 2 :=
      (le_div_iff₀ (Real.exp_pos 2)).mpr (by linarith)
    _ = Real.exp (-2) * (2 : ℝ) ^ 3 / 6 := by rw [Real.exp_neg]; ring
    _ ≤ Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ 3 / 6 :=
      div_le_div_of_nonneg_right hmass (by norm_num)
    _ = _ := by rw [poissonMeasure_real_singleton]; norm_num

/-- The printed quantitative Poisson inequality, with its exact cubic
prefactor, proved for the genuine strict tail and all source parameters. -/
theorem poisson_strict_tail_cubic_lower (rate : ℝ≥0) (hr : (2 : ℝ) < rate)
    {t : ℝ} (ht : 1 < t) :
    Real.exp (-(rate : ℝ) * bennettRate (t - 1)) / ((rate : ℝ) * t) ^ 3 ≤
      (poissonMeasure rate).real {k : ℕ | (rate : ℝ) * t < (k : ℝ)} := by
  have hr0 : (0 : ℝ) < rate := by linarith
  have hrNN : 0 < rate := hr0
  have ht0 : 0 < t := by linarith
  have hu : (2 : ℝ) < (rate : ℝ) * t := by nlinarith
  by_cases hu3 : 3 ≤ (rate : ℝ) * t
  · have hp := poisson_rounding_prefactor_ge_cubic hr.le hu3
    have hh := mul_le_mul_of_nonneg_left hp
      (Real.exp_pos (-(rate : ℝ) * bennettRate (t - 1))).le
    have hh' : Real.exp (-(rate : ℝ) * bennettRate (t - 1)) / ((rate : ℝ) * t) ^ 3 ≤
        Real.exp (-(rate : ℝ) * bennettRate (t - 1)) * (rate : ℝ) /
          (Real.exp 1 * ((rate : ℝ) * t + 1) ^ 2) := by
      convert hh using 1 <;> ring
    exact hh'.trans (poisson_strict_tail_rounding_lower rate hrNN ht)
  · have hu3' : (rate : ℝ) * t < 3 := lt_of_not_ge hu3
    have hr3 : (rate : ℝ) ≤ 3 := by nlinarith
    have htail : (poissonMeasure rate).real {3} ≤
        (poissonMeasure rate).real {k : ℕ | (rate : ℝ) * t < (k : ℝ)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro k hk
      obtain rfl := Set.mem_singleton_iff.mp hk
      exact hu3'
    have hg := bennettRate_nonneg (by linarith : 0 ≤ t - 1)
    have hE : Real.exp (-(rate : ℝ) * bennettRate (t - 1)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have hpow : (8 : ℝ) ≤ ((rate : ℝ) * t) ^ 3 := by
      have hp : 0 ≤ ((rate : ℝ) * t - 2) * (((rate : ℝ) * t) ^ 2 + 2 * ((rate : ℝ) * t) + 4) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith
    calc
      _ ≤ 1 / ((rate : ℝ) * t) ^ 3 := div_le_div_of_nonneg_right hE (by positivity)
      _ ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hpow
      _ ≤ _ := (poisson_three_mass_lower rate hr.le hr3).trans htail

end Freezing1
