module

public import Freezing1.PoissonLowerTail

/-!
# Quantitative strict Poisson tails with the actual integer rounding

The witness is `floor(rate * t) + 1`, including integral thresholds.
The finite correction is explicit; no ceiling-factorial estimate is
assumed. This supplies the polynomial prefactor needed by source A56.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

set_option backward.isDefEq.respectTransparency false

theorem poisson_strict_log_singleton_rounding_lower (rate : ℝ≥0)
    (hr : 0 < rate) {t : ℝ} (ht : 1 < t) :
    -(rate : ℝ) * bennettRate (t - 1) + Real.log (rate : ℝ) -
        2 * Real.log ((rate : ℝ) * t + 1) - 1 ≤
      Real.log ((poissonMeasure rate).real {strictPoissonCutoff rate t}) := by
  let u : ℝ := (rate : ℝ) * t
  let k : ℕ := strictPoissonCutoff rate t
  have hr0 : (0 : ℝ) < rate := hr
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := mul_pos hr0 ht0
  have hk1 : 1 ≤ k := by dsimp [k, strictPoissonCutoff]; omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have huk : u < (k : ℝ) := threshold_lt_strictPoissonCutoff rate t
  have hku : (k : ℝ) ≤ u + 1 := strictPoissonCutoff_le rate t hu0.le
  have hdelta : (k : ℝ) - u ≤ 1 := by linarith
  have hrk : (rate : ℝ) ≤ k := by dsimp only [u] at huk; nlinarith
  have hlogkr : 0 ≤ Real.log (k : ℝ) - Real.log (rate : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hr0 hrk)
  have hlogku := Real.log_le_sub_one_of_pos (div_pos hk0 hu0)
  rw [Real.log_div hk0.ne' hu0.ne'] at hlogku
  have hloginc : u * (Real.log (k : ℝ) - Real.log u) ≤ (k : ℝ) - u := by
    have hh := mul_le_mul_of_nonneg_left hlogku hu0.le
    have he : u * ((k : ℝ) / u - 1) = (k : ℝ) - u := by field_simp
    rwa [he] at hh
  have hround := mul_le_mul_of_nonneg_right hdelta hlogkr
  have hcompare : u * (1 + Real.log (rate : ℝ) - Real.log u) -
      (Real.log (k : ℝ) - Real.log (rate : ℝ)) ≤
        (k : ℝ) * (1 + Real.log (rate : ℝ) - Real.log (k : ℝ)) := by
    nlinarith
  have hentropy : -(rate : ℝ) + u * (1 + Real.log (rate : ℝ) - Real.log u) =
      -(rate : ℝ) * bennettRate (t - 1) := by
    dsimp only [u]
    rw [Real.log_mul hr0.ne' ht0.ne']
    simp only [bennettRate, show 1 + (t - 1) = t by ring]
    ring
  have hlogk := Real.log_le_log hk0 hku
  have hmass := poisson_log_singleton_lower rate hr hk1
  change -(rate : ℝ) * bennettRate (t - 1) + Real.log (rate : ℝ) -
    2 * Real.log (u + 1) - 1 ≤ _
  nlinarith

/-- A finite bound valid for every positive rate and every `t > 1`, with
the full loss from the strict integer cutoff displayed. -/
theorem poisson_strict_tail_rounding_lower (rate : ℝ≥0) (hr : 0 < rate)
    {t : ℝ} (ht : 1 < t) :
    Real.exp (-(rate : ℝ) * bennettRate (t - 1)) * (rate : ℝ) /
        (Real.exp 1 * ((rate : ℝ) * t + 1) ^ 2) ≤
      (poissonMeasure rate).real {k : ℕ | (rate : ℝ) * t < (k : ℝ)} := by
  have hr0 : (0 : ℝ) < rate := hr
  have ht0 : 0 < t := by linarith
  have hu : 0 < (rate : ℝ) * t + 1 := by positivity
  have hmasspos := poissonMeasure_real_singleton_pos (strictPoissonCutoff rate t) hr
  have hR : 0 < Real.exp (-(rate : ℝ) * bennettRate (t - 1)) * (rate : ℝ) /
      (Real.exp 1 * ((rate : ℝ) * t + 1) ^ 2) := by positivity
  have hlogR : Real.log (Real.exp (-(rate : ℝ) * bennettRate (t - 1)) * (rate : ℝ) /
      (Real.exp 1 * ((rate : ℝ) * t + 1) ^ 2)) =
      -(rate : ℝ) * bennettRate (t - 1) + Real.log (rate : ℝ) -
        2 * Real.log ((rate : ℝ) * t + 1) - 1 := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) hr0.ne',
      Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_exp,
      Real.log_pow]
    ring
  have hlog := poisson_strict_log_singleton_rounding_lower rate hr ht
  rw [← hlogR] at hlog
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hR, Real.exp_log hmasspos] at he
  exact he.trans (poisson_singleton_le_strict_tail rate t)

end Freezing1
