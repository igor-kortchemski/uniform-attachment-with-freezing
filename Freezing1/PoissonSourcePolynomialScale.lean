module

public import Freezing1.PoissonSourcePolynomialBound

/-! The literal logarithmic polynomial prefactor and large integer scale
choice in A56. The finite rounding constraint is explicit, and supplied
eventually by `log C → ∞`; the safe-threshold general-margin repair remains
visible in the final source specialization. -/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

set_option backward.isDefEq.respectTransparency false

theorem logarithmicPoisson_polynomial_lower {K t : ℝ} (hK : 0 < K) (ht : 1 < t)
    (C : ℕ) (hC : 1 < C) (hr : 2 < K * Real.log (C : ℝ))
    (hround : (K * t) ^ 3 ≤ Real.log (C : ℝ)) :
    Real.exp (-(K * Real.log (C : ℝ)) * bennettRate (t - 1)) / Real.log (C : ℝ) ^ 4 ≤
      (poissonMeasure (logarithmicPoissonRate K hK.le C)).real
        {k : ℕ | K * Real.log (C : ℝ) * t < (k : ℝ)} := by
  have hL : 0 < Real.log (C : ℝ) := Real.log_pos (by exact_mod_cast hC)
  have hu : 0 < K * Real.log (C : ℝ) * t := by positivity
  have hden : (K * Real.log (C : ℝ) * t) ^ 3 ≤ Real.log (C : ℝ) ^ 4 := by
    have hh := mul_le_mul_of_nonneg_right hround (pow_nonneg hL.le 3)
    convert hh using 1 <;> ring
  have hh := div_le_div_of_nonneg_left
    (Real.exp_pos (-(K * Real.log (C : ℝ)) * bennettRate (t - 1))).le
    (pow_pos hu 3) hden
  exact hh.trans (poisson_strict_tail_cubic_lower (logarithmicPoissonRate K hK.le C) hr ht)

theorem tendsto_nat_mul_log_polynomial_atTop {q : ℝ} (hq : q < 1) :
    Tendsto (fun C : ℕ => (C : ℝ) *
      (Real.exp (-q * Real.log (C : ℝ)) / Real.log (C : ℝ) ^ 4)) atTop atTop := by
  have hlog : Tendsto (fun C : ℕ => Real.log (C : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := (tendsto_exp_mul_div_rpow_atTop 4 (1 - q) (by linarith)).comp hlog
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with C hC
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  dsimp only [Function.comp_def]
  rw [show (1 - q) * Real.log (C : ℝ) =
      Real.log (C : ℝ) + (-q * Real.log (C : ℝ)) by ring,
    Real.exp_add, Real.exp_log hC0, Real.rpow_ofNat]
  ring

theorem exists_poisson_polynomial_scale {K t c : ℝ} (hK : 0 < K) (ht : 1 < t)
    (hc : 0 < c) (hrate : K * bennettRate (t - 1) < 1) (L₀ : ℝ) :
    ∃ C : ℕ, 1 < C ∧ L₀ ≤ Real.log (C : ℝ) ∧ 2 < K * Real.log (C : ℝ) ∧
      (K * t) ^ 3 ≤ Real.log (C : ℝ) ∧
      6 / (c * C) ≤ Real.exp (-(K * Real.log (C : ℝ)) * bennettRate (t - 1)) /
        Real.log (C : ℝ) ^ 4 ∧
      Real.exp (-(K * Real.log (C : ℝ)) * bennettRate (t - 1)) / Real.log (C : ℝ) ^ 4 ≤
        (poissonMeasure (logarithmicPoissonRate K hK.le C)).real
          {k : ℕ | K * Real.log (C : ℝ) * t < (k : ℝ)} := by
  have hlog : Tendsto (fun C : ℕ => Real.log (C : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr := hlog.const_mul_atTop hK
  have hpoly := tendsto_nat_mul_log_polynomial_atTop hrate
  obtain ⟨C, hC, hL₀, hrC, hround, hbound⟩ := ((eventually_ge_atTop 2).and
    ((hlog.eventually_ge_atTop L₀).and ((hr.eventually_gt_atTop 2).and
      ((hlog.eventually_ge_atTop ((K * t) ^ 3)).and
        (hpoly.eventually_ge_atTop (6 / c)))))).exists
  have hC1 : 1 < C := by omega
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hbound' : 6 / (c * C) ≤
      Real.exp (-(K * Real.log (C : ℝ)) * bennettRate (t - 1)) / Real.log (C : ℝ) ^ 4 := by
    rw [show -(K * Real.log (C : ℝ)) * bennettRate (t - 1) =
      -(K * bennettRate (t - 1)) * Real.log (C : ℝ) by ring]
    apply (div_le_iff₀ (mul_pos hc hC0)).mpr
    have hh := (div_le_iff₀ hc).mp hbound
    nlinarith
  exact ⟨C, hC1, hL₀, hrC, hround, hbound',
    logarithmicPoisson_polynomial_lower hK ht C hC1 hrC hround⟩

theorem linear_source_rate_slack (c : LinearRegimeParameter) {t : ℝ}
    (ht : 1 < t) (htf : t < linearHeightFactor c) :
    (((c : ℝ) + 1) / (2 * (c : ℝ))) * bennettRate (t - 1) < 1 := by
  have hc := c.property.1
  have hK : 0 < ((c : ℝ) + 1) / (2 * (c : ℝ)) := by positivity
  have hg := strictMonoOn_bennettRate (by linarith : 0 ≤ t - 1)
    (by linarith [one_lt_linearHeightFactor c] : 0 ≤ linearHeightFactor c - 1)
    (by linarith : t - 1 < linearHeightFactor c - 1)
  rw [bennettRate_linearHeightFactor] at hg
  have hh := mul_lt_mul_of_pos_left hg hK
  have he : (((c : ℝ) + 1) / (2 * (c : ℝ))) * (2 * (c : ℝ) / ((c : ℝ) + 1)) = 1 := by
    field_simp
  rwa [he] at hh

/-- Exact printed exponent, whenever its threshold satisfies the explicit
`t > 1` condition of the source Poisson step. -/
theorem exists_linear_poisson_polynomial_scale (c : LinearRegimeParameter) {η : ℝ}
    (hη : 0 < η) (ht : 1 < linearHeightFactor c - η) :
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      2 < (linearPoissonRate c C : ℝ) ∧
      6 / ((c : ℝ) * C) ≤
        Real.exp (-(linearPoissonRate c C : ℝ) * bennettRate (linearHeightFactor c - 1 - η)) /
          Real.log (C : ℝ) ^ 4 ∧
      Real.exp (-(linearPoissonRate c C : ℝ) * bennettRate (linearHeightFactor c - 1 - η)) /
          Real.log (C : ℝ) ^ 4 ≤
        (poissonMeasure (linearPoissonRate c C)).real
          {k : ℕ | (linearPoissonRate c C : ℝ) * (linearHeightFactor c - η) < (k : ℝ)} := by
  let K := ((c : ℝ) + 1) / (2 * (c : ℝ))
  have hc := c.property.1
  have hK : 0 < K := by dsimp [K]; positivity
  have hslack := linear_source_rate_slack c ht (by linarith : linearHeightFactor c - η < linearHeightFactor c)
  obtain ⟨C, hC, hlog, hr, _, hlow, hhigh⟩ := exists_poisson_polynomial_scale hK ht hc hslack
    (K * (linearHeightFactor c - η))
  refine ⟨C, hC, hlog, hr, ?_, ?_⟩
  · simpa only [linearPoissonRate, logarithmicPoissonRate_coe, K,
      show linearHeightFactor c - η - 1 = linearHeightFactor c - 1 - η by ring] using hlow
  · simpa only [linearPoissonRate, logarithmicPoissonRate_coe, K,
      show linearHeightFactor c - η - 1 = linearHeightFactor c - 1 - η by ring] using hhigh

/-- Every source margin is retained. If the printed threshold is not
above one, the exponential rate is explicitly replaced by the same safe
threshold used in the existing full-scope lower-bound proof. -/
theorem exists_linear_poisson_polynomial_scale_all_margins (c : LinearRegimeParameter)
    {η : ℝ} (hη : 0 < η) :
    let t := max ((linearHeightFactor c + 1) / 2) (linearHeightFactor c - η)
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      2 < (linearPoissonRate c C : ℝ) ∧
      6 / ((c : ℝ) * C) ≤
        Real.exp (-(linearPoissonRate c C : ℝ) * bennettRate (t - 1)) / Real.log (C : ℝ) ^ 4 ∧
      Real.exp (-(linearPoissonRate c C : ℝ) * bennettRate (t - 1)) / Real.log (C : ℝ) ^ 4 ≤
        (poissonMeasure (linearPoissonRate c C)).real
          {k : ℕ | (linearPoissonRate c C : ℝ) * (linearHeightFactor c - η) < (k : ℝ)} := by
  let K := ((c : ℝ) + 1) / (2 * (c : ℝ))
  let t := max ((linearHeightFactor c + 1) / 2) (linearHeightFactor c - η)
  have hc := c.property.1
  have hf := one_lt_linearHeightFactor c
  have hK : 0 < K := by dsimp [K]; positivity
  have ht : 1 < t := lt_of_lt_of_le (by linarith : 1 < (linearHeightFactor c + 1) / 2)
    (le_max_left _ _)
  have htf : t < linearHeightFactor c := by apply max_lt <;> linarith
  have hthreshold : linearHeightFactor c - η ≤ t := le_max_right _ _
  have hslack := linear_source_rate_slack c ht htf
  obtain ⟨C, hC, hlog, hr, _, hlow, hhigh⟩ := exists_poisson_polynomial_scale hK ht hc hslack
    (K * (linearHeightFactor c - η))
  refine ⟨C, hC, hlog, hr, hlow, hhigh.trans ?_⟩
  apply measureReal_mono _ (measure_ne_top _ _)
  intro k hk
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hthreshold (NNReal.coe_nonneg _)) hk

end Freezing1
