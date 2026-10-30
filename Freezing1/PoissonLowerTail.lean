module

public import Freezing1.RateFunction
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Strict Poisson lower tails for the linear-regime lower maximum bound

The singleton used for a strict tail is `floor (rate*t) + 1`, including when
`rate*t` is an integer. The proof uses an upper bound on log-factorials derived
from Mathlib's monotone Stirling sequence. Rate slack, rather than the printed
ceiling witness or its polynomial constants, gives the required divergence.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

/-- A logarithmic factorial upper bound, sufficient for the lower large-deviation estimate. -/
theorem log_factorial_le_entropy_add_log {k : ℕ} (hk : 1 ≤ k) :
    Real.log (k.factorial : ℝ) ≤
      (k : ℝ) * Real.log (k : ℝ) - k + Real.log (k : ℝ) + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  have hn : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hs := Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
  change Real.log (Stirling.stirlingSeq (m + 1)) ≤ Real.log (Stirling.stirlingSeq 1) at hs
  have hone : Real.log (Stirling.stirlingSeq 1) = 1 - (1 / 2 : ℝ) * Real.log 2 := by
    rw [Stirling.log_stirlingSeq_formula]
    norm_num [one_div, Real.log_inv, Real.log_exp]
    ring
  rw [hone, Stirling.log_stirlingSeq_formula,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn.ne',
    Real.log_div hn.ne' (Real.exp_ne_zero 1), Real.log_exp] at hs
  have hlog := Real.log_natCast_nonneg (m + 1)
  nlinarith

/-- The exact log mass, bounded below using the proved factorial estimate. -/
theorem poisson_log_singleton_lower (rate : ℝ≥0) (hrate : 0 < rate) {k : ℕ} (hk : 1 ≤ k) :
    -(rate : ℝ) + k * (1 + Real.log (rate : ℝ) - Real.log (k : ℝ)) - Real.log (k : ℝ) - 1 ≤
      Real.log ((poissonMeasure rate).real {k}) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrate0 : (0 : ℝ) < rate := hrate
  rw [poissonMeasure_real_singleton,
    Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_pow]
  have hf := log_factorial_le_entropy_add_log hk
  nlinarith

/-- Positive logarithmic Poisson rates, with harmless zero values at `n=0,1`. -/
noncomputable def logarithmicPoissonRate (K : ℝ) (hK : 0 ≤ K) (n : ℕ) : ℝ≥0 :=
  ⟨K * Real.log (n : ℝ), mul_nonneg hK (Real.log_natCast_nonneg n)⟩

@[simp] theorem logarithmicPoissonRate_coe (K : ℝ) (hK : 0 ≤ K) (n : ℕ) :
    (logarithmicPoissonRate K hK n : ℝ) = K * Real.log (n : ℝ) := rfl

/-- The least natural number strictly exceeding the real tail threshold. -/
noncomputable def strictPoissonCutoff (rate t : ℝ) : ℕ := Nat.floor (rate * t) + 1

theorem threshold_lt_strictPoissonCutoff (rate t : ℝ) :
    rate * t < (strictPoissonCutoff rate t : ℝ) := by
  simpa only [strictPoissonCutoff, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (rate * t)

theorem strictPoissonCutoff_le (rate t : ℝ) (h : 0 ≤ rate * t) :
    (strictPoissonCutoff rate t : ℝ) ≤ rate * t + 1 := by
  have hf := Nat.floor_le h
  simp only [strictPoissonCutoff, Nat.cast_add, Nat.cast_one]
  linarith

/-- The corrected singleton really belongs to the strict Poisson upper tail. -/
theorem poisson_singleton_le_strict_tail (rate : ℝ≥0) (t : ℝ) :
    (poissonMeasure rate).real {strictPoissonCutoff rate t} ≤
      (poissonMeasure rate).real {k : ℕ | (rate : ℝ) * t < (k : ℝ)} := by
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro k hk
  obtain rfl := Set.mem_singleton_iff.mp hk
  exact threshold_lt_strictPoissonCutoff rate t

/-- The strict integer cutoff has the expected logarithmic scale. -/
theorem tendsto_strictPoissonCutoff_div_log {K t : ℝ} (hK : 0 < K) (ht : 0 < t) :
    Tendsto (fun n : ℕ => (strictPoissonCutoff (K * Real.log (n : ℝ)) t : ℝ) /
      Real.log (n : ℝ)) atTop (𝓝 (K * t)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using tendsto_const_nhds.add hi) ?_ ?_
  · filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    apply (le_div_iff₀ hn).mpr
    have hh := (threshold_lt_strictPoissonCutoff (K * Real.log (n : ℝ)) t).le
    nlinarith
  · filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    apply (div_le_iff₀ hn).mpr
    have hh := strictPoissonCutoff_le (K * Real.log (n : ℝ)) t (by positivity)
    have he : (K * t + 1 / Real.log (n : ℝ)) * Real.log (n : ℝ) =
        K * Real.log (n : ℝ) * t + 1 := by field_simp
    rw [he]
    exact hh

/-- A positive sequence of logarithmic order has a negligible logarithm
on the original logarithmic scale. -/
theorem tendsto_log_div_log_of_div_log_limit {a : ℕ → ℝ} {b : ℝ}
    (ha : ∀ n, 0 < a n) (hb : 0 < b)
    (hab : Tendsto (fun n : ℕ => a n / Real.log (n : ℝ)) atTop (𝓝 b)) :
    Tendsto (fun n : ℕ => Real.log (a n) / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := (Real.continuousAt_log hb.ne').tendsto.comp hab
  have hsmall := hratio.div_atTop hlog
  have hloglog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hh := hsmall.add hloglog
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  dsimp
  rw [Real.log_div (ha n).ne' hn.ne']
  ring

/-- Strict Poisson upper tails beat `1/n` whenever their rate is below one.
The actual probability measure and the strict integer rounding are both retained. -/
theorem tendsto_nat_mul_poisson_strict_tail_atTop {K t : ℝ}
    (hK : 0 < K) (ht : 1 < t) (hrate : K * bennettRate (t - 1) < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (poissonMeasure (logarithmicPoissonRate K hK.le n)).real
        {k : ℕ | K * Real.log (n : ℝ) * t < (k : ℝ)}) atTop atTop := by
  let a : ℕ → ℕ := fun n => strictPoissonCutoff (K * Real.log (n : ℝ)) t
  let E : ℕ → ℝ := fun n => Real.log (n : ℝ) - K * Real.log (n : ℝ) +
    (a n : ℝ) * (1 - Real.log ((a n : ℝ) / (K * Real.log (n : ℝ)))) -
      Real.log (a n : ℝ) - 1
  have ht0 : 0 < t := by linarith
  have ha : ∀ n, (0 : ℝ) < a n := by
    intro n
    dsimp [a, strictPoissonCutoff]
    positivity
  have ha_lim : Tendsto (fun n : ℕ => (a n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 (K * t)) :=
    tendsto_strictPoissonCutoff_div_log hK ht0
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have ha_rate : Tendsto (fun n : ℕ => (a n : ℝ) / (K * Real.log (n : ℝ))) atTop (𝓝 t) := by
    have hh := ha_lim.div_const K
    have hlim : K * t / K = t := by field_simp
    rw [hlim] at hh
    apply hh.congr'
    filter_upwards [] with n
    rw [div_div, mul_comm (Real.log (n : ℝ)) K]
  have hlogratio := (Real.continuousAt_log ht0.ne').tendsto.comp ha_rate
  have hloga := tendsto_log_div_log_of_div_log_limit ha (mul_pos hK ht0) ha_lim
  have hE : Tendsto (fun n : ℕ => E n / Real.log (n : ℝ)) atTop
      (𝓝 (1 - K * bennettRate (t - 1))) := by
    have hh := (((tendsto_const_nhds (x := 1 - K)).add
      (ha_lim.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hlogratio))).sub hloga).sub hi
    have heq : 1 - K + K * t * (1 - Real.log t) - 0 - 0 =
        1 - K * bennettRate (t - 1) := by
      simp only [bennettRate, show 1 + (t - 1) = t by ring]
      ring
    rw [heq] at hh
    apply hh.congr'
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    dsimp [E]
    field_simp
  have hEinf : Tendsto E atTop atTop := by
    have hh := hE.pos_mul_atTop (by linarith : 0 < 1 - K * bennettRate (t - 1)) hlog
    apply hh.congr'
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    exact div_mul_cancel₀ _ hn.ne'
  have hexp := Real.tendsto_exp_atTop.comp hEinf
  apply tendsto_atTop_mono' _ ?_ hexp
  filter_upwards [eventually_ge_atTop 2, hlog.eventually_gt_atTop 0] with n hn hnlog
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr0 : (0 : ℝ) < K * Real.log (n : ℝ) := mul_pos hK hnlog
  have hr : 0 < logarithmicPoissonRate K hK.le n := hr0
  have hak : 1 ≤ a n := by dsimp [a, strictPoissonCutoff]; omega
  have hp := poisson_log_singleton_lower (logarithmicPoissonRate K hK.le n) hr hak
  simp only [logarithmicPoissonRate_coe] at hp
  have hmpos := poissonMeasure_real_singleton_pos (a n) hr
  have he : E n ≤ Real.log ((n : ℝ) *
      (poissonMeasure (logarithmicPoissonRate K hK.le n)).real {a n}) := by
    rw [Real.log_mul hn0.ne' hmpos.ne']
    dsimp [E]
    rw [Real.log_div (ha n).ne' hr0.ne']
    linarith
  have hexpbound := Real.exp_le_exp.mpr he
  rw [Real.exp_log (mul_pos hn0 hmpos)] at hexpbound
  refine hexpbound.trans ?_
  exact mul_le_mul_of_nonneg_left
    (poisson_singleton_le_strict_tail (logarithmicPoissonRate K hK.le n) t) hn0.le

/-- The source's logarithmic Poisson parameter in the linear regime. -/
noncomputable def linearPoissonRate (c : LinearRegimeParameter) (n : ℕ) : ℝ≥0 :=
  logarithmicPoissonRate (((c : ℝ) + 1) / (2 * (c : ℝ))) (by have hc := c.property.1; positivity) n

/-- The required Poisson tail dominates `1/n` for every positive margin below
`f(c)`. A threshold in `(1,f(c))` handles larger margins by monotonicity. -/
theorem linear_poisson_strict_tail_atTop (c : LinearRegimeParameter)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => (n : ℝ) * (poissonMeasure (linearPoissonRate c n)).real
      {k : ℕ | (linearPoissonRate c n : ℝ) * (linearHeightFactor c - η) < (k : ℝ)})
      atTop atTop := by
  let K : ℝ := ((c : ℝ) + 1) / (2 * (c : ℝ))
  let t : ℝ := max ((linearHeightFactor c + 1) / 2) (linearHeightFactor c - η)
  have hc := c.property.1
  have hcp : (0 : ℝ) < (c : ℝ) + 1 := by linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hf := one_lt_linearHeightFactor c
  have ht : 1 < t := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have htf : t < linearHeightFactor c := by apply max_lt <;> linarith
  have hthreshold : linearHeightFactor c - η ≤ t := le_max_right _ _
  have hrate : K * bennettRate (t - 1) < 1 := by
    have hg := strictMonoOn_bennettRate
      (by linarith : 0 ≤ t - 1) (by linarith : 0 ≤ linearHeightFactor c - 1)
      (by linarith : t - 1 < linearHeightFactor c - 1)
    rw [bennettRate_linearHeightFactor] at hg
    have hmul := mul_lt_mul_of_pos_left hg hK
    have he : K * (2 * (c : ℝ) / ((c : ℝ) + 1)) = 1 := by
      dsimp [K]
      field_simp
    rwa [he] at hmul
  have hlim := tendsto_nat_mul_poisson_strict_tail_atTop hK ht hrate
  apply tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [] with n
  apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro k hk
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hthreshold (NNReal.coe_nonneg _)) hk

/-- The corrected scalar input to the source's `6/(c*C)` block estimate.
The integer scale can satisfy the original size condition and have rate above two. -/
theorem exists_linear_poisson_tail_scale (c : LinearRegimeParameter)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      (2 : ℝ) < linearPoissonRate c C ∧
      6 / ((c : ℝ) * C) ≤ (poissonMeasure (linearPoissonRate c C)).real
        {k : ℕ | (linearPoissonRate c C : ℝ) * (linearHeightFactor c - η) < (k : ℝ)} := by
  let K : ℝ := ((c : ℝ) + 1) / (2 * (c : ℝ))
  have hc := c.property.1
  have hcp : (0 : ℝ) < (c : ℝ) + 1 := by linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun n : ℕ => (linearPoissonRate c n : ℝ)) atTop atTop :=
    hlog.const_mul_atTop hK
  have hP := linear_poisson_strict_tail_atTop c hη
  have he := ((eventually_ge_atTop 2).and
    (hlog.eventually_ge_atTop (K * (linearHeightFactor c - η)))).and
    ((hr.eventually_gt_atTop 2).and (hP.eventually_ge_atTop (6 / (c : ℝ))))
  obtain ⟨C, ⟨hC, hlogC⟩, hrC, hpC⟩ := he.exists
  refine ⟨C, by omega, hlogC, hrC, ?_⟩
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  apply (div_le_iff₀ (mul_pos c.property.1 hC0)).mpr
  have hmul := (div_le_iff₀ c.property.1).mp hpC
  nlinarith

end Freezing1
