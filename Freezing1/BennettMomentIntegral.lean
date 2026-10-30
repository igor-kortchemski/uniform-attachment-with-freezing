module

public import Freezing1.RateFunction
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Bennett tail integral for every positive real moment

The nonnegative integral remains extended-valued at zero mean. Positive
means have finite integrals, and a fixed positive lower mean gives a
dominating Gamma density for the source's conditional-moment argument.
-/

@[expose] public section

namespace Freezing1

open Filter Set MeasureTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

noncomputable def bennettMomentDensity (q m u : ℝ) : ℝ :=
  Real.exp (-m * bennettRate u) * u ^ (q - 1)

noncomputable def bennettMomentIntegral (q m : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (bennettMomentDensity q m u)

theorem bennettRate_linear_lower {u : ℝ} (hu : 0 ≤ u) :
    u - Real.exp 2 ≤ bennettRate u := by
  by_cases hsmall : u ≤ Real.exp 2
  · exact (sub_nonpos.mpr hsmall).trans (bennettRate_nonneg hu)
  · have hlog : 2 ≤ Real.log (1 + u) := by
      apply (Real.le_log_iff_exp_le (by linarith : 0 < 1 + u)).mpr
      linarith
    unfold bennettRate
    nlinarith [Real.exp_pos (2 : ℝ)]

theorem bennettMomentDensity_nonneg {u : ℝ} (hu : 0 ≤ u) (q m : ℝ) :
    0 ≤ bennettMomentDensity q m u :=
  mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hu _)

theorem measurable_bennettMomentDensity (q m : ℝ) : Measurable (bennettMomentDensity q m) := by
  unfold bennettMomentDensity bennettRate
  fun_prop

theorem bennettMomentDensity_le_gamma {u m : ℝ} (hu : 0 ≤ u) (hm : 0 < m) (q : ℝ) :
    bennettMomentDensity q m u ≤ Real.exp (m * Real.exp 2) *
      (u ^ (q - 1) * Real.exp (-m * u)) := by
  have hlower := bennettRate_linear_lower hu
  have he : Real.exp (-m * bennettRate u) ≤ Real.exp (m * Real.exp 2) * Real.exp (-m * u) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hu (q - 1))
  dsimp [bennettMomentDensity]
  nlinarith [Real.exp_pos (m * Real.exp 2), Real.exp_pos (-m * u), Real.rpow_nonneg hu (q - 1)]

theorem integrable_bennettMomentDensity {q m : ℝ} (hq : 0 < q) (hm : 0 < m) :
    Integrable (bennettMomentDensity q m) (volume.restrict (Ioi (0 : ℝ))) := by
  have hgamma : Integrable (fun u : ℝ => u ^ (q - 1) * Real.exp (-m * u))
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [Real.rpow_one, IntegrableOn] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := q - 1) (p := 1) (b := m)
        (by linarith) (by norm_num) hm
  apply (hgamma.const_mul (Real.exp (m * Real.exp 2))).mono'
    (measurable_bennettMomentDensity q m).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (bennettMomentDensity_nonneg hu.le q m)]
  exact bennettMomentDensity_le_gamma hu.le hm q

theorem bennettMomentIntegral_eq_ofReal {q m : ℝ} (hq : 0 < q) (hm : 0 < m) :
    bennettMomentIntegral q m = ENNReal.ofReal
      (∫ u in Ioi (0 : ℝ), bennettMomentDensity q m u) := by
  symm
  apply ofReal_integral_eq_lintegral_ofReal (integrable_bennettMomentDensity hq hm)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact bennettMomentDensity_nonneg hu.le q m

theorem bennettMomentIntegral_ne_top {q m : ℝ} (hq : 0 < q) (hm : 0 < m) :
    bennettMomentIntegral q m ≠ ∞ := by
  rw [bennettMomentIntegral_eq_ofReal hq hm]
  exact ENNReal.ofReal_ne_top

theorem bennettMomentDensity_antitone_mean {u a b : ℝ} (hu : 0 ≤ u) (hab : a ≤ b) (q : ℝ) :
    bennettMomentDensity q b u ≤ bennettMomentDensity q a u := by
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hu (q - 1))
  apply Real.exp_le_exp.mpr
  have hg := bennettRate_nonneg hu
  nlinarith

theorem bennettMomentIntegral_antitone_mean {a b : ℝ} (hab : a ≤ b) (q : ℝ) :
    bennettMomentIntegral q b ≤ bennettMomentIntegral q a := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact ENNReal.ofReal_le_ofReal (bennettMomentDensity_antitone_mean hu.le hab q)

theorem bennettMomentIntegral_add_nat_tendsto {q a : ℝ} (hq : 0 < q) (ha : 0 < a) :
    Tendsto (fun n : ℕ => bennettMomentIntegral q (a + n)) atTop (nhds 0) := by
  have hreal : Tendsto (fun n : ℕ => ∫ u in Ioi (0 : ℝ), bennettMomentDensity q (a + n) u)
      atTop (nhds 0) := by
    have hh := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ))) (f := fun _ => (0 : ℝ)) (bennettMomentDensity q a)
      (fun n => (measurable_bennettMomentDensity q (a + (n : ℝ))).aestronglyMeasurable.restrict)
      (integrable_bennettMomentDensity hq ha) (fun n => by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        rw [Real.norm_eq_abs, abs_of_nonneg (bennettMomentDensity_nonneg hu.le q _)]
        exact bennettMomentDensity_antitone_mean hu.le (le_add_of_nonneg_right (Nat.cast_nonneg n)) q)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hg := bennettRate_pos hu
        have hx : Tendsto (fun n : ℕ => (a + n) * bennettRate u) atTop atTop :=
          (tendsto_atTop_add_const_left atTop a (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_mul_const hg
        have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hx)
        simpa only [bennettMomentDensity, Function.comp_def, neg_mul, zero_mul] using he.mul_const (u ^ (q - 1)))
    simpa only [integral_zero] using hh
  have ho := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  simp only [ENNReal.ofReal_zero] at ho
  convert ho using 1
  funext n
  exact bennettMomentIntegral_eq_ofReal hq (by positivity : 0 < a + (n : ℝ))

end Freezing1
