module

public import Freezing1.UniformBirthMomentConclusions

/-! The Bennett integral as an ordinary real conditional expectation. -/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem expected_bennettMomentIntegral_ne_top (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (hn : 1 ≤ n) {q : ℝ} (hq : 0 < q) :
    (∫⁻ z, bennettMomentIntegral q (randomMean x n h z) ∂auxiliaryLaw x n h) ≠ ∞ := by
  apply ne_top_of_le_ne_top (bennettMomentIntegral_ne_top hq (by norm_num : (0 : ℝ) < 1 / 2))
  calc
    _ ≤ ∫⁻ _z, bennettMomentIntegral q (1 / 2) ∂auxiliaryLaw x n h := by
      apply lintegral_mono_ae
      filter_upwards [randomMean_ge_half x n h hn] with z hz
      exact bennettMomentIntegral_antitone_mean hz q
    _ = _ := by simp

theorem bennettMomentIntegral_finite_ae (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (hn : 1 ≤ n) {q : ℝ} (hq : 0 < q) :
    ∀ᵐ z ∂auxiliaryLaw x n h, bennettMomentIntegral q (randomMean x n h z) < ∞ := by
  filter_upwards [randomMean_ge_half x n h hn] with z hz
  exact (bennettMomentIntegral_antitone_mean hz q).trans_lt
    (lt_top_iff_ne_top.mpr (bennettMomentIntegral_ne_top hq (by norm_num)))

theorem realBennettIntegral_integrable (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (hn : 1 ≤ n) {q : ℝ} (hq : 0 < q) :
    Integrable (fun z => (bennettMomentIntegral q (randomMean x n h z)).toReal)
      (auxiliaryLaw x n h) := by
  apply (integrable_const (bennettMomentIntegral q (1 / 2)).toReal).mono'
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [randomMean_ge_half x n h hn] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (bennettMomentIntegral_ne_top hq (by norm_num))
    (bennettMomentIntegral_antitone_mean hz q)

/-- Source 1440 with ordinary real expectations, rather than a totalized
infinite real integral. Finiteness is proved on every positive row. -/
theorem randomRelativeError_real_bennett_bound (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (hn : 1 ≤ n) {q : ℝ} (hq : 0 < q) :
    (∫ z, |randomRelativeError x n h z| ^ q ∂auxiliaryLaw x n h) ≤
      (2 * q) * ∫ z, (bennettMomentIntegral q (randomMean x n h z)).toReal
        ∂auxiliaryLaw x n h := by
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (expected_bennettMomentIntegral_ne_top x n h hn hq))
    (randomRelativeError_bennett_integral_bound x n h hn hq)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * q),
    ← integral_toReal (measurable_of_countable _).aemeasurable
      (bennettMomentIntegral_finite_ae x n h hn hq)] at hh
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (abs_nonneg _) _))
    (measurable_of_countable _).aestronglyMeasurable]
  exact hh

theorem expected_realBennettIntegral_tendsto (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => ∫ z, (bennettMomentIntegral q (randomMean (rows n) n (hrows n) z)).toReal
      ∂auxiliaryLaw (rows n) n (hrows n)) atTop (nhds 0) := by
  have hh := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp
    (expected_bennettMomentIntegral_tendsto rows hrows hbulk hq)
  simp only [Function.comp_def, ENNReal.toReal_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact (integral_toReal (measurable_of_countable _).aemeasurable
    (bennettMomentIntegral_finite_ae (rows n) n (hrows n) hn hq)).symm

end Freezing1.UniformBirth
