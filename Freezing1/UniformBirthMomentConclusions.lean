module

public import Freezing1.UniformBirthRelativeMomentLimit
public import Freezing1.UniformBirthConditionalMoments

/-! The real expectations and the sum normalization in the source proof. -/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem randomRelativeError_integrable_rpow (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun z => |randomRelativeError x n h z| ^ q) (auxiliaryLaw x n h) :=
  relativeMoment_integrable x n h hq

theorem randomRelativeError_real_moment_tendsto (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => ∫ z, |randomRelativeError (rows n) n (hrows n) z| ^ q
      ∂auxiliaryLaw (rows n) n (hrows n)) atTop (nhds 0) := by
  have hh := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp
    (randomRelativeError_moment_tendsto rows hrows hbulk hq)
  simp only [ENNReal.toReal_zero, Function.comp_def] at hh
  convert hh using 1
  funext n
  exact integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (abs_nonneg _) _))
    (measurable_of_countable _).aestronglyMeasurable

theorem centeredScaleError_integrable_rpow (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun z => |centeredScaleError x n h z| ^ q) (auxiliaryLaw x n h) := by
  by_cases hn : n = 0
  · subst n
    simpa only [centeredScaleError, randomSum_zero, randomMean_zero, sub_self, zero_div,
      abs_zero] using
      (integrable_const ((0 : ℝ) ^ q) : Integrable (fun _ : ℕ × (Fin 0 → ℕ) => (0 : ℝ) ^ q)
        (auxiliaryLaw x 0 h))
  apply (randomRelativeError_integrable_rpow x n h hq).mono'
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [centeredScaleError_abs_le_relative x n h (Nat.one_le_iff_ne_zero.mpr hn)] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) hz hq

theorem centeredScaleError_real_moment_le_relative (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (hn : 1 ≤ n) {q : ℝ} (hq : 0 ≤ q) :
    (∫ z, |centeredScaleError x n h z| ^ q ∂auxiliaryLaw x n h) ≤
      ∫ z, |randomRelativeError x n h z| ^ q ∂auxiliaryLaw x n h := by
  apply integral_mono_ae (centeredScaleError_integrable_rpow x n h hq)
    (randomRelativeError_integrable_rpow x n h hq)
  filter_upwards [centeredScaleError_abs_le_relative x n h hn] with z hz
  exact Real.rpow_le_rpow (abs_nonneg _) hz hq

theorem centeredScaleError_real_moment_tendsto (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => ∫ z, |centeredScaleError (rows n) n (hrows n) z| ^ q
      ∂auxiliaryLaw (rows n) n (hrows n)) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (randomRelativeError_real_moment_tendsto rows hrows hbulk hq)
    (Eventually.of_forall (fun _ => integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact centeredScaleError_real_moment_le_relative (rows n) n (hrows n) hn hq.le

noncomputable def sumNormalizationError (x : SignSequence) (n : ℕ) (_h : PositiveThrough x n)
    (z : ℕ × (Fin n → ℕ)) : ℝ := randomSum x z / heightScale x n - 1

theorem sumNormalizationError_eq_add (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    sumNormalizationError x n h = centeredScaleError x n h + meanNormalizationError x n h := by
  funext z
  simp only [sumNormalizationError, centeredScaleError, meanNormalizationError, Pi.add_apply, sub_div]
  ring

/-- Source 1445: the source's random-mean proof itself yields Z_n/h_n→1. -/
theorem randomSum_normalized_tendsto_Lp (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm (sumNormalizationError (rows n) n (hrows n))
      (ENNReal.ofReal p) (auxiliaryLaw (rows n) n (hrows n))) atTop (nhds 0) := by
  have hp0 : 0 < p := by linarith
  have hh := (centeredScaleError_tendsto_Lp rows hrows hbulk hp0).add
    (randomMean_normalized_tendsto_Lp rows hrows hbulk hp)
  rw [add_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
    (Eventually.of_forall (fun _ => bot_le))
  apply Eventually.of_forall
  intro n
  rw [sumNormalizationError_eq_add]
  exact eLpNorm_add_le (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)

end Freezing1.UniformBirth
