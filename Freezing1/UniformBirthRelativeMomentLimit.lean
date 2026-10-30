module

public import Freezing1.UniformBirthRelativeMomentLaw
public import Freezing1.UniformBirthMeanEscape

/-!
# The actual birth-truncated relative moments

These are moments under the independent product construction whose joint
birth/height law was proved equal to the actual uniform reverse-tree law.
The zero-mean initial row is not modified. Positive rows use the proved
almost-sure lower bound on the genuine conditional mean.
-/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

noncomputable def randomRelativeError (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (z : ℕ × (Fin n → ℕ)) : ℝ := fixedRelativeError x n h z.1 z.2

theorem fixedRelativeError_bennett_integral_bound (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (b : ℕ) (hm : 0 < truncatedMean x n h b)
    {q : ℝ} (hq : 0 < q) :
    (∫⁻ Y, ENNReal.ofReal (|fixedRelativeError x n h b Y| ^ q)
      ∂bernoulliProductLaw (reciprocalParameter x n h)) ≤
      ENNReal.ofReal (2 * q) * bennettMomentIntegral q (truncatedMean x n h b) := by
  have he (u : ℝ) :
      ENNReal.ofReal (2 * Real.exp (-truncatedMean x n h b * bennettRate u)) *
        ENNReal.ofReal (u ^ (q - 1)) =
      (2 : ℝ≥0∞) * ENNReal.ofReal (bennettMomentDensity q (truncatedMean x n h b) u) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [bennettMomentDensity, ENNReal.ofReal_mul (Real.exp_pos _).le]
    norm_num only [ENNReal.ofReal_ofNat]
    ac_rfl
  calc
    _ ≤ ENNReal.ofReal q * ∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (2 * Real.exp (-truncatedMean x n h b * bennettRate u)) *
          ENNReal.ofReal (u ^ (q - 1)) :=
      fixedRelativeError_bennett_moment_bound x n h b hm hq
    _ = ENNReal.ofReal q * ((2 : ℝ≥0∞) *
        bennettMomentIntegral q (truncatedMean x n h b)) := by
      simp_rw [he]
      rw [lintegral_const_mul' _ _ (by norm_num)]
      rfl
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      ac_rfl

theorem birthLaw_pos (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (hn : 1 ≤ n) :
    ∀ᵐ b ∂birthLaw x n, 1 ≤ b := by
  rw [birthLaw, ae_map_iff (measurable_of_countable _).aemeasurable (by measurability)]
  filter_upwards [uniformVertex_supported x n] with v hv
  exact birthTime_pos_of_mem h hn hv

theorem randomRelativeError_bennett_integral_bound (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (hn : 1 ≤ n) {q : ℝ} (hq : 0 < q) :
    (∫⁻ z, ENNReal.ofReal (|randomRelativeError x n h z| ^ q) ∂auxiliaryLaw x n h) ≤
      ENNReal.ofReal (2 * q) * ∫⁻ z, bennettMomentIntegral q (randomMean x n h z)
        ∂auxiliaryLaw x n h := by
  have := birthLaw_probability x n h
  rw [auxiliaryLaw, lintegral_prod _ (measurable_of_countable _).aemeasurable]
  calc
    _ ≤ ∫⁻ b, ENNReal.ofReal (2 * q) * bennettMomentIntegral q (truncatedMean x n h b)
        ∂birthLaw x n := by
      apply lintegral_mono_ae
      filter_upwards [birthLaw_pos x n h hn] with b hb
      exact fixedRelativeError_bennett_integral_bound x n h b
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (truncatedMean_ge_half x n h hn hb)) hq
    _ = ENNReal.ofReal (2 * q) * ∫⁻ b, bennettMomentIntegral q (truncatedMean x n h b)
        ∂birthLaw x n := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      congr 1
      symm
      exact (auxiliary_birth_hasLaw x n h).lintegral_comp
        (f := fun b => bennettMomentIntegral q (truncatedMean x n h b))
        (measurable_of_countable _).aemeasurable

/-- Source 1431--1440: no random-mean convergence or moment premise is
assumed. Both are proved for the actual birth law. -/
theorem randomRelativeError_moment_tendsto (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (|randomRelativeError (rows n) n (hrows n) z| ^ q)
      ∂auxiliaryLaw (rows n) n (hrows n)) atTop (nhds 0) := by
  have hh := (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
    (ENNReal.ofReal_ne_top : ENNReal.ofReal (2 * q) ≠ ∞) (by norm_num : (0 : ℝ) < 1)).comp
      (expected_bennettMomentIntegral_tendsto rows hrows hbulk hq)
  simp only [ENNReal.rpow_one, Function.comp_def] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact randomRelativeError_bennett_integral_bound (rows n) n (hrows n) hn hq

theorem randomRelativeError_tendsto_Lp (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n => eLpNorm (randomRelativeError (rows n) n (hrows n))
      (ENNReal.ofReal p) (auxiliaryLaw (rows n) n (hrows n))) atTop (nhds 0) := by
  have hh := (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
    (c := (1 : ℝ≥0∞)) (by simp) (by positivity : 0 < 1 / p)).comp
      (randomRelativeError_moment_tendsto rows hrows hbulk hp)
  simp only [one_mul, Function.comp_def] at hh
  convert hh using 1
  funext n
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
      (measurable_of_countable _).aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  congr 2
  funext z
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]

noncomputable def centeredScaleError (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (z : ℕ × (Fin n → ℕ)) : ℝ := (randomSum x z - randomMean x n h z) / heightScale x n

theorem centeredScaleError_abs_le_relative (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (hn : 1 ≤ n) :
    ∀ᵐ z ∂auxiliaryLaw x n h, |centeredScaleError x n h z| ≤ |randomRelativeError x n h z| := by
  filter_upwards [randomMean_ge_half x n h hn] with z hz
  have hm : 0 < randomMean x n h z := by linarith
  have hs := heightScale_pos hn h
  have hb := (randomMean_bounds x n h z).2
  have he : centeredScaleError x n h z =
      (randomMean x n h z / heightScale x n) * randomRelativeError x n h z := by
    have hm0 : truncatedMean x n h z.1 ≠ 0 := hm.ne'
    unfold centeredScaleError randomRelativeError fixedRelativeError randomSum randomMean
    field_simp [hm0]
  rw [he, abs_mul, abs_of_nonneg (div_nonneg hm.le hs.le)]
  exact mul_le_of_le_one_left (abs_nonneg _) ((div_le_one hs).mpr hb)

theorem centeredScaleError_tendsto_Lp (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n => eLpNorm (centeredScaleError (rows n) n (hrows n))
      (ENNReal.ofReal p) (auxiliaryLaw (rows n) n (hrows n))) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (randomRelativeError_tendsto_Lp rows hrows hbulk hp)
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact eLpNorm_mono_ae (measurable_of_countable _).aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using centeredScaleError_abs_le_relative (rows n) n (hrows n) hn)

end Freezing1.UniformBirth
