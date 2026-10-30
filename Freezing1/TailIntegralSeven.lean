module

public import Freezing1.ActiveHeightTailIntegral

/-! A reusable real-power moment bound from the source's split at seven. -/

@[expose] public section

namespace Freezing1

open Filter Set MeasureTheory
open scoped Classical

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem moment_le_seven_of_bennett_tail {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hn : 0 ≤ᵐ[μ] f) {p : ℝ} (hp : 1 ≤ p)
    (hi : Integrable (fun ω => f ω ^ p) μ)
    (htail : ∀ u : ℝ, 7 < u → μ.real {ω | u ≤ f ω} ≤ Real.exp (-bennettRate u / 2)) :
    (∫ ω, f ω ^ p ∂μ) ≤
      (7 : ℝ) ^ p + p * ∫ u in Ioi (7 : ℝ), bennettMomentDensity p (1 / 2) u := by
  have hp0 : 0 < p := by linarith
  have hint := rpow_layercake_real_integrable hf hn hp0 hi
  have hit := hint.mono_set
    (show Ioi (7 : ℝ) ⊆ Ioi 0 by intro u hu; exact lt_trans (by norm_num) hu)
  have hil : IntervalIntegrable (realMomentTailDensity μ f p) volume 0 7 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 7)).mpr
      (hint.mono_set Ioc_subset_Ioi_self)
  have hipow : IntervalIntegrable (fun u : ℝ => u ^ (p - 1)) volume 0 7 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hlow : (∫ u in (0 : ℝ)..7, realMomentTailDensity μ f p u) ≤ (7 : ℝ) ^ p / p := by
    have hh := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 7) hil hipow
      (fun u hu => show realMomentTailDensity μ f p u ≤ u ^ (p - 1) by
        have hb : μ.real {ω | u ≤ f ω} ≤ 1 := measureReal_le_one
        simpa only [realMomentTailDensity, one_mul] using
          mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hu.1 _))
    rw [integral_rpow (Or.inl (by linarith : -1 < p - 1))] at hh
    simpa only [sub_add_cancel, Real.zero_rpow hp0.ne', sub_zero] using hh
  have hhigh : (∫ u in Ioi (7 : ℝ), realMomentTailDensity μ f p u) ≤
      ∫ u in Ioi (7 : ℝ), bennettMomentDensity p (1 / 2) u := by
    apply integral_mono_ae hit
      (IntegrableOn.mono_set
        (integrable_bennettMomentDensity hp0 (by norm_num : (0 : ℝ) < 1 / 2))
        (show Ioi (7 : ℝ) ⊆ Ioi 0 by intro u hu; exact lt_trans (by norm_num) hu))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hh := mul_le_mul_of_nonneg_right (htail u hu)
      (Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 7) hu)) (p - 1))
    simpa only [realMomentTailDensity, bennettMomentDensity,
      show -bennettRate u / 2 = -(1 / 2) * bennettRate u by ring] using hh
  rw [rpow_layercake_real hf hn hp0,
    ← intervalIntegral.integral_interval_add_Ioi hint hit]
  have hlow' := (le_div_iff₀ hp0).mp hlow
  nlinarith

end Freezing1
