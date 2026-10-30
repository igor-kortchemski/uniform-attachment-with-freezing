module

public import Freezing1.UniformActiveMoments
public import Freezing1.ExponentialMomentTail
public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The literal active-height moment integral and its split at seven

The layer-cake identity and the real integral are for the actual uniform
active-height law. All integrability conditions are proved. The source's
exponential-tail asymptotic is supplied for every finite real exponent by
`ExponentialMomentTail`, using a logarithmic envelope in place of repeated
integration by parts.
-/

@[expose] public section

namespace Freezing1

open Filter Set MeasureTheory ProbabilityTheory Asymptotics
open scoped Topology ENNReal Classical

set_option backward.isDefEq.respectTransparency false

section RealLayercake

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {f : Ω → ℝ}

noncomputable def realMomentTailDensity (μ : Measure Ω) (f : Ω → ℝ) (p u : ℝ) : ℝ :=
  μ.real {ω | u ≤ f ω} * u ^ (p - 1)

theorem measurable_realMomentTailDensity (μ : Measure Ω) (f : Ω → ℝ) (p : ℝ) :
    Measurable (realMomentTailDensity μ f p) := by
  have ht : Antitone (fun u : ℝ => μ {ω | u ≤ f ω}) := by
    intro u v huv
    exact measure_mono fun _ h => huv.trans h
  exact ht.measurable.ennreal_toReal.mul (by fun_prop)

omit [IsProbabilityMeasure μ] in
theorem realMomentTailDensity_nonneg {p u : ℝ} (hu : 0 ≤ u) :
    0 ≤ realMomentTailDensity μ f p u :=
  mul_nonneg measureReal_nonneg (Real.rpow_nonneg hu _)

theorem rpow_layercake_real_integrable
    (hf : AEMeasurable f μ) (hn : 0 ≤ᵐ[μ] f) {p : ℝ} (hp : 0 < p)
    (hi : Integrable (fun ω => f ω ^ p) μ) :
    IntegrableOn (realMomentTailDensity μ f p) (Ioi 0) := by
  have he : (∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ) =
      ENNReal.ofReal p * ∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (realMomentTailDensity μ f p u) := by
    rw [lintegral_rpow_eq_lintegral_meas_le_mul μ hn hf hp]
    congr 1
    apply lintegral_congr_ae
    apply Eventually.of_forall
    intro u
    simp only [realMomentTailDensity]
    rw [ENNReal.ofReal_mul measureReal_nonneg,
      Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hfin : (∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (realMomentTailDensity μ f p u)) < ⊤ := by
    have hh := hi.lintegral_lt_top
    rw [he, ENNReal.mul_lt_top_iff] at hh
    rcases hh with hh | hh | hh
    · exact hh.2
    · exact (ENNReal.ofReal_pos.mpr hp).ne' hh |>.elim
    · rw [hh]
      exact ENNReal.zero_lt_top
  refine ⟨(measurable_realMomentTailDensity μ f p).aestronglyMeasurable.restrict, ?_⟩
  rw [HasFiniteIntegral]
  have heq : (fun u : ℝ => ‖realMomentTailDensity μ f p u‖ₑ) =ᵐ[volume.restrict (Ioi 0)]
      fun u => ENNReal.ofReal (realMomentTailDensity μ f p u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (realMomentTailDensity_nonneg hu.le)]
  rwa [lintegral_congr_ae heq]

theorem rpow_layercake_real
    (hf : AEMeasurable f μ) (hn : 0 ≤ᵐ[μ] f) {p : ℝ} (hp : 0 < p) :
    (∫ ω, f ω ^ p ∂μ) = p * ∫ u in Ioi (0 : ℝ), realMomentTailDensity μ f p u := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (hn.mono fun _ h => Real.rpow_nonneg h _) (hf.pow_const p).aestronglyMeasurable,
    lintegral_rpow_eq_lintegral_meas_le_mul μ hn hf hp, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.le]
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae
    (show 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] realMomentTailDensity μ f p from
      (ae_restrict_mem measurableSet_Ioi).mono fun _ hu => realMomentTailDensity_nonneg hu.le)
    (measurable_realMomentTailDensity μ f p).aestronglyMeasurable.restrict]
  congr 1
  apply lintegral_congr_ae
  apply Eventually.of_forall
  intro u
  simp only [realMomentTailDensity]
  rw [ENNReal.ofReal_mul measureReal_nonneg,
    Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end RealLayercake

noncomputable def activeHeightTailDensity (x : SignSequence) (n : ℕ) (p u : ℝ) : ℝ :=
  (Forward.uniformActiveHeightLaw x n).real {k | u ≤ |activeHeightError x n k|} * u ^ (p - 1)

theorem activeHeight_moment_layercake (x : SignSequence) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    (∫ k, |activeHeightError x n k| ^ p ∂Forward.uniformActiveHeightLaw x n) =
      p * ∫ u in Ioi (0 : ℝ), activeHeightTailDensity x n p u :=
  rpow_layercake_real (measurable_of_countable _).aemeasurable
    (Eventually.of_forall fun _ => abs_nonneg _) hp

theorem integrable_activeHeightTailDensity (x : SignSequence) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    IntegrableOn (activeHeightTailDensity x n p) (Ioi 0) :=
  rpow_layercake_real_integrable (measurable_of_countable _).aemeasurable
    (Eventually.of_forall fun _ => abs_nonneg _) hp
    (Forward.uniformActiveHeightLaw_integrable x n _)

theorem activeHeightTailDensity_le_bennett (x : SignSequence) (n : ℕ)
    (hx : PositiveThrough x n) (hn : 1 ≤ n) (p : ℝ) {u : ℝ} (hu : 0 < u) :
    activeHeightTailDensity x n p u ≤ 2 * bennettMomentDensity p (heightScale x n) u := by
  have hh := mul_le_mul_of_nonneg_right
    (uniformActiveHeight_closed_deviation_le x n hx hn hu) (Real.rpow_nonneg hu.le (p - 1))
  simpa only [activeHeightTailDensity, activeHeightError, bennettMomentDensity, mul_assoc] using hh

theorem activeHeight_moment_le_split_seven (x : SignSequence) (n : ℕ)
    (hx : PositiveThrough x n) (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p) :
    (∫ k, |activeHeightError x n k| ^ p ∂Forward.uniformActiveHeightLaw x n) ≤
      (7 : ℝ) ^ p + 2 * p * ∫ u in Ioi (7 : ℝ), bennettMomentDensity p (heightScale x n) u := by
  have hp0 : 0 < p := by linarith
  have hm := heightScale_pos hn hx
  have hi := integrable_activeHeightTailDensity x n hp0
  have hit := hi.mono_set
    (show Ioi (7 : ℝ) ⊆ Ioi 0 by intro u hu; exact lt_trans (by norm_num) hu)
  have hil : IntervalIntegrable (activeHeightTailDensity x n p) volume 0 7 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 7)).mpr
      (hi.mono_set Ioc_subset_Ioi_self)
  have hipow : IntervalIntegrable (fun u : ℝ => u ^ (p - 1)) volume 0 7 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hlow : (∫ u in (0 : ℝ)..7, activeHeightTailDensity x n p u) ≤ (7 : ℝ) ^ p / p := by
    have hh := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 7) hil hipow
      (fun u hu => show activeHeightTailDensity x n p u ≤ u ^ (p - 1) by
        have hb : (Forward.uniformActiveHeightLaw x n).real
            {k | u ≤ |activeHeightError x n k|} ≤ 1 := measureReal_le_one
        simpa only [activeHeightTailDensity, one_mul] using
          mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hu.1 _))
    rw [integral_rpow (Or.inl (by linarith : -1 < p - 1))] at hh
    simpa only [sub_add_cancel, Real.zero_rpow hp0.ne', sub_zero] using hh
  have htail : (∫ u in Ioi (7 : ℝ), activeHeightTailDensity x n p u) ≤
      2 * ∫ u in Ioi (7 : ℝ), bennettMomentDensity p (heightScale x n) u := by
    rw [← integral_const_mul]
    apply integral_mono_ae hit
      ((IntegrableOn.mono_set (integrable_bennettMomentDensity hp0 hm)
        (show Ioi (7 : ℝ) ⊆ Ioi 0 by intro u hu; exact lt_trans (by norm_num) hu)).const_mul 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact activeHeightTailDensity_le_bennett x n hx hn p (lt_trans (by norm_num) hu)
  rw [activeHeight_moment_layercake x n hp0,
    ← intervalIntegral.integral_interval_add_Ioi hi hit]
  have hlow' := (le_div_iff₀ hp0).mp hlow
  nlinarith

theorem activeHeight_moment_le_exponentialTail (x : SignSequence) (n : ℕ)
    (hx : PositiveThrough x n) (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p) :
    (∫ k, |activeHeightError x n k| ^ p ∂Forward.uniformActiveHeightLaw x n) ≤
      (7 : ℝ) ^ p + 2 * p * exponentialMomentTail p (heightScale x n) := by
  have hh := bennett_tail_le_exponentialMomentTail hp (heightScale_pos hn hx)
  exact (activeHeight_moment_le_split_seven x n hx hn hp).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * p)))

theorem activeHeight_moment_le_dilated_tail (x : SignSequence) (n : ℕ)
    (hx : PositiveThrough x n) (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p) :
    (∫ k, |activeHeightError x n k| ^ p ∂Forward.uniformActiveHeightLaw x n) ≤
      (7 : ℝ) ^ p + 2 * p * (heightScale x n) ^ (-p) *
        ∫ u in Ioi (7 * heightScale x n), Real.exp (-u) * u ^ (p - 1) := by
  simpa only [exponentialMomentTail_dilation p (heightScale_pos hn hx), mul_assoc] using
    activeHeight_moment_le_exponentialTail x n hx hn hp

theorem activeHeight_moment_le_source_tail_asymptotic (x : SignSequence) (n : ℕ)
    (hx : PositiveThrough x n) (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p)
    (hlarge : 2 * (p - 1) / 7 ≤ heightScale x n) :
    (∫ k, |activeHeightError x n k| ^ p ∂Forward.uniformActiveHeightLaw x n) ≤
      (7 : ℝ) ^ p + 4 * p * (7 : ℝ) ^ (p - 1) *
        Real.exp (-7 * heightScale x n) / heightScale x n := by
  have hh := exponentialMomentTail_le hp (heightScale_pos hn hx) hlarge
  have hb := (activeHeight_moment_le_exponentialTail x n hx hn hp).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * p)))
  convert hb using 1
  ring

theorem activeHeight_moment_le_split_seven_uniform (x : SignSequence) (n : ℕ)
    (hx : PositiveThrough x n) (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p) :
    (∫ k, |activeHeightError x n k| ^ p ∂Forward.uniformActiveHeightLaw x n) ≤
      (7 : ℝ) ^ p + 2 * p * ∫ u in Ioi (7 : ℝ), bennettMomentDensity p (1 / 2) u := by
  have hm : (1 : ℝ) / 2 ≤ heightScale x n := by
    have hh := UniformBirth.truncatedMean_ge_half x n hx hn hn
    simpa only [UniformBirth.truncatedMean_eq_heightScale x n hx le_rfl] using hh
  have ht : (∫ u in Ioi (7 : ℝ), bennettMomentDensity p (heightScale x n) u) ≤
      ∫ u in Ioi (7 : ℝ), bennettMomentDensity p (1 / 2) u := by
    apply integral_mono_ae
      (IntegrableOn.mono_set (integrable_bennettMomentDensity (by linarith) (heightScale_pos hn hx))
        (show Ioi (7 : ℝ) ⊆ Ioi 0 by intro u hu; exact lt_trans (by norm_num) hu))
      (IntegrableOn.mono_set
        (integrable_bennettMomentDensity (by linarith : 0 < p) (by norm_num : (0 : ℝ) < 1 / 2))
        (show Ioi (7 : ℝ) ⊆ Ioi 0 by intro u hu; exact lt_trans (by norm_num) hu))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact bennettMomentDensity_antitone_mean
      (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 7) hu)) hm p
  exact (activeHeight_moment_le_split_seven x n hx hn hp).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * p)))

theorem activeHeight_exponentialTail_isBigO (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (p : ℝ) (hp : 1 ≤ p) :
    (fun n => exponentialMomentTail p (heightScale (rows n) n)) =O[atTop]
      (fun n => Real.exp (-7 * heightScale (rows n) n) / heightScale (rows n) n) :=
  (exponentialMomentTail_isBigO p hp).comp_tendsto (tendsto_heightScale_atTop rows hrows)

theorem activeHeightError_eLpNorm_le_source_integral (x : SignSequence) (n : ℕ)
    (hx : PositiveThrough x n) (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (activeHeightError x n) (ENNReal.ofReal p) (Forward.uniformActiveHeightLaw x n) ≤
      ENNReal.ofReal ((7 : ℝ) ^ p + 2 * p *
        ∫ u in Ioi (7 : ℝ), bennettMomentDensity p (1 / 2) u) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
    ENNReal.ofReal_ne_top (measurable_of_countable _).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  apply ENNReal.rpow_le_rpow ?_ (by positivity)
  calc
    _ = ENNReal.ofReal (∫ k, |activeHeightError x n k| ^ p
        ∂Forward.uniformActiveHeightLaw x n) := by
      simp_rw [Real.enorm_eq_ofReal_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
      exact (ofReal_integral_eq_lintegral_ofReal
        (Forward.uniformActiveHeightLaw_integrable x n _)
        (Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (activeHeight_moment_le_split_seven_uniform x n hx hn hp)

/-- The source's all-finite-real-Lp conclusion, now using the proved
split-at-seven moment bound rather than the alternate generic MGF bound. -/
theorem uniformActiveHeight_tendsto_Lp_via_tail_integral (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm (activeHeightError (rows n) n) (ENNReal.ofReal p)
      (Forward.uniformActiveHeightLaw (rows n) n)) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_of_tail_and_higher_moment (fun _ => measurable_of_countable _)
    hp (by linarith : p < p + 1)
    (C := ENNReal.ofReal ((7 : ℝ) ^ (p + 1) + 2 * (p + 1) *
      ∫ u in Ioi (7 : ℝ), bennettMomentDensity (p + 1) (1 / 2) u) ^ (1 / (p + 1))) (by finiteness)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact activeHeightError_eLpNorm_le_source_integral (rows n) n (hrows n) hn (by linarith)
  · intro e he
    apply (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
    simpa only [Real.norm_eq_abs, activeHeightError, Measure.real] using
      uniformActiveHeight_closed_deviation_tendsto rows hrows he

end Freezing1
