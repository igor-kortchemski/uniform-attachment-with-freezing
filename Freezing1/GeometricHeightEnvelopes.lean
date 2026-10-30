module

public import Freezing1.GeometricHeightBlockBounds

/-! Scalar envelopes for the corrected geometric proof. The auxiliary
variable `t` controls both the near-origin ratio error and `1 / A`.
All limiting values are proved from the actual rational formulas. -/

@[expose] public section

namespace Freezing1.GeometricHeight

open Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

noncomputable def upperValue (c β t : ℝ) : ℝ :=
  (((c + 1) / 2) * (β - 1 + t) + β * t) / (c - t)

noncomputable def lowerValue (c β t : ℝ) : ℝ :=
  (((c + 1) / 2) * (1 - 1 / β - 2 * t / β) - t) / (c + t)

noncomputable def upperEnvelope (c C β t : ℝ) : ℝ :=
  upperValue c β t / Real.log β +
    (2 * (β - 1) + t) / (c - t) / Real.log C

noncomputable def lowerEnvelope (c C β t : ℝ) : ℝ :=
  lowerValue c β t / Real.log β -
    (c + 1) / c * (1 - 1 / β) / Real.log C

theorem block_comparison {c β η A : ℝ} (hc : 0 < c) (hβ : 1 < β)
    (hη : 0 ≤ η) (hηc : η < c) (_hA : 0 < A) (hcut : 1 / A ≤ η) :
    lowerValue c β η ≤ lowerBlock c β η A ∧
    upperBlock c β η A ≤ upperValue c β η := by
  have hdL : 0 < c + η := by linarith
  have hdU := sub_pos.mpr hηc
  have hβ0 : 0 < β := by linarith
  constructor
  · apply (div_le_div_iff_of_pos_right hdL).mpr
    have hinv : 2 / (β * A) ≤ 2 * η / β := by
      have h := mul_le_mul_of_nonneg_left hcut (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hβ0.le)
      convert h using 1 <;> ring
    nlinarith
  · apply (div_le_div_iff_of_pos_right hdU).mpr
    nlinarith

/-- A diagonal tolerance also controls the literal row-dependent error
parameter in the manuscript, when that error is at most the tolerance. -/
theorem block_comparison_mixed {c β η t A : ℝ} (hc : 0 < c) (hβ : 1 < β)
    (hη : 0 ≤ η) (hηt : η ≤ t) (htc : t < c) (_hA : 0 < A)
    (hcut : 1 / A ≤ t) (hV : 0 ≤ lowerValue c β t) :
    lowerValue c β t ≤ lowerBlock c β η A ∧
    upperBlock c β η A ≤ upperValue c β t := by
  have ht : 0 ≤ t := hη.trans hηt
  have hβ0 : 0 < β := by linarith
  have hK : 0 < (c + 1) / 2 := by positivity
  have hdL : 0 < c + η := by linarith
  have hdU : 0 < c - η := by linarith
  have hdV : 0 < c + t := by linarith
  have hdW : 0 < c - t := sub_pos.mpr htc
  have hinv : 2 / (β * A) ≤ 2 * t / β := by
    have h := mul_le_mul_of_nonneg_left hcut (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hβ0.le)
    convert h using 1 <;> ring
  have heL : lowerValue c β t * (c + t) =
      (c + 1) / 2 * (1 - 1 / β - 2 * t / β) - t := div_mul_cancel₀ _ hdV.ne'
  have heU : upperValue c β t * (c - t) =
      (c + 1) / 2 * (β - 1 + t) + β * t := div_mul_cancel₀ _ hdW.ne'
  have hU0 : 0 ≤ upperValue c β t := by
    exact div_nonneg
      (add_nonneg (mul_nonneg hK.le (add_nonneg (sub_pos.mpr hβ).le ht))
        (mul_nonneg hβ0.le ht)) hdW.le
  constructor
  · apply (le_div_iff₀ hdL).mpr
    nlinarith [mul_nonneg hV (sub_nonneg.mpr hηt)]
  · apply (div_le_iff₀ hdU).mpr
    nlinarith [mul_nonneg hU0 (sub_nonneg.mpr hηt)]

theorem upperEnvelope_zero (c C β : ℝ) :
    upperEnvelope c C β 0 =
      (c + 1) / (2 * c) * ((β - 1) / Real.log β) +
        2 * (β - 1) / (c * Real.log C) := by
  simp only [upperEnvelope, upperValue, add_zero, sub_zero, mul_zero]
  ring

theorem lowerEnvelope_zero (c C β : ℝ) :
    lowerEnvelope c C β 0 =
      (c + 1) / (2 * c) * ((1 - 1 / β) / Real.log β) -
        2 * ((c + 1) / (2 * c)) * (1 - 1 / β) / Real.log C := by
  simp only [lowerEnvelope, lowerValue, add_zero, sub_zero, mul_zero, zero_div]
  ring

theorem beta_log_ratios {β : ℝ} (hβ : 1 < β) :
    (β - 1) / Real.log β ≤ β ∧
    1 / β ≤ (1 - 1 / β) / Real.log β ∧
    0 ≤ 1 - 1 / β ∧ 1 - 1 / β ≤ β - 1 := by
  have hβ0 : 0 < β := by linarith
  have hl := Real.log_pos hβ
  have hloglo := Real.one_sub_inv_le_log_of_pos hβ0
  have hloghi := Real.log_le_sub_one_of_pos hβ0
  have he : β * (1 - 1 / β) = β - 1 := by field_simp
  have hi : 0 < 1 / β := one_div_pos.mpr hβ0
  have hip : 1 / β ≤ 1 := (div_le_one hβ0).mpr hβ.le
  have h1 := mul_le_mul_of_nonneg_left hloglo hβ0.le
  have h2 := mul_le_mul_of_nonneg_left hloghi hi.le
  have he' : (1 / β) * (β - 1) = 1 - 1 / β := by field_simp
  have hd : 1 - 1 / β ≤ β - 1 := by
    have hm := mul_le_mul_of_nonneg_right hip (sub_pos.mpr hβ).le
    rw [he'] at hm
    simpa only [one_mul] using hm
  have heInv : β * (1 - β⁻¹) = β - 1 := by simpa only [one_div] using he
  rw [heInv] at h1
  exact ⟨(div_le_iff₀ hl).mpr h1,
    (le_div_iff₀ hl).mpr (by simpa only [he'] using h2), by linarith, hd⟩

theorem zero_envelope_bounds {c C β : ℝ} (hc : 0 < c) (hC : 1 < C) (hβ : 1 < β) :
    (c + 1) / (2 * c) -
        (((c + 1) / (2 * c)) * (1 + 2 / Real.log C)) * (β - 1) ≤
      lowerEnvelope c C β 0 ∧
    upperEnvelope c C β 0 ≤ (c + 1) / (2 * c) +
      ((c + 1) / (2 * c) + 2 / (c * Real.log C)) * (β - 1) := by
  let K := (c + 1) / (2 * c)
  have hK : 0 < K := by dsimp [K]; positivity
  have hlC := Real.log_pos hC
  obtain ⟨hU, hL, hd0, hd⟩ := beta_log_ratios hβ
  have hLU := mul_le_mul_of_nonneg_left hL hK.le
  have hU' := mul_le_mul_of_nonneg_left hU hK.le
  have htail := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ K * (1 + 2 / Real.log C) by positivity)
  have he : K * (1 / β) - 2 * K * (1 - 1 / β) / Real.log C =
      K - (K * (1 + 2 / Real.log C)) * (1 - 1 / β) := by ring
  rw [lowerEnvelope_zero, upperEnvelope_zero]
  change K - _ ≤ K * ((1 - 1 / β) / Real.log β) - _ ∧
    K * ((β - 1) / Real.log β) + _ ≤ K + _
  constructor
  · have hm : K * (1 / β) - 2 * K * (1 - 1 / β) / Real.log C ≤
        K * ((1 - 1 / β) / Real.log β) - 2 * K * (1 - 1 / β) / Real.log C :=
      sub_le_sub_right hLU _
    rw [he] at hm
    linarith
  · calc
      _ ≤ K * β + 2 * (β - 1) / (c * Real.log C) := add_le_add hU' le_rfl
      _ = _ := by dsimp only [K]; ring

theorem exists_beta_zero_envelopes {c C δ : ℝ} (hc : 0 < c) (hC : 1 < C) (hδ : 0 < δ) :
    ∃ β : ℝ, 1 < β ∧ β < C ∧
      (c + 1) / (2 * c) - δ < lowerEnvelope c C β 0 ∧
      upperEnvelope c C β 0 < (c + 1) / (2 * c) + δ := by
  let K := (c + 1) / (2 * c)
  let D := K * (1 + 2 / Real.log C) + K + 2 / (c * Real.log C) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hlC := Real.log_pos hC
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨β, hβ, hβmax⟩ := exists_between (show (1 : ℝ) < min C (1 + δ / D) by
    exact lt_min hC (by have hp := div_pos hδ hD; linarith))
  have hβC := hβmax.trans_le (min_le_left _ _)
  have hsmall : (β - 1) * D < δ := by
    have hh := hβmax.trans_le (min_le_right _ _)
    exact (lt_div_iff₀ hD).mp (by linarith : β - 1 < δ / D)
  have hβm := sub_pos.mpr hβ
  obtain ⟨hlo, hhi⟩ := zero_envelope_bounds hc hC hβ
  have hp : 0 < 2 / (c * Real.log C) := by positivity
  have hkl : 0 < K * (1 + 2 / Real.log C) := by positivity
  have hDlo : K * (1 + 2 / Real.log C) ≤ D := by dsimp [D]; linarith
  have hDhi : K + 2 / (c * Real.log C) ≤ D := by dsimp [D]; linarith
  have hlo' := mul_le_mul_of_nonneg_right hDlo hβm.le
  have hhi' := mul_le_mul_of_nonneg_right hDhi hβm.le
  refine ⟨β, hβ, hβC, ?_, ?_⟩ <;> dsimp only [K] at * <;> nlinarith

theorem continuousAt_values_zero {c C β : ℝ} (hc : 0 < c) :
    ContinuousAt (lowerValue c β) 0 ∧
    ContinuousAt (lowerEnvelope c C β) 0 ∧
    ContinuousAt (upperEnvelope c C β) 0 := by
  have hcp : c + (0 : ℝ) ≠ 0 := by simpa using hc.ne'
  have hcm : c - (0 : ℝ) ≠ 0 := by simpa using hc.ne'
  unfold lowerEnvelope upperEnvelope
  unfold lowerValue upperValue
  constructor
  · fun_prop
  constructor <;> fun_prop

theorem exists_diagonal_tolerance {c C β δ : ℝ} (hc : 0 < c) (hβ : 1 < β)
    (hlo : (c + 1) / (2 * c) - δ < lowerEnvelope c C β 0)
    (hhi : upperEnvelope c C β 0 < (c + 1) / (2 * c) + δ) :
    ∃ η : ℝ, 0 < η ∧ η < c ∧ 0 < lowerValue c β η ∧
      (c + 1) / (2 * c) - δ ≤ lowerEnvelope c C β η ∧
      upperEnvelope c C β η ≤ (c + 1) / (2 * c) + δ := by
  have hβ0 : 0 < β := by linarith
  have hi : 1 / β < 1 := (div_lt_one hβ0).mpr hβ
  have hLv : 0 < lowerValue c β 0 := by
    dsimp [lowerValue]
    simp only [mul_zero, zero_div, sub_zero, add_zero]
    exact div_pos (mul_pos (by positivity) (by linarith)) hc
  obtain ⟨hcontV, hcontL, hcontU⟩ := continuousAt_values_zero (C := C) (β := β) hc
  have hev := hcontV.tendsto.eventually (lt_mem_nhds hLv)
  have hel := hcontL.tendsto.eventually (lt_mem_nhds hlo)
  have heu := hcontU.tendsto.eventually (gt_mem_nhds hhi)
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < c ∧ 0 < lowerValue c β t ∧
      (c + 1) / (2 * c) - δ ≤ lowerEnvelope c C β t ∧
      upperEnvelope c C β t ≤ (c + 1) / (2 * c) + δ := by
    filter_upwards [Ioo_mem_nhdsGT hc, hev.filter_mono nhdsWithin_le_nhds,
      hel.filter_mono nhdsWithin_le_nhds, heu.filter_mono nhdsWithin_le_nhds]
      with t ht hv hl hu
    exact ⟨ht.1, ht.2, hv, hl.le, hu.le⟩
  exact he.exists

end Freezing1.GeometricHeight
