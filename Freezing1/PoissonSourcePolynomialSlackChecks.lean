module

public import Freezing1.RateFunction
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The source's claim of positive rate slack for every margin in `(0,1)`
fails when the threshold crosses below the mean. This check is independent
of the valid small-margin Poisson polynomial estimate. -/

@[expose] public section

namespace Freezing1

set_option backward.isDefEq.respectTransparency false

theorem printed_all_margin_rate_slack_counterexample :
    ∃ c : LinearRegimeParameter, linearHeightFactor c = 5 / 4 ∧
      (0 : ℝ) < 3 / 4 ∧ (3 / 4 : ℝ) < 1 ∧
      1 - (((c : ℝ) + 1) / (2 * (c : ℝ))) *
        bennettRate (linearHeightFactor c - 1 - 3 / 4) < 0 := by
  let G : ℝ := bennettRate (1 / 4)
  have hG0 : 0 < G := bennettRate_pos (by norm_num)
  have hlog : Real.log (5 / 4 : ℝ) ≤ 1 / 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
    norm_num at h
    exact h
  have hGdef : G = (5 / 4 : ℝ) * Real.log (5 / 4 : ℝ) - 1 / 4 := by
    dsimp [G, bennettRate]
    norm_num
  have hG1 : G ≤ 1 / 16 := by rw [hGdef]; linarith
  have hd : 0 < 2 - G := by linarith
  let c : LinearRegimeParameter := ⟨G / (2 - G), div_pos hG0 hd,
    (div_le_one hd).mpr (by linarith)⟩
  have hc : (c : ℝ) = G / (2 - G) := rfl
  have hcp := c.property.1
  have hceq : ((c : ℝ) - 1) / ((c : ℝ) + 1) = G - 1 := by
    rw [hc]
    field_simp
    ring
  have hF : linearHeightFactor c = 5 / 4 := by
    symm
    apply linearHeightFactor_unique c (by norm_num)
    rw [hceq, hGdef]
    ring
  have hK : 0 < ((c : ℝ) + 1) / (2 * (c : ℝ)) := by positivity
  have hnorm : (((c : ℝ) + 1) / (2 * (c : ℝ))) * G = 1 := by
    have hg : G = bennettRate (linearHeightFactor c - 1) := by
      rw [hF]
      norm_num [G]
    rw [hg, bennettRate_linearHeightFactor]
    field_simp
  have hneg : (1 / 8 : ℝ) < bennettRate (-(1 / 2)) := by
    have hh : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    norm_num [bennettRate, hh]
    linarith [Real.log_two_lt_d9]
  have hcompare : G < bennettRate (-(1 / 2)) := by linarith
  have hmul := mul_lt_mul_of_pos_left hcompare hK
  rw [hnorm] at hmul
  refine ⟨c, hF, by norm_num, by norm_num, ?_⟩
  rw [hF]
  norm_num only [show (5 / 4 : ℝ) - 1 - 3 / 4 = -(1 / 2) by norm_num]
  linarith

end Freezing1
