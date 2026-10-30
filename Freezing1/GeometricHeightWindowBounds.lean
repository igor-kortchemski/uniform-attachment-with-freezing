module

public import Freezing1.GeometricHeightBlockBounds

/-! Normalize the actual finite geometric estimates on a log-ratio window.
The explicit constants tend to the manuscript constants as `A → ∞` and
the near-origin error tends to zero. -/

@[expose] public section

namespace Freezing1.GeometricHeight

theorem normalize_geometric_bounds {H L U P y d l : ℝ}
    (hd : 0 < d) (hdy : d ≤ y) (_hl : 0 < l) (hL : 0 ≤ L) (hP : 0 ≤ P)
    (hlo : (y / l - 2) * L ≤ H) (hhi : H ≤ (y / l) * U + P) :
    L / l - 2 * L / d ≤ H / y ∧ H / y ≤ U / l + P / d := by
  have hy := hd.trans_le hdy
  have hLm := mul_le_mul_of_nonneg_left hdy (div_nonneg (by positivity : 0 ≤ 2 * L) hd.le)
  have hPm := mul_le_mul_of_nonneg_left hdy (div_nonneg hP hd.le)
  rw [div_mul_cancel₀ _ hd.ne'] at hLm hPm
  constructor
  · apply (le_div_iff₀ hy).mpr
    have he : (L / l - 2 * L / d) * y = (y / l - 2) * L +
        (2 * L - (2 * L / d) * y) := by ring
    rw [he]
    linarith
  · apply (div_le_iff₀ hy).mpr
    have he : (U / l + P / d) * y = (y / l) * U + (P / d) * y := by ring
    rw [he]
    linarith

theorem heightInterval_geometric_bounds {x : SignSequence} {a b : ℕ}
    {β C A c η : ℝ} (hβ : 1 < β) (hβC : β < C) (hA : 1 ≤ A) (hAa : A ≤ a)
    (haC : (a : ℝ) * C < b) (hc : 0 < c) (hη : 0 ≤ η) (hηc : η < c)
    (hL : 0 ≤ lowerBlock c β η A)
    (herr : ∀ i ∈ Finset.Icc a b, |(activeCount x i : ℝ) / i - c| ≤ η) :
    lowerBlock c β η A / Real.log β - 2 * lowerBlock c β η A / Real.log C ≤
        heightInterval x a b / Real.log ((b : ℝ) / a) ∧
    heightInterval x a b / Real.log ((b : ℝ) / a) ≤
      upperBlock c β η A / Real.log β +
        (2 * (β - 1) + 1 / A) / (c - η) / Real.log C := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one (hA.trans hAa)
  have hC : 1 < C := hβ.trans hβC
  have hlC : 0 < Real.log C := Real.log_pos hC
  have hlog : Real.log C ≤ Real.log ((b : ℝ) / a) := by
    apply Real.log_le_log (lt_trans zero_lt_one hC)
    exact ((lt_div_iff₀ ha0).mpr (by simpa only [mul_comm] using haC)).le
  have hP : 0 ≤ (2 * (β - 1) + 1 / A) / (c - η) := by
    exact div_nonneg (add_nonneg (mul_nonneg (by norm_num) (sub_pos.mpr hβ).le)
      (one_div_pos.mpr (by linarith : 0 < A)).le) (sub_pos.mpr hηc).le
  obtain ⟨hlo, hhi⟩ := heightInterval_geometric_unnormalized hβ hβC hA hAa haC hc hη hηc hL herr
  exact normalize_geometric_bounds hlC hlog (Real.log_pos hβ) hL hP hlo hhi

theorem lowerBlock_source_endpoint {β A c η : ℝ} (hc : 0 < c)
    (hη : 0 ≤ η) (_hηc : η < c) (hL : 0 ≤ lowerBlock c β η A) :
    2 * lowerBlock c β η A ≤
      (c + 1) / c * (1 - 1 / β - 2 / (β * A)) := by
  have hd : 0 < c + η := by linarith
  have he : lowerBlock c β η A * (c + η) =
      (c + 1) / 2 * (1 - 1 / β - 2 / (β * A)) - η := by
    exact div_mul_cancel₀ _ hd.ne'
  rw [show (c + 1) / c * (1 - 1 / β - 2 / (β * A)) =
    ((c + 1) * (1 - 1 / β - 2 / (β * A))) / c by ring]
  apply (le_div_iff₀ hc).mpr
  have hm := mul_nonneg hL hη
  nlinarith

end Freezing1.GeometricHeight
