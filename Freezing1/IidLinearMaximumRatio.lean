module

public import Freezing1.IidLinearAssumptions

/-! The stronger introductory hypothesis in its literal finite-maximum form. -/

@[expose] public section

namespace Freezing1

open Filter
open scoped Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem uniformTailRatio_iff_maximum_tendsto {rows : ℕ → SignSequence}
    {A : ℕ → ℝ} {c : ℝ} :
    UniformTailRatio rows A c ↔
      Tendsto (nearOriginMaximum rows A c 1) atTop (𝓝 0) := by
  constructor
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [h (η / 2) (half_pos hη)] with n hn
    have hb : nearOriginMaximum rows A c 1 n ≤ η / 2 := by
      apply (nearOriginMaximum_le_iff (by norm_num : (1 : ℝ) ≤ 1) (half_pos hη).le).mpr
      intro i hAi hi
      exact hn i hAi (by exact_mod_cast (show (i : ℝ) ≤ n by simpa only [one_mul] using hi))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (nearOriginMaximum_nonneg _ _ _ _ _)]
    linarith only [hb, hη]
  · intro h η hη
    have he := h.eventually (gt_mem_nhds hη)
    filter_upwards [he] with n hn i hAi hin
    have hb := (nearOriginMaximum_le_iff (by norm_num : (1 : ℝ) ≤ 1) hη.le).mp hn.le
    exact hb i hAi (by simpa only [one_mul] using (show (i : ℝ) ≤ n by exact_mod_cast hin))

/-- The exact stronger maximum hypothesis stated in the Introduction gives
both original nested-limit assumptions under the original standing inputs. -/
theorem sourceAssumptions_of_uniformMaximum {rows : ℕ → SignSequence} {A : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (nearOriginMaximum rows A c 1) atTop (𝓝 0))
    (hc : 0 < c) (hc1 : c ≤ 1) (hApos : ∀ n, 0 < A n)
    (hAlog : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hs : ∀ n, PositiveThrough (rows n) n) :
    NearOriginLimsup rows A c ∧ BulkLiminf rows :=
  (uniformTailRatio_iff_maximum_tendsto.mpr h).sourceAssumptions hc hc1 hApos hAlog hs

end Freezing1
