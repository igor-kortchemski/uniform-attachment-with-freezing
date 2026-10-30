module

public import Freezing1.LinearRegimeAssumptions
public import Freezing1.IidScheduleExtinction

/-!
# Uniform tail ratios imply the two source linear assumptions

The deterministic statement isolates precisely the stronger hypothesis in
the Introduction. A second result transfers one path's ratio limit to any
family of whole schedules eventually equal to that path.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory ProbabilityTheory
open scoped Classical Topology ENNReal

set_option backward.isDefEq.respectTransparency false

def UniformTailRatio (rows : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ η > 0, ∀ᶠ n in atTop, ∀ i : ℕ, A n ≤ (i : ℝ) → i ≤ n →
    |(activeCount (rows n) i : ℝ) / i - c| ≤ η

theorem UniformTailRatio.nearOrigin {rows : ℕ → SignSequence} {A : ℕ → ℝ} {c : ℝ}
    (h : UniformTailRatio rows A c) : NearOriginLinear rows A c := by
  intro η hη
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [h η hη] with n hn i hAi hi
  apply hn i hAi
  have hh : (i : ℝ) ≤ n := hi.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  exact_mod_cast hh

theorem UniformTailRatio.bulk {rows : ℕ → SignSequence} {A : ℕ → ℝ} {c : ℝ}
    (h : UniformTailRatio rows A c) (hc : 0 < c)
    (hA : Tendsto (fun n : ℕ => A n / n) atTop (𝓝 0)) : BulkLowerBound rows := by
  intro ε hε _
  refine ⟨c * ε / 2, by positivity, ?_⟩
  filter_upwards [h (c / 2) (half_pos hc), hA.eventually (gt_mem_nhds hε),
    eventually_ge_atTop 1] with n hn hAn hn1
  intro i hi hin
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hiR : (0 : ℝ) < i := (mul_pos hε hnp).trans_le hi
  have hcut : A n ≤ (i : ℝ) :=
    ((div_lt_iff₀ hnp).mp hAn).le.trans hi
  have hlow := (abs_le.mp (hn i hcut hin)).1
  have hratio : c / 2 ≤ (activeCount (rows n) i : ℝ) / i := by linarith only [hlow]
  have hcount := (le_div_iff₀ hiR).mp hratio
  have hscale := mul_le_mul_of_nonneg_left hi (half_pos hc).le
  apply (le_div_iff₀ hnp).mpr
  nlinarith only [hcount, hscale]

/-- The stronger uniform-ratio condition implies exactly both nested source
assumptions. Survival is the original standing row assumption. -/
theorem UniformTailRatio.sourceAssumptions {rows : ℕ → SignSequence} {A : ℕ → ℝ} {c : ℝ}
    (h : UniformTailRatio rows A c) (hc : 0 < c) (hc1 : c ≤ 1)
    (hApos : ∀ n, 0 < A n)
    (hAlog : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hs : ∀ n, PositiveThrough (rows n) n) :
    NearOriginLimsup rows A c ∧ BulkLiminf rows := by
  exact ⟨(nearOriginLimsup_iff rows A hApos hc.le hc1 hs).mpr h.nearOrigin,
    (bulkLiminf_iff rows hs).mpr (h.bulk hc (cutoff_div_nat_tendsto_zero A hAlog))⟩

/-- One true pathwise ratio limit supplies uniform ratios over any diverging
cutoff for rows eventually equal to that entire path. -/
theorem uniformTailRatio_of_eventually_eq_path {rows : ℕ → SignSequence}
    {x : SignSequence} {A : ℕ → ℝ} {c : ℝ}
    (hrows : ∀ᶠ n in atTop, rows n = x)
    (hx : Tendsto (fun i : ℕ => (activeCount x i : ℝ) / i) atTop (𝓝 c))
    (hA : Tendsto A atTop atTop) : UniformTailRatio rows A c := by
  intro η hη
  have he := (Metric.tendsto_nhds.mp hx) η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  filter_upwards [hrows, hA.eventually_ge_atTop (N : ℝ)] with n hn hAn i hAi _
  rw [hn]
  have hi : N ≤ i := by exact_mod_cast hAn.trans hAi
  simpa only [Real.dist_eq] using (hN i hi).le

end Freezing1
