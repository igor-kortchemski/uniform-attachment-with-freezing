module

public import Freezing1.GeometricHeightEnvelopes
public import Freezing1.GeometricHeightWindowBounds
public import Freezing1.LinearRegimeUniform

/-!
# Lemma 8 through the repaired geometric-block argument

The finite estimates below are supplied by the genuine integer geometric
partition and actual attachment counts. Only the existing definitions of
the source maximum and the generic quantified-to-nested-limit conversion
are reused from `LinearRegimeUniform`; its Abel estimate is not used.
-/

@[expose] public section

namespace Freezing1.GeometricHeight

open Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

theorem heightInterval_diagonal_envelopes {x : SignSequence} {a b : ℕ}
    {β C A c η : ℝ} (hβ : 1 < β) (hβC : β < C) (hA : 1 ≤ A) (hAa : A ≤ a)
    (haC : (a : ℝ) * C < b) (hc : 0 < c) (hη : 0 ≤ η) (hηc : η < c)
    (hcut : 1 / A ≤ η) (hV : 0 < lowerValue c β η)
    (herr : ∀ i ∈ Finset.Icc a b, |(activeCount x i : ℝ) / i - c| ≤ η) :
    lowerEnvelope c C β η ≤ heightInterval x a b / Real.log ((b : ℝ) / a) ∧
    heightInterval x a b / Real.log ((b : ℝ) / a) ≤ upperEnvelope c C β η := by
  have hA0 : 0 < A := by linarith
  have hβ0 : 0 < β := by linarith
  have hlβ := Real.log_pos hβ
  have hlC := Real.log_pos (hβ.trans hβC)
  obtain ⟨hcompL, hcompU⟩ := block_comparison hc hβ hη hηc hA0 hcut
  have hL : 0 ≤ lowerBlock c β η A := hV.le.trans hcompL
  obtain ⟨hlo, hhi⟩ := heightInterval_geometric_bounds hβ hβC hA hAa haC hc hη hηc hL herr
  have hLdiv := div_le_div_of_nonneg_right hcompL hlβ.le
  have hUdiv := div_le_div_of_nonneg_right hcompU hlβ.le
  have hP : (2 * (β - 1) + 1 / A) / (c - η) / Real.log C ≤
      (2 * (β - 1) + η) / (c - η) / Real.log C :=
    div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (by linarith) (sub_pos.mpr hηc).le) hlC.le
  have hEnd : 2 * lowerBlock c β η A ≤ (c + 1) / c * (1 - 1 / β) := by
    have hraw := lowerBlock_source_endpoint hc hη hηc hL
    have hd : 0 ≤ 2 / (β * A) := by positivity
    have hm : 0 ≤ (c + 1) / c := by positivity
    nlinarith
  have hEnddiv := div_le_div_of_nonneg_right hEnd hlC.le
  dsimp only [lowerEnvelope, upperEnvelope]
  constructor <;> linarith

/-- For every fixed geometric ratio, the printed row-dependent lower
constant is eventually positive at a sufficiently small outer cutoff.
The error is the actual source finite maximum `η_n(ε)`. -/
theorem eventually_source_lowerBlock_positive {x : ℕ → SignSequence}
    {A : ℕ → ℝ} {c β : ℝ} (hnear : NearOriginLinear x A c)
    (hA : Tendsto A atTop atTop) (hc : 0 < c) (hβ : 1 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      0 ≤ nearOriginMaximum x A c ε n ∧ nearOriginMaximum x A c ε n < c ∧
      0 < lowerBlock c β (nearOriginMaximum x A c ε n) (A n) := by
  have hβ0 : 0 < β := by linarith
  have hi : 1 / β < 1 := (div_lt_one hβ0).mpr hβ
  have hV0 : 0 < lowerValue c β 0 := by
    dsimp [lowerValue]
    simp only [mul_zero, zero_div, sub_zero, add_zero]
    exact div_pos (mul_pos (by positivity) (by linarith)) hc
  have hv := (continuousAt_values_zero (C := β + 1) (β := β) hc).1.tendsto.eventually
    (lt_mem_nhds hV0)
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < c ∧ 0 < lowerValue c β t := by
    filter_upwards [Ioo_mem_nhdsGT hc, hv.filter_mono nhdsWithin_le_nhds] with t ht hV
    exact ⟨ht.1, ht.2, hV⟩
  obtain ⟨t, ht, htc, hV⟩ := he.exists
  obtain ⟨ε, hε0, hε1, hε⟩ := hnear t ht
  refine ⟨ε, hε0, hε1, ?_⟩
  filter_upwards [hε, hA.eventually_ge_atTop (max 1 (1 / t))] with n hn hAn
  have hA0 : 0 < A n := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hAn)
  have hcut : 1 / A n ≤ t := by
    have hh : 1 / t ≤ A n := (le_max_right _ _).trans hAn
    have hm := (div_le_iff₀ ht).mp hh
    exact (div_le_iff₀ hA0).mpr (by nlinarith)
  have hη0 := nearOriginMaximum_nonneg x A c ε n
  have hηt := (nearOriginMaximum_le_iff hε1.le ht.le).mpr hn
  have hcmp := (block_comparison_mixed hc hβ hη0 hηt htc hA0 hcut hV.le).1
  exact ⟨hη0, hηt.trans_lt htc, hV.trans_le hcmp⟩

/-- The source quantified uniform conclusion, proved by geometric blocks.
No interval estimate or geometric partition is an additional premise. -/
theorem uniformLogIntervals_of_nearOriginLinear_geometric {x : ℕ → SignSequence}
    {A : ℕ → ℝ} {c C : ℝ} (hnear : NearOriginLinear x A c)
    (hA : Tendsto A atTop atTop) (hc : 0 < c) (hC : 1 < C) :
    UniformLogIntervals x A c C := by
  intro δ hδ
  obtain ⟨β, hβ, hβC, hbL, hbU⟩ := exists_beta_zero_envelopes hc hC hδ
  obtain ⟨η, hη, hηc, hV, henvL, henvU⟩ := exists_diagonal_tolerance hc hβ hbL hbU
  obtain ⟨ε, hε0, hε1, hε⟩ := hnear η hη
  refine ⟨ε, hε0, hε1, ?_⟩
  filter_upwards [hε, hA.eventually_ge_atTop (max 1 (1 / η))] with n hn hAn
  intro a b hAa _hab hbε haC
  have hA1 : 1 ≤ A n := (le_max_left _ _).trans hAn
  have hA0 : 0 < A n := by linarith
  have hcut : 1 / A n ≤ η := by
    have hh : 1 / η ≤ A n := (le_max_right _ _).trans hAn
    have hm := (div_le_iff₀ hη).mp hh
    exact (div_le_iff₀ hA0).mpr (by nlinarith)
  have herr : ∀ i ∈ Finset.Icc a b, |(activeCount (x n) i : ℝ) / i - c| ≤ η := by
    intro i hi
    obtain ⟨hai, hib⟩ := Finset.mem_Icc.mp hi
    exact hn i (hAa.trans (by exact_mod_cast hai))
      ((by exact_mod_cast hib : (i : ℝ) ≤ b).trans hbε)
  obtain ⟨hlo, hhi⟩ := heightInterval_diagonal_envelopes hβ hβC hA1 hAa haC hc
    hη.le hηc hcut hV herr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The same actual finite maximum and nested limit as existing L08, now
with the corrected geometric proof supplying the uniform estimate. -/
theorem logIntervalLimsup_of_nearOriginLinear_geometric {x : ℕ → SignSequence}
    {A : ℕ → ℝ} {c C : ℝ} (hnear : NearOriginLinear x A c)
    (hA : Tendsto A atTop atTop) (hc : 0 < c) (hC : 1 < C) :
    LogIntervalLimsup x A c C :=
  logIntervalLimsup_of_uniformLogIntervals
    (uniformLogIntervals_of_nearOriginLinear_geometric hnear hA hc hC)

/-- The literal source near-origin maximum hypothesis gives the original
L08 maximum/limsup/outer-limit statement by the geometric proof. -/
theorem logIntervalLimsup_of_nearOriginLimsup_geometric {x : ℕ → SignSequence}
    {A : ℕ → ℝ} {c C : ℝ} (hnear : NearOriginLimsup x A c)
    (hApos : ∀ n, 0 < A n) (hA : Tendsto A atTop atTop)
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 < C)
    (hsurv : ∀ n, PositiveThrough (x n) n) : LogIntervalLimsup x A c C :=
  logIntervalLimsup_of_nearOriginLinear_geometric
    ((nearOriginLimsup_iff x A hApos hc.le hc1 hsurv).mp hnear) hA hc hC

end Freezing1.GeometricHeight
