module

public import Freezing1.CoalescenceLimits
public import Freezing1.HeightScaleBounds
public import Mathlib.Analysis.PSeries

/-!
# Coalescence is negligible even on the logarithmic scale

The source proves only the `n`-scale claim before invoking a logarithmic
distance limit. Here the two uniform walk assumptions give the stronger
coalescence estimate directly. The small cutoff is retained throughout.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology Classical

/-- Correct domain for the uniform linear lower bound: indices at or above
the diverging cutoff, not the first few schedule steps. -/
theorem eventually_linear_lower_above_cutoff (x : ℕ → SignSequence) (A : ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) (hA : Tendsto A atTop atTop)
    (hnear : NearOriginLinear x A c) (hbulk : BulkLowerBound x) :
    ∃ d > 0, ∀ᶠ n in atTop, ∀ i : ℕ,
      A n ≤ (i : ℝ) → i ≤ n → d * i ≤ (activeCount (x n) i : ℝ) := by
  obtain ⟨ε, hε0, hε1, hnear'⟩ := hnear (c / 2) (half_pos hc)
  obtain ⟨δ, hδ, hbulk'⟩ := hbulk ε hε0 hε1
  refine ⟨min (c / 2) δ, lt_min (half_pos hc) hδ, ?_⟩
  filter_upwards [hnear', hbulk', hA.eventually_gt_atTop 0] with n hnnear hnbulk hAn
  intro i hAi hin
  have hi0 : (0 : ℝ) < i := hAn.trans_le hAi
  have hinR : (i : ℝ) ≤ n := by exact_mod_cast hin
  have hn0 : (0 : ℝ) < n := hi0.trans_le hinR
  by_cases hiε : (i : ℝ) ≤ ε * n
  · have hratio : c / 2 ≤ (activeCount (x n) i : ℝ) / i := by
      have hh := (abs_le.mp (hnnear i hAi hiε)).1
      linarith
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hi0.le).trans
      ((le_div_iff₀ hi0).mp hratio)
  · calc
      min (c / 2) δ * i ≤ δ * i := mul_le_mul_of_nonneg_right (min_le_right _ _) hi0.le
      _ ≤ δ * n := mul_le_mul_of_nonneg_left hinR hδ.le
      _ ≤ _ := (le_div_iff₀ hn0).mp (hnbulk i (le_of_lt (lt_of_not_ge hiε)) hin)

namespace ReverseHistory

theorem sum_coalescenceHazard_le_inv_cutoff (x : SignSequence) (n a : ℕ)
    (ha : 0 < a) {d : ℝ} (hd : 0 < d) (hda : 2 ≤ d * a)
    (hwalk : ∀ j ∈ Finset.Ioc a n, d * j ≤ (activeCount x j : ℝ)) :
    ∑ t ∈ Finset.Ioc a n, Reverse.coalescenceHazard x t ≤ (4 / d ^ 2) / a := by
  by_cases han : a ≤ n
  · calc
      _ ≤ ∑ t ∈ Finset.Ioc a n, (4 / d ^ 2) * ((t : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum
        intro t ht
        have hat : (a : ℝ) ≤ t := by exact_mod_cast (Finset.mem_Ioc.mp ht).1.le
        have hdt : 2 ≤ d * t := hda.trans (mul_le_mul_of_nonneg_left hat hd.le)
        calc
          _ ≤ 2 / ((d * t) * (d * t - 1)) :=
            Reverse.coalescenceHazard_le_of_activeCount x t (by linarith) (hwalk t ht)
          _ ≤ 4 / (d * t) ^ 2 := two_div_mul_sub_one_le_four_div_sq hdt
          _ = _ := by simp only [mul_pow, div_eq_mul_inv, mul_inv]; ring
      _ = (4 / d ^ 2) * ∑ t ∈ Finset.Ioc a n, ((t : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (4 / d ^ 2) * ((a : ℝ)⁻¹ - (n : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (Nat.ne_of_gt ha) han) (by positivity)
      _ ≤ (4 / d ^ 2) * (a : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
      _ = _ := by simp only [div_eq_mul_inv]
  · have he : Finset.Ioc a n = ∅ := Finset.Ioc_eq_empty_of_le (Nat.le_of_lt (lt_of_not_ge han))
    rw [he, Finset.sum_empty]
    positivity

/-- With probability tending to one, two uniform labels have already
coalesced below the original diverging small cutoff. -/
theorem uniform_coalescence_above_cutoff_tendsto_zero
    (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (hτ : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n)) {c : ℝ} (hc : 0 < c)
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A c) (hbulk : BulkLowerBound x) :
    Tendsto (fun n : ℕ => (uniformCoalescenceLaw (x n) n).real
      {k : ℕ | Nat.ceil (A n) ≤ k}) atTop (𝓝 0) := by
  obtain ⟨d, hd, hwalk⟩ := eventually_linear_lower_above_cutoff x A hc hA hnear hbulk
  have haInf := tendsto_nat_ceil_atTop_of_tendsto hA
  have hnInf : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdaInf := haInf.const_mul_atTop hd
  have hbound : Tendsto (fun n : ℕ => 2 / (n : ℝ) + (4 / d ^ 2) / Nat.ceil (A n))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 2 / (n : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnInf
    have h2 : Tendsto (fun n : ℕ => (4 / d ^ 2) / (Nat.ceil (A n) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop haInf
    simpa only [add_zero] using h1.add h2
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) ?_ hbound
  filter_upwards [hwalk, hdaInf.eventually_ge_atTop 2, haInf.eventually_gt_atTop 0,
    eventually_ge_atTop 1] with n hwalkn hdan han hn
  have ha : 0 < Nat.ceil (A n) := by exact_mod_cast han
  calc
    _ ≤ 1 / ((vertexLabels (x n) n).card : ℝ) +
        ∑ t ∈ Finset.Ioc (Nat.ceil (A n)) n, Reverse.coalescenceHazard (x n) t :=
      uniformCoalescenceLaw_tail_le (x n) n (Nat.ceil (A n)) (hτ n)
    _ ≤ _ := by
      apply add_le_add (inverse_vertex_card_le_two_div_nat (by omega)
        (activeCount_nonneg_of_le_extinctionTime (hτ n)))
      apply sum_coalescenceHazard_le_inv_cutoff (x n) n (Nat.ceil (A n)) ha hd hdan
      intro j hj
      rcases Finset.mem_Ioc.mp hj with ⟨haj, hjn⟩
      apply hwalkn j _ hjn
      exact (Nat.le_ceil (A n)).trans (by exact_mod_cast haj.le)

/-- The stronger logarithmic estimate needed before a uniform-pair distance
argument. It does not follow merely from the source's `C/n → 0`. -/
theorem uniform_coalescence_div_log_tendsto_zero
    (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (hτ : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n)) {c : ℝ} (hc : 0 < c)
    (hA : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hnear : NearOriginLinear x A c) (hbulk : BulkLowerBound x) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (uniformCoalescenceLaw (x n) n).real
      {k : ℕ | ε < (k : ℝ) / Real.log (n : ℝ)}) atTop (𝓝 0) := by
  have hceil := tendsto_ceil_div_log_zero ((hA.eventually_gt_atTop 0).mono fun _ h => h.le) hsmall
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (uniform_coalescence_above_cutoff_tendsto_zero x A hτ hc hA hnear hbulk)
  filter_upwards [hceil.eventually_lt_const hε, hlog.eventually_gt_atTop 0] with n hcn hln
  let := uniformCoalescenceLaw_probability (x n) n (hτ n)
  have hsub : {k : ℕ | ε < (k : ℝ) / Real.log (n : ℝ)} ⊆
      {k : ℕ | Nat.ceil (A n) ≤ k} := by
    intro k hk
    have hcast : (Nat.ceil (A n) : ℝ) < k :=
      (div_lt_div_iff_of_pos_right hln).mp (hcn.trans hk)
    exact_mod_cast hcast.le
  exact measureReal_mono hsub

end ReverseHistory
end Freezing1
