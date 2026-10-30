module

public import Freezing1.UniformBirthRandomMean
public import Freezing1.UniformBirthTail
public import Freezing1.ForwardUniformHeight
public import Freezing1.LinearRegimeCutoffs
public import Freezing1.LinearRegimeAssumptions
public import Freezing1.BernoulliArrayLimits

/-!
# Random conditional-mean normalization

A uniform birth misses only a negligible fraction of the height scale.
The positive bulk bound controls the late deterministic tail; the exact
uniform-birth law makes the remaining early-birth probability arbitrarily
small. Boundedness then gives every real `Lp` normalization.
-/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem truncatedMean_mono (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    {a b : ℕ} (hab : a ≤ b) : truncatedMean x n h a ≤ truncatedMean x n h b := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact (Finset.mem_filter.mp hi).2.trans_le hab
  · exact fun _ _ _ => unitInterval.nonneg _

theorem bulk_late_scale_over_full_tendsto (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    Tendsto (fun n : ℕ => heightScaleOn (rows n) (Finset.Ioc ⌊e * (n : ℝ)⌋₊ n) /
      heightScale (rows n) n) atTop (nhds 0) := by
  obtain ⟨d, hd, hlate⟩ := hbulk e he he1
  have hupper := (tendsto_const_nhds (x := 1 / d)).div_atTop (tendsto_heightScale_atTop rows hrows)
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop (1 : ℕ), hlate] with n hn hln
    have hs : Finset.Ioc ⌊e * (n : ℝ)⌋₊ n ⊆ Finset.Ioc 0 n := by
      intro i hi
      have hh := Finset.mem_Ioc.mp hi
      exact Finset.mem_Ioc.mpr ⟨by omega, hh.2⟩
    have hnon := (heightScaleOn_le_card_half (hrows n) hs).1
    exact div_nonneg hnon (heightScale_pos hn (hrows n)).le
  · filter_upwards [eventually_ge_atTop (1 : ℕ), hlate] with n hn hln
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hs : Finset.Ioc ⌊e * (n : ℝ)⌋₊ n ⊆ Finset.Ioc 0 n := by
      intro i hi
      have hh := Finset.mem_Ioc.mp hi
      exact Finset.mem_Ioc.mpr ⟨by omega, hh.2⟩
    have hbound := (heightScaleOn_le_inv_delta hn hd hs (fun i hi _ => by
      have hi' := Finset.mem_Ioc.mp hi
      have htime : e * (n : ℝ) < i :=
        (Nat.floor_lt (mul_nonneg he.le hnR.le)).mp hi'.1
      exact (le_div_iff₀ hnR).mp (hln i htime.le hi'.2))).2
    exact div_le_div_of_nonneg_right hbound (heightScale_pos hn (hrows n)).le

noncomputable def meanNormalizationError (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (z : ℕ × (Fin n → ℕ)) : ℝ := randomMean x n h z / heightScale x n - 1

theorem meanNormalizationError_abs_le_one (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (hn : 1 ≤ n) (z : ℕ × (Fin n → ℕ)) : |meanNormalizationError x n h z| ≤ 1 := by
  have hm := randomMean_bounds x n h z
  have hh := heightScale_pos hn h
  have hlo := div_nonneg hm.1 hh.le
  have hhi := (div_le_one hh).mpr hm.2
  unfold meanNormalizationError
  rw [abs_le]
  constructor <;> linarith

theorem meanNormalizationError_bad_subset (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (hn : 1 ≤ n) {a : ℕ} (ha : a ≤ n) {eps : ℝ}
    (htail : heightScaleOn x (Finset.Ioc a n) / heightScale x n < eps) :
    {z : ℕ × (Fin n → ℕ) | eps ≤ |meanNormalizationError x n h z|} ⊆ {z | z.1 < a} := by
  intro z hz
  change eps ≤ |meanNormalizationError x n h z| at hz
  by_contra hnot
  have haz : a ≤ z.1 := Nat.le_of_not_gt hnot
  have hmlo : heightScale x a ≤ randomMean x n h z := by
    rw [← truncatedMean_eq_heightScale x n h ha]
    exact truncatedMean_mono x n h haz
  have hmhi := (randomMean_bounds x n h z).2
  have hh := heightScale_pos hn h
  have htailid := heightScale_add_heightScaleOn_Ioc (x := x) ha
  have hnorm : |meanNormalizationError x n h z| =
      (heightScale x n - randomMean x n h z) / heightScale x n := by
    unfold meanNormalizationError
    rw [abs_of_nonpos (by apply sub_nonpos.mpr; exact (div_le_one hh).mpr hmhi)]
    field_simp
    ring
  rw [hnorm] at hz
  have hbound : (heightScale x n - randomMean x n h z) / heightScale x n ≤
      heightScaleOn x (Finset.Ioc a n) / heightScale x n :=
    div_le_div_of_nonneg_right (by linarith) hh.le
  exact (not_lt_of_ge (hz.trans hbound)) htail

theorem randomMean_normalized_real_probability (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (auxiliaryLaw (rows n) n (hrows n)).real
      {z | eps ≤ |meanNormalizationError (rows n) n (hrows n) z|}) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro a ha
    let e : ℝ := min (a / 2) (1 / 2)
    have he : 0 < e := lt_min (by positivity) (by norm_num)
    have he1 : e < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hea : e < a := (min_le_left _ _).trans_lt (by linarith)
    have htail := bulk_late_scale_over_full_tendsto rows hrows hbulk he he1
    have hratio := tendsto_floor_mul_div_nat he.le
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      htail.eventually (eventually_lt_nhds heps), hratio.eventually (eventually_lt_nhds hea)]
        with n hn htn hrn
    have han : ⌊e * (n : ℝ)⌋₊ ≤ n := floor_mul_le_self he1.le n
    have hbound := measureReal_mono (μ := auxiliaryLaw (rows n) n (hrows n))
      (meanNormalizationError_bad_subset (rows n) n (hrows n) hn han htn) (measure_ne_top _ _)
    have hbirth := (auxiliary_birth_hasLaw (rows n) n (hrows n)).measureReal_eq
      (p := fun b : ℕ => b < ⌊e * (n : ℝ)⌋₊) (by measurability)
    exact (hbound.trans (hbirth.trans_le (birthLaw_lt_le_div (rows n) n (hrows n) hn han))).trans_lt hrn

theorem randomMean_normalized_probability (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => auxiliaryLaw (rows n) n (hrows n)
      {z | eps ≤ |meanNormalizationError (rows n) n (hrows n) z|}) atTop (nhds 0) :=
  (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
    (randomMean_normalized_real_probability rows hrows hbulk heps)

theorem randomMean_normalized_tendsto_Lp (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm (meanNormalizationError (rows n) n (hrows n))
      (ENNReal.ofReal p) (auxiliaryLaw (rows n) n (hrows n))) atTop (nhds 0) := by
  apply tendsto_eLpNorm_of_tail_and_higher_moment (fun n => measurable_of_countable _)
    hp (show p < p + 1 by linarith) (C := 1) (by norm_num)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hh := eLpNorm_le_of_ae_bound
      (μ := auxiliaryLaw (rows n) n (hrows n))
      (f := meanNormalizationError (rows n) n (hrows n)) (C := (1 : ℝ))
      (p := ENNReal.ofReal (p + 1)) (measurable_of_countable _).aestronglyMeasurable
      (Eventually.of_forall (fun z => by
        simpa only [Real.norm_eq_abs] using meanNormalizationError_abs_le_one (rows n) n (hrows n) hn z))
    simpa only [measure_univ, ENNReal.one_rpow, ENNReal.ofReal_one, one_mul] using hh
  · intro e he
    simpa only [Real.norm_eq_abs] using randomMean_normalized_probability rows hrows hbulk he

end Freezing1.UniformBirth
