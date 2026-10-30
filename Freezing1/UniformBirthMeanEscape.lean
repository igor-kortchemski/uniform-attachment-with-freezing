module

public import Freezing1.UniformBirthMeanLimit
public import Freezing1.BennettMomentIntegral

/-! Escape of the genuine random mean and the source's Bennett integral. -/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem randomMean_bounded_probability_tendsto (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows) (L : ℝ) :
    Tendsto (fun n => auxiliaryLaw (rows n) n (hrows n)
      {z | randomMean (rows n) n (hrows n) z ≤ L}) atTop (nhds 0) := by
  have hh := randomMean_normalized_probability rows hrows hbulk (by norm_num : (0 : ℝ) < 1 / 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (tendsto_heightScale_atTop rows hrows).eventually (eventually_gt_atTop (2 * L))] with n hn hscale
  apply measure_mono
  intro z hz
  have hpos := heightScale_pos hn (hrows n)
  have hratio : randomMean (rows n) n (hrows n) z / heightScale (rows n) n < 1 / 2 := by
    apply (div_lt_iff₀ hpos).mpr
    change randomMean (rows n) n (hrows n) z ≤ L at hz
    linarith
  change 1 / 2 ≤ |meanNormalizationError (rows n) n (hrows n) z|
  unfold meanNormalizationError
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem lintegral_le_small_add_bound_bad {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) (C : ℝ≥0∞)
    (hbound : ∀ᵐ a ∂μ, f a ≤ C) (B : Set α) (hB : MeasurableSet B) (e : ℝ≥0∞)
    (hgood : ∀ a ∉ B, f a ≤ e) : ∫⁻ a, f a ∂μ ≤ e + C * μ B := by
  calc
    _ = (∫⁻ a in Bᶜ, f a ∂μ) + ∫⁻ a in B, f a ∂μ := by
      simpa only [compl_compl] using (lintegral_add_compl f hB.compl).symm
    _ ≤ e * μ Bᶜ + C * μ B := by
      apply add_le_add
      · exact (setLIntegral_mono' hB.compl hgood).trans_eq (setLIntegral_const _ _)
      · exact (setLIntegral_mono_ae' hB (hbound.mono (fun _ ha _ => ha))).trans_eq
          (setLIntegral_const _ _)
    _ ≤ _ := add_le_add (mul_le_of_le_one_right' prob_le_one) (le_refl _)

/-- Source 1440: the actual expected Bennett tail integral tends to zero.
The initial zero-mean row is kept extended-valued; only positive rows use
the uniform lower mean proved from the original birth law. -/
theorem expected_bennettMomentIntegral_tendsto (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => ∫⁻ z, bennettMomentIntegral q (randomMean (rows n) n (hrows n) z)
      ∂auxiliaryLaw (rows n) n (hrows n)) atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro e he
  obtain ⟨eta, heta, hsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (2 : ℝ≥0∞)) (b := e) (by norm_num) he.ne'
  let C : ℝ≥0∞ := bennettMomentIntegral q (1 / 2)
  have hC : C ≠ ∞ := bennettMomentIntegral_ne_top hq (by norm_num)
  obtain ⟨k, hk⟩ := ((ENNReal.tendsto_nhds_zero.mp
    (bennettMomentIntegral_add_nat_tendsto hq (by norm_num : (0 : ℝ) < 1 / 2)))
      (eta : ℝ≥0∞) (by exact_mod_cast heta)).exists
  let L : ℝ := 1 / 2 + k
  let B : (n : ℕ) → Set (ℕ × (Fin n → ℕ)) := fun n =>
    {z | randomMean (rows n) n (hrows n) z ≤ L}
  have hbad := randomMean_bounded_probability_tendsto rows hrows hbulk L
  have hweighted : Tendsto (fun n => C * auxiliaryLaw (rows n) n (hrows n) (B n)) atTop (nhds 0) := by
    have hh := (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC (by norm_num : (0 : ℝ) < 1)).comp hbad
    simpa only [ENNReal.rpow_one, Function.comp_def, B] using hh
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (ENNReal.tendsto_nhds_zero.mp hweighted) (eta : ℝ≥0∞) (by exact_mod_cast heta)] with n hn hbn
  have hbound : ∀ᵐ z ∂auxiliaryLaw (rows n) n (hrows n),
      bennettMomentIntegral q (randomMean (rows n) n (hrows n) z) ≤ C := by
    filter_upwards [randomMean_ge_half (rows n) n (hrows n) hn] with z hz
    exact bennettMomentIntegral_antitone_mean hz q
  have htotal := lintegral_le_small_add_bound_bad (auxiliaryLaw (rows n) n (hrows n))
    (fun z => bennettMomentIntegral q (randomMean (rows n) n (hrows n) z)) C hbound
    (B n) (Set.to_countable _).measurableSet (eta : ℝ≥0∞) (fun z hz => by
      have hL : L ≤ randomMean (rows n) n (hrows n) z := (lt_of_not_ge hz).le
      exact (bennettMomentIntegral_antitone_mean hL q).trans hk)
  calc
    _ ≤ (eta : ℝ≥0∞) + C * auxiliaryLaw (rows n) n (hrows n) (B n) := htotal
    _ ≤ (eta : ℝ≥0∞) + eta := add_le_add (le_refl _) hbn
    _ = (eta : ℝ≥0∞) * 2 := by ring
    _ ≤ e := hsmall.le

end Freezing1.UniformBirth
