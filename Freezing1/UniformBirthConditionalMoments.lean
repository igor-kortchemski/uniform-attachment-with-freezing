module

public import Freezing1.UniformBirthRelativeMomentLaw

/-! Actual conditional moment and tail functions given the birth coordinate. -/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem relativeMoment_integrable (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun z : ℕ × (Fin n → ℕ) => |fixedRelativeError x n h z.1 z.2| ^ q)
      (auxiliaryLaw x n h) := by
  have := birthLaw_probability x n h
  by_cases hn : n = 0
  · subst n
    simpa only [fixedRelativeError, truncatedSum, truncatedMean, Finset.univ_eq_empty,
      Finset.filter_empty, Finset.sum_empty, Nat.cast_zero, zero_div, zero_sub, abs_neg,
      abs_one, Real.one_rpow] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℕ × (Fin 0 → ℕ) => (1 : ℝ))
        (auxiliaryLaw x 0 h))
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  apply (integrable_prod_iff (measurable_of_countable _).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall (fun b => fixedRelativeError_rpow_integrable x n h b hq)
  · apply (integrable_const (relativeMomentBound q)).mono'
      (measurable_of_countable _).aestronglyMeasurable
    have hbirth : ∀ᵐ b ∂birthLaw x n, 1 ≤ b := by
      rw [birthLaw, ae_map_iff (measurable_of_countable _).aemeasurable (by measurability)]
      filter_upwards [uniformVertex_supported x n] with v hv
      exact birthTime_pos_of_mem h hn1 hv
    filter_upwards [hbirth] with b hb
    have hnneg : 0 ≤ ∫ Y, ‖|fixedRelativeError x n h b Y| ^ q‖
        ∂bernoulliProductLaw (reciprocalParameter x n h) := integral_nonneg (fun _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnneg]
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact fixedRelativeError_moment_le x n h hn1 hb hq

/-- The fixed-birth moment is the genuine conditional expectation, not
an additional conditional-distribution hypothesis. -/
theorem relativeMoment_condExp (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    {q : ℝ} (hq : 0 ≤ q) :
    (auxiliaryLaw x n h)[(fun z : ℕ × (Fin n → ℕ) => |fixedRelativeError x n h z.1 z.2| ^ q) |
      (inferInstance : MeasurableSpace ℕ).comap Prod.fst] =ᵐ[auxiliaryLaw x n h]
      (fun z => ∫ Y, |fixedRelativeError x n h z.1 Y| ^ q
        ∂bernoulliProductLaw (reciprocalParameter x n h)) := by
  have := birthLaw_probability x n h
  exact condExp_prod_fst_nat (birthLaw x n) (bernoulliProductLaw (reciprocalParameter x n h))
    _ (relativeMoment_integrable x n h hq)

/-- Source 1432 interpreted as conditional expectation under the actual
independent birth/array law. -/
theorem relativeMoment_condExp_layercake (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) {q : ℝ} (hq : 0 < q) :
    (auxiliaryLaw x n h)[(fun z : ℕ × (Fin n → ℕ) => |fixedRelativeError x n h z.1 z.2| ^ q) |
      (inferInstance : MeasurableSpace ℕ).comap Prod.fst] =ᵐ[auxiliaryLaw x n h]
      (fun z => (ENNReal.ofReal q * ∫⁻ u in Ioi (0 : ℝ),
        bernoulliProductLaw (reciprocalParameter x n h)
          {Y | u ≤ |fixedRelativeError x n h z.1 Y|} * ENNReal.ofReal (u ^ (q - 1))).toReal) := by
  filter_upwards [relativeMoment_condExp x n h hq.le] with z hz
  rw [hz, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun Y => Real.rpow_nonneg (abs_nonneg _) _))
    (measurable_of_countable _).aestronglyMeasurable, fixedRelativeError_layercake x n h z.1 hq]

theorem relativeTail_condExp (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (u : ℝ) :
    (auxiliaryLaw x n h)[(fun z : ℕ × (Fin n → ℕ) =>
      if u ≤ |fixedRelativeError x n h z.1 z.2| then (1 : ℝ) else 0) |
      (inferInstance : MeasurableSpace ℕ).comap Prod.fst] =ᵐ[auxiliaryLaw x n h]
      (fun z => (bernoulliProductLaw (reciprocalParameter x n h)).real
        {Y | u ≤ |fixedRelativeError x n h z.1 Y|}) := by
  have := birthLaw_probability x n h
  have hi : Integrable (fun z : ℕ × (Fin n → ℕ) =>
      if u ≤ |fixedRelativeError x n h z.1 z.2| then (1 : ℝ) else 0) (auxiliaryLaw x n h) := by
    apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    exact Eventually.of_forall (fun z => by split <;> norm_num)
  filter_upwards [condExp_prod_fst_nat (birthLaw x n)
    (bernoulliProductLaw (reciprocalParameter x n h)) _ hi] with z hz
  change ((birthLaw x n).prod (bernoulliProductLaw (reciprocalParameter x n h)))[(fun z : ℕ × (Fin n → ℕ) =>
    if u ≤ |fixedRelativeError x n h z.1 z.2| then (1 : ℝ) else 0) |
    (inferInstance : MeasurableSpace ℕ).comap Prod.fst] z = _
  rw [hz]
  exact integral_indicator_one (Set.to_countable _).measurableSet

/-- Source 1436 for the actual conditional tail, with the positive mean
and n≥1 established from the genuine birth law. -/
theorem relativeTail_condExp_bennett (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    ∀ᵐ z ∂auxiliaryLaw x n h,
      (auxiliaryLaw x n h)[(fun z : ℕ × (Fin n → ℕ) =>
        if u ≤ |fixedRelativeError x n h z.1 z.2| then (1 : ℝ) else 0) |
        (inferInstance : MeasurableSpace ℕ).comap Prod.fst] z ≤
        2 * Real.exp (-randomMean x n h z * bennettRate u) := by
  filter_upwards [relativeTail_condExp x n h u, randomMean_ge_half x n h hn] with z hz hm
  rw [hz]
  exact fixedRelativeError_closed_tail x n h z.1 (by change 0 < randomMean x n h z; linarith) hu

end Freezing1.UniformBirth
