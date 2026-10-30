module

public import Freezing1.UniformBirthBernoulliParameters
public import Freezing1.HeightScaleBounds
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.MeasureTheory.Integral.Prod

/-! Conditional means and the corrected strict post-birth tail. -/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators ProbabilityTheory

set_option backward.isDefEq.respectTransparency false

theorem condExp_prod_fst_nat {β : Type*} [MeasurableSpace β]
    (μ : Measure ℕ) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : ℕ × β → ℝ) (hf : Integrable f (μ.prod ν)) :
    (μ.prod ν)[f | (inferInstance : MeasurableSpace ℕ).comap Prod.fst] =ᵐ[μ.prod ν]
      fun z => ∫ Y, f (z.1, Y) ∂ν := by
  have hm : (inferInstance : MeasurableSpace ℕ).comap (Prod.fst : ℕ × β → ℕ) ≤
      (inferInstance : MeasurableSpace (ℕ × β)) :=
    (measurable_fst : Measurable (fun z : ℕ × β => z.1)).comap_le
  have hg : Integrable (fun z : ℕ × β => ∫ Y, f (z.1, Y) ∂ν) (μ.prod ν) :=
    hf.integral_prod_left.comp_fst ν
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm hf
    (fun _ _ _ => hg.integrableOn) ?_ ?_).symm
  · rintro s ⟨t, ht, rfl⟩ _
    have he : Prod.fst ⁻¹' t = t ×ˢ (univ : Set β) := by ext z; simp
    rw [he, setIntegral_prod _ hg.integrableOn, setIntegral_prod _ hf.integrableOn]
    simp only [integral_const, Measure.restrict_univ, probReal_univ, one_smul]
  · have hB : @Measurable (ℕ × β) ℕ
        ((inferInstance : MeasurableSpace ℕ).comap Prod.fst) inferInstance Prod.fst :=
      measurable_iff_comap_le.mpr le_rfl
    exact ((measurable_of_countable (fun b : ℕ => ∫ Y, f (b, Y) ∂ν)).comp hB).stronglyMeasurable.aestronglyMeasurable

theorem maskedCoordinate_integrable (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (i : Fin n) :
    Integrable (fun Y => (maskedCoordinate x i Y : ℝ))
      (bernoulliProductLaw (reciprocalParameter x n h)) := by
  exact (maskedCoordinate_hasLaw x n h i).integrable_fun_comp
    (integrable_bernoulliMeasure (1 : ℕ) 0 _ (fun z : ℕ => (z : ℝ)))

theorem integral_maskedCoordinate (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (i : Fin n) :
    (∫ Y, (maskedCoordinate x i Y : ℝ) ∂bernoulliProductLaw (reciprocalParameter x n h)) =
      (Reverse.attachmentParameter x n (horizon_le_extinction h) i : ℝ) := by
  have hh := (maskedCoordinate_hasLaw x n h i).integral_comp
    (f := fun z : ℕ => (z : ℝ)) ((measurable_of_countable _).aestronglyMeasurable)
  simpa only [Function.comp_def, integral_bernoulliMeasure, Nat.cast_one, Nat.cast_zero,
    smul_eq_mul, mul_one, mul_zero, add_zero] using hh

theorem truncatedSum_integrable (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (b : ℕ) :
    Integrable (fun Y => (truncatedSum x b Y : ℝ))
      (bernoulliProductLaw (reciprocalParameter x n h)) := by
  unfold truncatedSum
  simp only [Nat.cast_sum]
  exact integrable_finsetSum _ (fun i _ => maskedCoordinate_integrable x n h i)

theorem integral_truncatedSum (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (b : ℕ) :
    (∫ Y, (truncatedSum x b Y : ℝ) ∂bernoulliProductLaw (reciprocalParameter x n h)) =
      truncatedMean x n h b := by
  unfold truncatedSum truncatedMean
  simp only [Nat.cast_sum]
  rw [integral_finsetSum _ (fun i _ => maskedCoordinate_integrable x n h i)]
  exact Finset.sum_congr rfl (fun i _ => integral_maskedCoordinate x n h i)

/-- The correct source tail excludes the already counted birth step. -/
theorem heightScale_sub_truncatedMean (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    {b : ℕ} (hb : b ≤ n) :
    heightScale x n - truncatedMean x n h b = heightScaleOn x (Finset.Ioc b n) := by
  rw [truncatedMean_eq_heightScale x n h hb]
  have hh := heightScale_add_heightScaleOn_Ioc (x := x) hb
  linarith

/-- S21: the printed equality with the birth term included is false even
for one all-attachment step and birth time one. -/
theorem printed_inclusive_birth_tail_false :
    let x : SignSequence := fun _ => true
    heightScale x 1 - heightScale x 1 ≠ heightScaleOn x (Finset.Icc 1 1) := by
  norm_num [heightScaleOn, heightScale, activeCount_succ]

end Freezing1.UniformBirth
