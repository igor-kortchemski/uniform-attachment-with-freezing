module

public import Freezing1.UniformPermutationMoments
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Averaging a proved symmetry over uniform permutations

An invariant probability law can be averaged over a finite family of its
measure-preserving relabelings. The proof is a finite sum of actual integrals;
there is no conditional-distribution or independence assumption.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped ENNReal BigOperators Classical

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

theorem integral_permutation_action_indicator
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (act : Equiv.Perm ι → Ω → Ω) (hact : ∀ σ, Measurable (act σ))
    (hlaw : ∀ σ, μ.map (act σ) = μ) {E : Set Ω} (hE : MeasurableSet E) :
    (∫ ω, (uniformPermutationLaw ι).real {σ | act σ ω ∈ E} ∂μ) = μ.real E := by
  have hi : ∀ σ, Integrable (fun ω => E.indicator (fun _ => (1 : ℝ)) (act σ ω)) μ := by
    intro σ
    apply Integrable.of_bound ((measurable_const.indicator hE).comp (hact σ)).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro ω
    by_cases h : act σ ω ∈ E <;> simp [h]
  have hv : ∀ σ, (∫ ω, E.indicator (fun _ => (1 : ℝ)) (act σ ω) ∂μ) = μ.real E := by
    intro σ
    have h := integral_map (μ := μ) (f := E.indicator (fun _ : Ω => (1 : ℝ)))
      (hact σ).aemeasurable
      (measurable_const.indicator hE).aestronglyMeasurable
    rw [hlaw σ, integral_indicator_const (1 : ℝ) hE] at h
    simpa only [smul_eq_mul, mul_one] using h.symm
  have hinner : ∀ ω, (uniformPermutationLaw ι).real {σ | act σ ω ∈ E} =
      (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ *
        ∑ σ, E.indicator (fun _ => (1 : ℝ)) (act σ ω) := by
    intro ω
    rw [← integral_uniformPermutation]
    have hset : MeasurableSet {σ | act σ ω ∈ E} := measurable_from_top hE
    have h := integral_indicator_one (μ := uniformPermutationLaw ι) hset
    simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using h.symm
  simp_rw [hinner]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun σ _ => hi σ)]
  simp only [hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Equiv.Perm ι)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- A pointwise finite matching estimate bounds the event under any proved
invariant law. An almost-everywhere bound is enough for supported state spaces. -/
theorem measureReal_le_of_permutation_average
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (act : Equiv.Perm ι → Ω → Ω) (hact : ∀ σ, Measurable (act σ))
    (hlaw : ∀ σ, μ.map (act σ) = μ) {E : Set Ω} (hE : MeasurableSet E)
    {B : ℝ} (hB : ∀ᵐ ω ∂μ,
      (uniformPermutationLaw ι).real {σ | act σ ω ∈ E} ≤ B) :
    μ.real E ≤ B := by
  rw [← integral_permutation_action_indicator μ act hact hlaw hE]
  have hmeas : Measurable (fun ω => (uniformPermutationLaw ι).real {σ | act σ ω ∈ E}) := by
    have heq : (fun ω => (uniformPermutationLaw ι).real {σ | act σ ω ∈ E}) =
        fun ω => (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ *
          ∑ σ, E.indicator (fun _ => (1 : ℝ)) (act σ ω) := by
      funext ω
      rw [← integral_uniformPermutation]
      have h := integral_indicator_one (μ := uniformPermutationLaw ι)
        (show MeasurableSet {σ | act σ ω ∈ E} from measurable_from_top hE)
      simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using h.symm
    rw [heq]
    fun_prop
  have hi : Integrable (fun ω => (uniformPermutationLaw ι).real {σ | act σ ω ∈ E}) μ := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  simpa using integral_mono_ae hi (integrable_const B) hB

end Freezing1
