module

public import Freezing1.ConditionalInvariantAverage

/-! Identifying and bounding actual conditional expectations by finite
averages under observation-preserving transformations. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Classical BigOperators

variable {Ω B I : Type*} [mΩ : MeasurableSpace Ω] [mB : MeasurableSpace B]
  {μ : Measure Ω} [IsFiniteMeasure μ] {φ : Ω → B}

omit [IsFiniteMeasure μ] in
theorem integrable_finite_action_average (s : Finset I) (T : I → Ω → Ω)
    (hT : ∀ i ∈ s, MeasurePreserving (T i) μ μ) {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable (fun ω => (s.card : ℝ)⁻¹ * ∑ i ∈ s, f (T i ω)) μ := by
  exact (integrable_finsetSum s (fun i hi => (hT i hi).integrable_comp_of_integrable hf)).const_mul _

theorem condExp_eq_of_finite_invariant_average (hφ : Measurable φ)
    (s : Finset I) (hs : s.Nonempty) (T : I → Ω → Ω)
    (hT : ∀ i ∈ s, MeasurePreserving (T i) μ μ)
    (hobs : ∀ i ∈ s, (fun ω => φ (T i ω)) =ᵐ[μ] φ)
    {f : Ω → ℝ} (hf : Integrable f μ) (g : B → ℝ) (hg : Measurable g)
    (havg : (fun ω => (s.card : ℝ)⁻¹ * ∑ i ∈ s, f (T i ω)) =ᵐ[μ]
      fun ω => g (φ ω)) :
    μ[f | mB.comap φ] =ᵐ[μ] fun ω => g (φ ω) := by
  have hi := (integrable_finite_action_average s T hT hf).congr havg
  have hφc : @Measurable Ω B (mB.comap φ) mB φ := measurable_iff_comap_le.mpr le_rfl
  have hsm : StronglyMeasurable[mB.comap φ] (fun ω => g (φ ω)) :=
    (hg.comp hφc).stronglyMeasurable
  have hfix := condExp_of_stronglyMeasurable hφ.comap_le hsm hi
  calc
    _ =ᵐ[μ] μ[(fun ω => (s.card : ℝ)⁻¹ * ∑ i ∈ s, f (T i ω)) | mB.comap φ] :=
      (condExp_finite_invariant_average hφ s hs T hT hobs hf).symm
    _ =ᵐ[μ] μ[(fun ω => g (φ ω)) | mB.comap φ] := condExp_congr_ae havg
    _ =ᵐ[μ] _ := Eventually.of_forall (congrFun hfix)

theorem condExp_le_of_finite_invariant_average (hφ : Measurable φ)
    (s : Finset I) (hs : s.Nonempty) (T : I → Ω → Ω)
    (hT : ∀ i ∈ s, MeasurePreserving (T i) μ μ)
    (hobs : ∀ i ∈ s, (fun ω => φ (T i ω)) =ᵐ[μ] φ)
    {f : Ω → ℝ} (hf : Integrable f μ) (g : B → ℝ) (hg : Measurable g)
    (hgi : Integrable (fun ω => g (φ ω)) μ)
    (havg : (fun ω => (s.card : ℝ)⁻¹ * ∑ i ∈ s, f (T i ω)) ≤ᵐ[μ]
      fun ω => g (φ ω)) :
    μ[f | mB.comap φ] ≤ᵐ[μ] fun ω => g (φ ω) := by
  have hφc : @Measurable Ω B (mB.comap φ) mB φ := measurable_iff_comap_le.mpr le_rfl
  have hsm : StronglyMeasurable[mB.comap φ] (fun ω => g (φ ω)) :=
    (hg.comp hφc).stronglyMeasurable
  have hfix := condExp_of_stronglyMeasurable hφ.comap_le hsm hgi
  have hce := condExp_finite_invariant_average hφ s hs T hT hobs hf
  have hmono := condExp_mono (m := mB.comap φ)
    (integrable_finite_action_average s T hT hf) hgi havg
  filter_upwards [hce, hmono] with ω hω hle
  rw [hω, hfix] at hle
  exact hle

end Freezing1
