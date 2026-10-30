module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! Conditional expectations under finite observation-preserving randomization.
The observation need only be preserved almost surely, as for supported
reconstruction operators with a total default outside their support. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

variable {Ω B I : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
  {μ : Measure Ω} [IsFiniteMeasure μ] {φ : Ω → B}

omit [IsFiniteMeasure μ] in
theorem setIntegral_comp_of_preserving_observation (hφ : Measurable φ)
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hobs : (fun ω => φ (T ω)) =ᵐ[μ] φ) {f : Ω → ℝ} (hf : Integrable f μ)
    {s : Set Ω} (hs : MeasurableSet[MeasurableSpace.comap φ ‹MeasurableSpace B›] s) :
    ∫ ω in s, f (T ω) ∂μ = ∫ ω in s, f ω ∂μ := by
  have hs₀ : MeasurableSet s := hφ.comap_le _ hs
  have hmem : ∀ᵐ ω ∂μ, T ω ∈ s ↔ ω ∈ s := by
    obtain ⟨b, _, hb⟩ := MeasurableSpace.measurableSet_comap.mp hs
    rw [← hb]
    filter_upwards [hobs] with ω hω
    simp only [Set.mem_preimage, hω]
  have hind : (fun ω => (s.indicator f) (T ω)) =ᵐ[μ]
      s.indicator (fun ω => f (T ω)) := by
    filter_upwards [hmem] with ω hω
    simp only [Set.indicator_apply, hω]
  have hi := integral_map hT.measurable.aemeasurable
    (show AEStronglyMeasurable (s.indicator f) (μ.map T) by
      rw [hT.map_eq]
      exact (hf.indicator hs₀).aestronglyMeasurable)
  rw [hT.map_eq] at hi
  calc
    _ = ∫ ω, s.indicator (fun ω => f (T ω)) ω ∂μ := (integral_indicator hs₀).symm
    _ = ∫ ω, (s.indicator f) (T ω) ∂μ := integral_congr_ae hind.symm
    _ = ∫ ω, s.indicator f ω ∂μ := hi.symm
    _ = _ := integral_indicator hs₀

theorem condExp_comp_of_preserving_observation (hφ : Measurable φ)
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hobs : (fun ω => φ (T ω)) =ᵐ[μ] φ) {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[(fun ω => f (T ω)) | MeasurableSpace.comap φ ‹MeasurableSpace B›] =ᵐ[μ]
      μ[f | MeasurableSpace.comap φ ‹MeasurableSpace B›] := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq hφ.comap_le
    (hT.integrable_comp_of_integrable hf)
    (fun _ _ _ => integrable_condExp.integrableOn) ?_
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  intro s hs _
  rw [setIntegral_condExp hφ.comap_le hf hs]
  exact (setIntegral_comp_of_preserving_observation hφ hT hobs hf hs).symm

/-- Averaging finitely many genuine measure-preserving transformations
does not alter the expectation conditional on an almost-surely preserved
observation. No group law or invertibility premise is needed. -/
theorem condExp_finite_invariant_average (hφ : Measurable φ) (s : Finset I)
    (hs : s.Nonempty) (T : I → Ω → Ω)
    (hT : ∀ i ∈ s, MeasurePreserving (T i) μ μ)
    (hobs : ∀ i ∈ s, (fun ω => φ (T i ω)) =ᵐ[μ] φ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[(fun ω => (s.card : ℝ)⁻¹ * ∑ i ∈ s, f (T i ω)) |
      MeasurableSpace.comap φ ‹MeasurableSpace B›] =ᵐ[μ]
      μ[f | MeasurableSpace.comap φ ‹MeasurableSpace B›] := by
  have hsum := condExp_finsetSum
    (fun i hi => (hT i hi).integrable_comp_of_integrable hf)
    (MeasurableSpace.comap φ ‹MeasurableSpace B›)
  simp only [Function.comp_def] at hsum
  have heach : ∀ᵐ ω ∂μ, ∀ i ∈ s,
      μ[(fun ω => f (T i ω)) | MeasurableSpace.comap φ ‹MeasurableSpace B›] ω =
        μ[f | MeasurableSpace.comap φ ‹MeasurableSpace B›] ω :=
    (eventually_all_finset s).mpr (fun i hi =>
      condExp_comp_of_preserving_observation hφ (hT i hi) (hobs i hi) hf)
  have hsmul := condExp_smul (μ := μ) (s.card : ℝ)⁻¹ (∑ i ∈ s, fun ω => f (T i ω))
    (MeasurableSpace.comap φ ‹MeasurableSpace B›)
  have hfun : (fun ω => (s.card : ℝ)⁻¹ * ∑ i ∈ s, f (T i ω)) =
      (s.card : ℝ)⁻¹ • (∑ i ∈ s, fun ω => f (T i ω)) := by
    ext ω
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  filter_upwards [hsum, heach, hsmul] with ω hsumω heachω hsmulω
  rw [hfun, hsmulω]
  change (s.card : ℝ)⁻¹ * μ[(∑ i ∈ s, fun ω => f (T i ω)) |
    MeasurableSpace.comap φ ‹MeasurableSpace B›] ω = _
  rw [hsumω]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl heachω]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hs.card_pos.ne' : (s.card : ℝ) ≠ 0), one_mul]

end Freezing1
