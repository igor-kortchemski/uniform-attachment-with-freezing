module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weak convergence of actual probability pushforwards and mixtures
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology

theorem tendsto_probability_map_of_ae_tendsto
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [TopologicalSpace Y] [BorelSpace Y]
    (μ : ProbabilityMeasure Ω) (F : ℕ → Ω → Y) (f : Ω → Y)
    (hF : ∀ n, Measurable (F n)) (hf : AEMeasurable f (μ : Measure Ω))
    (hc : ∀ᵐ ω ∂(μ : Measure Ω), Tendsto (fun n => F n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n => μ.map (F n)) atTop (𝓝 (μ.map f)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have ht := tendsto_integral_filter_of_norm_le_const (μ := (μ : Measure Ω))
    (F := fun n ω => g (F n ω)) (f := fun ω => g (f ω))
    (Eventually.of_forall fun n => (g.continuous.measurable.comp (hF n)).aestronglyMeasurable)
    ⟨‖g‖, Eventually.of_forall fun _ => Eventually.of_forall fun ω => g.norm_coe_le_norm _⟩
    (hc.mono fun ω hω => (g.continuous.tendsto _).comp hω)
  have hleft (n : ℕ) : (∫ y, g y ∂(μ.map (F n) : Measure Y)) =
      ∫ ω, g (F n ω) ∂(μ : Measure Ω) :=
    integral_map (hF n).aemeasurable g.continuous.measurable.aestronglyMeasurable
  have hright : (∫ y, g y ∂(μ.map f : Measure Y)) =
      ∫ ω, g (f ω) ∂(μ : Measure Ω) :=
    integral_map hf g.continuous.measurable.aestronglyMeasurable
  simpa only [hleft, hright] using ht

noncomputable def probabilityMix {Y : Type*} [MeasurableSpace Y]
    (p : unitInterval) (μ ν : ProbabilityMeasure Y) : ProbabilityMeasure Y :=
  ⟨unitInterval.toNNReal p • (μ : Measure Y) +
      unitInterval.toNNReal (unitInterval.symm p) • (ν : Measure Y), by
    constructor
    simp⟩

theorem tendsto_probabilityMix {Y : Type*} [MeasurableSpace Y]
    [TopologicalSpace Y] [OpensMeasurableSpace Y]
    (p : unitInterval) {μs νs : ℕ → ProbabilityMeasure Y} {μ ν : ProbabilityMeasure Y}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν)) :
    Tendsto (fun n => probabilityMix p (μs n) (νs n)) atTop (𝓝 (probabilityMix p μ ν)) := by
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds] at hμ hν ⊢
  change Tendsto (fun n => unitInterval.toNNReal p • (μs n).toFiniteMeasure +
    unitInterval.toNNReal (unitInterval.symm p) • (νs n).toFiniteMeasure) atTop
      (𝓝 (unitInterval.toNNReal p • μ.toFiniteMeasure +
        unitInterval.toNNReal (unitInterval.symm p) • ν.toFiniteMeasure))
  exact (hμ.const_smul _).add (hν.const_smul _)

end Freezing1
