module

public import Freezing1.SIRPhysicalLaws
public import Freezing1.MainSIRUniformSamplesFinite

/-!
# Finite-rate terminal uniform samples of the physical epidemic

The actual whole-contact protocol is followed to absorption, then vertices
are sampled conditionally uniformly from its complete genealogy. The scaled
height/distance laws converge to the source's geometric-survival mixtures.
Their identities with embedded sampling laws are proved from source data.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

section FixedPopulation

variable {Ω : Type*} [MeasurableSpace Ω]

theorem physical_sampleLaw_probability (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) (k : ℕ)
    {α : Type*} [MeasurableSpace α] (K : Kernel PlaneForward.State α) [IsMarkovKernel K] :
    IsProbabilityMeasure (((physicalTreePathLaw mu n X : Measure (ℕ → TreeState)).map
      (fun H => (H k).tree)).bind K) := by
  have hm : Measurable (fun H : ℕ → TreeState => (H k).tree) :=
    (measurable_of_countable TreeState.tree).comp (measurable_pi_apply k)
  have : IsProbabilityMeasure ((physicalTreePathLaw mu n X : Measure (ℕ → TreeState)).map
      (fun H => (H k).tree)) :=
    Measure.isProbabilityMeasure_map_iff hm.aemeasurable |>.mpr inferInstance
  exact isProbabilityMeasure_bind K.aemeasurable (Filter.Eventually.of_forall fun _ => inferInstance)

instance physicalUniformHeightLaw_probability (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) (k : ℕ) :
    IsProbabilityMeasure (physicalUniformHeightLaw mu n X k) :=
  physical_sampleLaw_probability mu n X k PlaneForward.vertexHeightKernel

instance physicalPairDataLaw_probability (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) (k : ℕ) :
    IsProbabilityMeasure (physicalPairDataLaw mu n X k) :=
  physical_sampleLaw_probability mu n X k PlaneForward.pairDataKernel

noncomputable def physicalTerminalUniformHeightScaledLaw
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (⟨physicalUniformHeightLaw mu n X (2 * n + 1), inferInstance⟩ : ProbabilityMeasure ℕ)
    (fun h : ℕ => (h : ℝ) / Real.log (n : ℝ))

noncomputable def physicalTerminalUniformDistanceScaledLaw
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (⟨physicalPairDataLaw mu n X (2 * n + 1), inferInstance⟩ : ProbabilityMeasure (ℕ × ℕ × ℕ))
    (fun z : ℕ × ℕ × ℕ => (z.2.2 : ℝ) / Real.log (n : ℝ))

variable {mu : Measure Ω} [IsProbabilityMeasure mu] {n : ℕ} {rate : ℝ≥0}
  {X : (c : ClockSlot n) → Ω → ClockDatum c}

theorem PoissonSIRData.terminalUniformHeightScaledLaw_eq
    (h : PoissonSIRData mu n rate X) (hr : 0 < rate) :
    physicalTerminalUniformHeightScaledLaw mu n X = terminalUniformHeightScaledLaw rate n := by
  apply Subtype.ext
  exact (congrArg (fun nu : Measure ℕ => nu.map
    (fun a : ℕ => (a : ℝ) / Real.log (n : ℝ))) (h.uniformHeightLaw_eq hr (2 * n + 1))).trans
      (terminalUniformHeightScaledLaw_eq_sample rate n).symm

theorem PoissonSIRData.terminalUniformDistanceScaledLaw_eq
    (h : PoissonSIRData mu n rate X) (hr : 0 < rate) :
    physicalTerminalUniformDistanceScaledLaw mu n X = terminalUniformDistanceScaledLaw rate n := by
  apply Subtype.ext
  exact (congrArg (fun nu : Measure (ℕ × ℕ × ℕ) => nu.map
    (fun z : ℕ × ℕ × ℕ => (z.2.2 : ℝ) / Real.log (n : ℝ))) (h.pairDataLaw_eq hr (2 * n + 1))).trans
      (terminalUniformDistanceScaledLaw_eq_sample rate n).symm

end FixedPopulation

section Limits

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (mu : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (mu n)]
  (X : (n : ℕ) → (c : ClockSlot n) → Ω n → ClockDatum c)

/-- T07.I.b.height for the complete terminal full-contact infection tree. The
source data assumptions and positive intensities are needed only eventually. -/
theorem physical_sir_uniform_height_limit_of_source_ratio (rate : ℕ → ℝ≥0)
    (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    Tendsto (fun n => physicalTerminalUniformHeightScaledLaw (mu n) n (X n)) atTop
      (𝓝 (geometricSurvivalScalarLaw lam ((lam : ℝ) / ((lam : ℝ) - 1)))) := by
  have hl0 : (0 : ℝ) < lam := lt_trans (by norm_num) hlam
  have hscaled := scaled_rate_of_source_ratio rate lam (by exact_mod_cast hl0) hratio
  have hp := eventually_rate_pos_of_scaled_limit rate hl0 hscaled
  apply (embedded_sir_uniform_height_limit_of_source_ratio rate lam hlam hratio).congr'
  filter_upwards [hp, hdata] with n hpn hdn
  exact (hdn.terminalUniformHeightScaledLaw_eq hpn).symm

/-- T07.I.b.distance for independent conditional uniform vertices of the same full
terminal physical tree, with their diagonal retained. -/
theorem physical_sir_uniform_distance_limit_of_source_ratio (rate : ℕ → ℝ≥0)
    (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    Tendsto (fun n => physicalTerminalUniformDistanceScaledLaw (mu n) n (X n)) atTop
      (𝓝 (geometricSurvivalScalarLaw lam (2 * (lam : ℝ) / ((lam : ℝ) - 1)))) := by
  have hl0 : (0 : ℝ) < lam := lt_trans (by norm_num) hlam
  have hscaled := scaled_rate_of_source_ratio rate lam (by exact_mod_cast hl0) hratio
  have hp := eventually_rate_pos_of_scaled_limit rate hl0 hscaled
  apply (embedded_sir_uniform_distance_limit_of_source_ratio rate lam hlam hratio).congr'
  filter_upwards [hp, hdata] with n hpn hdn
  exact (hdn.terminalUniformDistanceScaledLaw_eq hpn).symm

end Limits

end Freezing1.SIR
