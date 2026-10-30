module

public import Freezing1.SIRPhysicalFiniteLimits

/-! Actual conditional samples and their finite-rate source limits. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

example {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) :
    (physicalTerminalUniformHeightScaledLaw mu n X : Measure ℝ) =
      (physicalUniformHeightLaw mu n X (2 * n + 1)).map
        (fun h : ℕ => (h : ℝ) / Real.log (n : ℝ)) := rfl

example {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) :
    (physicalTerminalUniformDistanceScaledLaw mu n X : Measure ℝ) =
      (physicalPairDataLaw mu n X (2 * n + 1)).map
        (fun z : ℕ × ℕ × ℕ => (z.2.2 : ℝ) / Real.log (n : ℝ)) := rfl

section Families

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (mu : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (mu n)]
  (X : (n : ℕ) → (c : ClockSlot n) → Ω n → ClockDatum c)

example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    Tendsto (fun n => physicalTerminalUniformHeightScaledLaw (mu n) n (X n)) atTop
      (𝓝 (geometricSurvivalScalarLaw lam ((lam : ℝ) / ((lam : ℝ) - 1)))) :=
  physical_sir_uniform_height_limit_of_source_ratio mu X rate lam hlam hratio hdata

example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    Tendsto (fun n => physicalTerminalUniformDistanceScaledLaw (mu n) n (X n)) atTop
      (𝓝 (geometricSurvivalScalarLaw lam (2 * (lam : ℝ) / ((lam : ℝ) - 1)))) :=
  physical_sir_uniform_distance_limit_of_source_ratio mu X rate lam hlam hratio hdata

end Families

#print axioms physical_sampleLaw_probability
#print axioms PoissonSIRData.terminalUniformHeightScaledLaw_eq
#print axioms PoissonSIRData.terminalUniformDistanceScaledLaw_eq
#print axioms physical_sir_uniform_height_limit_of_source_ratio
#print axioms physical_sir_uniform_distance_limit_of_source_ratio

end Freezing1.SIR
