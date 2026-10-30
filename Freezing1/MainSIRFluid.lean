module

public import Freezing1.MainSIRFluidMixture
public import Freezing1.SIRGeometricSurvivalPath

/-!
# The finite-rate SIR fluid limit with the source survival event

The limiting path uses one geometric Bienaymé tree, and its survival event
is shared by every observation time. The actual stopped embedded population
law converges in the topology of uniform convergence on compact time sets.
Identification with the independent physical clock history is still separate.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory
open scoped NNReal Topology

theorem embedded_sir_fluid_limit (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ))) :
    Tendsto (fun n : ℕ => populationPathLaw (rate n) n) atTop
      (𝓝 (geometricSurvivalPathLaw lam)) := by
  rw [geometricSurvivalPathLaw_eq_fluidMixtureLaw lam hlam]
  exact embedded_sir_fluid_mixture_limit rate lam hlam hrate

theorem embedded_sir_fluid_limit_of_source_ratio (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => populationPathLaw (rate n) n) atTop
      (𝓝 (geometricSurvivalPathLaw lam)) := by
  rw [geometricSurvivalPathLaw_eq_fluidMixtureLaw lam hlam]
  exact embedded_sir_fluid_mixture_limit_of_source_ratio rate lam hlam hratio

end Freezing1.SIR
