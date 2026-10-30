module

public import Freezing1.MainSIRUniformSamplesFiniteJoint
public import Freezing1.SIRSampleMarginals
public import Freezing1.SIRGeometricSurvivalScalar
public import Freezing1.MainSIREmbedded

/-!
# Finite-rate terminal SIR height and distance limits

The scalar laws are exactly the actual terminal conditionally uniform
samples, divided by log n. Both targets use the same concrete geometric
Bienaymé survival event.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

theorem embedded_sir_uniform_height_limit (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ))) :
    Tendsto (fun n => terminalUniformHeightScaledLaw (rate n) n) atTop
      (𝓝 (geometricSurvivalScalarLaw lam ((lam : ℝ) / ((lam : ℝ) - 1)))) := by
  rw [geometricSurvivalScalarLaw_eq_twoPoint lam hlam]
  apply TwoPointMixture.marginal_tendsto
  · simpa only [sirSurvivalParameter_coe hlam] using
      sir_terminal_joint_height_gate_tendsto rate lam hlam hscaled
  · exact fun eps heps => sir_terminal_joint_height_real_concentrates rate lam hlam hscaled heps

theorem embedded_sir_uniform_distance_limit (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ))) :
    Tendsto (fun n => terminalUniformDistanceScaledLaw (rate n) n) atTop
      (𝓝 (geometricSurvivalScalarLaw lam (2 * (lam : ℝ) / ((lam : ℝ) - 1)))) := by
  rw [geometricSurvivalScalarLaw_eq_twoPoint lam hlam]
  apply TwoPointMixture.marginal_tendsto
  · simpa only [sirSurvivalParameter_coe hlam] using
      sir_terminal_joint_distance_gate_tendsto rate lam hlam hscaled
  · exact fun eps heps => sir_terminal_joint_distance_real_concentrates rate lam hlam hscaled heps

theorem embedded_sir_uniform_height_limit_of_source_ratio (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n => terminalUniformHeightScaledLaw (rate n) n) atTop
      (𝓝 (geometricSurvivalScalarLaw lam ((lam : ℝ) / ((lam : ℝ) - 1)))) :=
  embedded_sir_uniform_height_limit rate lam hlam
    (scaled_rate_of_source_ratio rate lam (by exact_mod_cast (lt_trans zero_lt_one hlam)) hratio)

theorem embedded_sir_uniform_distance_limit_of_source_ratio (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n => terminalUniformDistanceScaledLaw (rate n) n) atTop
      (𝓝 (geometricSurvivalScalarLaw lam (2 * (lam : ℝ) / ((lam : ℝ) - 1)))) :=
  embedded_sir_uniform_distance_limit rate lam hlam
    (scaled_rate_of_source_ratio rate lam (by exact_mod_cast (lt_trans zero_lt_one hlam)) hratio)

end Freezing1.SIR
