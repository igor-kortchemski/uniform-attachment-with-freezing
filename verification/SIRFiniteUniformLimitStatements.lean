module

import Freezing1.MainSIRUniformSamplesFinite

/-!
Independent reconstruction of the root agent's final weak-limit assembly.
The geometric input estimates were authored by this reviewer; the weak
aggregation, actual scalar marginal identification, and concrete geometric
survival target were not.
-/

open Freezing1 Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

namespace Verification.SIRFiniteUniformLimits

set_option backward.isDefEq.respectTransparency false

theorem height_is_actual_terminal_sample (rate : ℝ≥0) (n : ℕ) :
    (SIR.terminalUniformHeightScaledLaw rate n : Measure ℝ) =
      (((SIR.treeFullLaw rate n).map (fun H => (H (2 * n + 1)).tree)).bind
        PlaneForward.vertexHeightKernel).map (fun h : ℕ => (h : ℝ) / Real.log (n : ℝ)) :=
  SIR.terminalUniformHeightScaledLaw_eq_sample rate n

theorem distance_is_actual_terminal_pair (rate : ℝ≥0) (n : ℕ) :
    (SIR.terminalUniformDistanceScaledLaw rate n : Measure ℝ) =
      (((SIR.treeFullLaw rate n).map (fun H => (H (2 * n + 1)).tree)).bind
        PlaneForward.pairDataKernel).map (fun z => (z.2.2 : ℝ) / Real.log (n : ℝ)) :=
  SIR.terminalUniformDistanceScaledLaw_eq_sample rate n

theorem height_limit_expanded (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ))) :
    Tendsto (fun n => SIR.terminalUniformHeightScaledLaw (rate n) n) atTop
      (nhds (ProbabilityMeasure.map (⟨PlaneTree.geometricBienaymeLaw (SIR.infectionProbability lam 1), inferInstance⟩ :
        ProbabilityMeasure PlaneTree.Tree)
          (fun T => if ¬PlaneTree.FiniteVertices T then (lam : ℝ) / ((lam : ℝ) - 1) else 0))) :=
  SIR.embedded_sir_uniform_height_limit rate lam hlam hscaled

theorem distance_limit_expanded (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ))) :
    Tendsto (fun n => SIR.terminalUniformDistanceScaledLaw (rate n) n) atTop
      (nhds (ProbabilityMeasure.map (⟨PlaneTree.geometricBienaymeLaw (SIR.infectionProbability lam 1), inferInstance⟩ :
        ProbabilityMeasure PlaneTree.Tree)
          (fun T => if ¬PlaneTree.FiniteVertices T then 2 * (lam : ℝ) / ((lam : ℝ) - 1) else 0))) :=
  SIR.embedded_sir_uniform_distance_limit rate lam hlam hscaled

theorem source_ratio_height (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (nhds 1)) :
    Tendsto (fun n => SIR.terminalUniformHeightScaledLaw (rate n) n) atTop
      (nhds (SIR.geometricSurvivalScalarLaw lam ((lam : ℝ) / ((lam : ℝ) - 1)))) :=
  SIR.embedded_sir_uniform_height_limit_of_source_ratio rate lam hlam hratio

theorem source_ratio_distance (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (nhds 1)) :
    Tendsto (fun n => SIR.terminalUniformDistanceScaledLaw (rate n) n) atTop
      (nhds (SIR.geometricSurvivalScalarLaw lam (2 * (lam : ℝ) / ((lam : ℝ) - 1)))) :=
  SIR.embedded_sir_uniform_distance_limit_of_source_ratio rate lam hlam hratio

#print axioms height_is_actual_terminal_sample
#print axioms distance_is_actual_terminal_pair
#print axioms height_limit_expanded
#print axioms distance_limit_expanded
#print axioms source_ratio_height
#print axioms source_ratio_distance

end Verification.SIRFiniteUniformLimits
