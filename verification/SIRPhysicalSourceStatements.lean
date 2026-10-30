module

import Freezing1.SIRPhysicalFiniteLimits
import Freezing1.SIRPhysicalLimits

/-!
Independent reconstruction of source-model assumptions and main transfers.
The reviewer authored none of the physical protocol/law/limit modules.
-/

open Freezing1 Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

namespace Verification.PhysicalSource

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (mu : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (mu n)]
  (X : (n : ℕ) → (c : SIR.ClockSlot n) → Ω n → SIR.ClockDatum c)
  (rate : ℕ → ℝ≥0)
  (hsource : ∀ᶠ n in atTop,
    (∀ c, Measurable (X n c)) ∧ iIndepFun (X n) (mu n) ∧
      (∀ v : SIR.Individual n, (mu n).map (X n (v, none)) = expMeasure 1) ∧
      (∀ v w : SIR.Individual n, ∀ t : ℝ≥0,
        ((mu n).map (X n (v, some w))).map
          (fun a => SIR.PoissonContact.count a (t : ℝ)) = poissonMeasure (rate n * t)))

include hsource in
omit [∀ n, IsProbabilityMeasure (mu n)] in
private theorem sourceData : ∀ᶠ n in atTop, SIR.PoissonSIRData (mu n) n (rate n) (X n) :=
  hsource.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

example (lam : ℝ≥0) (hlam : 0 < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n => SIR.physicalTerminalTreeLaw (mu n) n (X n)) atTop
      (𝓝 (SIR.geometricProbabilityLaw (SIR.infectionProbability lam 1))) :=
  SIR.physical_sir_geometric_local_limit_of_source_ratio mu X rate lam hlam hratio
    (sourceData mu X rate hsource)

example (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n => SIR.physicalPopulationPathLaw (mu n) n (X n)) atTop
      (𝓝 (SIR.geometricSurvivalPathLaw lam)) :=
  SIR.physical_sir_fluid_limit_of_source_ratio mu X rate lam hlam hratio
    (sourceData mu X rate hsource)

example (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n => SIR.physicalTerminalUniformHeightScaledLaw (mu n) n (X n)) atTop
      (𝓝 (ProbabilityMeasure.map
        (⟨PlaneTree.geometricBienaymeLaw (SIR.infectionProbability lam 1), inferInstance⟩ :
          ProbabilityMeasure PlaneTree.Tree)
        (fun T => if ¬PlaneTree.FiniteVertices T then (lam : ℝ) / ((lam : ℝ) - 1) else 0))) :=
  SIR.physical_sir_uniform_height_limit_of_source_ratio mu X rate lam hlam hratio
    (sourceData mu X rate hsource)

example (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n => SIR.physicalTerminalUniformDistanceScaledLaw (mu n) n (X n)) atTop
      (𝓝 (ProbabilityMeasure.map
        (⟨PlaneTree.geometricBienaymeLaw (SIR.infectionProbability lam 1), inferInstance⟩ :
          ProbabilityMeasure PlaneTree.Tree)
        (fun T => if ¬PlaneTree.FiniteVertices T then 2 * (lam : ℝ) / ((lam : ℝ) - 1) else 0))) :=
  SIR.physical_sir_uniform_distance_limit_of_source_ratio mu X rate lam hlam hratio
    (sourceData mu X rate hsource)

example (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop) :
    ¬IsTightMeasureSet (Set.range fun n =>
      (SIR.physicalTerminalTreeLaw (mu n) n (X n) : Measure PlaneTree.Tree)) :=
  SIR.physical_sir_not_tight_of_source_ratio mu X rate hratio (sourceData mu X rate hsource)

example (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (SIR.physicalTreePathLaw (mu n) n (X n) : Measure (ℕ → SIR.TreeState))
      {H | eps ≤ |(((H (2*n+1)).tree.vertices.sup List.length : ℕ) : ℝ) /
        Real.log (n : ℝ) - Real.exp 1|}) atTop (𝓝 0) :=
  SIR.physical_sir_strong_terminal_maximum_of_source_ratio mu X rate hratio
    (sourceData mu X rate hsource) heps

#print axioms Freezing1.SIR.physical_sir_geometric_local_limit_of_source_ratio
#print axioms Freezing1.SIR.physical_sir_not_tight_of_source_ratio
#print axioms Freezing1.SIR.physical_sir_fluid_limit_of_source_ratio
#print axioms Freezing1.SIR.physical_sir_uniform_height_limit_of_source_ratio
#print axioms Freezing1.SIR.physical_sir_uniform_distance_limit_of_source_ratio
#print axioms Freezing1.SIR.physical_sir_strong_terminal_maximum_of_source_ratio

end Verification.PhysicalSource
