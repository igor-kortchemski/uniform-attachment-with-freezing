module

import Freezing1.SIREarlyExtinction
import Freezing1.SIRGeometricSurvivalPath

/-!
Source reconstruction of A73 and the shared survival event in T07.I.a.
The events below use the entire Ulam--Harris vertex set. The early SIR
probability is taken under the actual stopped count law at floor(delta*n).
-/

open Freezing1 Filter MeasureTheory
open scoped NNReal ENNReal Topology

example (lam : ℝ≥0) (hlam : 1 < (lam : ℝ)) :
    (PlaneTree.geometricBienaymeLaw (SIR.infectionProbability lam 1)).real
      {T | Set.Infinite {u : PlaneTree.Address | PlaneTree.Present T u}} =
      1 - 1 / (lam : ℝ) :=
  SIR.geometric_sir_survival_real lam hlam

example (lam : ℝ≥0) (hlam : 1 < (lam : ℝ)) :
    PlaneTree.geometricBienaymeLaw (SIR.infectionProbability lam 1)
      {T | Set.Finite {u : PlaneTree.Address | PlaneTree.Present T u}} =
      ENNReal.ofReal (1 / (lam : ℝ)) :=
  SIR.geometric_sir_finite_probability lam hlam

example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta ∈ Set.Ioo (0 : ℝ) delta0,
      ∀ᶠ n : ℕ in atTop,
        |(SIR.countsFullLaw (rate n) n).real
          {H | (H ⌊delta * n⌋₊).infectious = 0} - 1 / (lam : ℝ)| < eps :=
  SIR.countsFullLaw_early_extinction_two_stage rate lam hlam hrate heps

example (lam : ℝ≥0) (hlam : 1 < (lam : ℝ)) :
    SIR.geometricSurvivalPathLaw lam = SIR.fluidMixtureLaw lam :=
  SIR.geometricSurvivalPathLaw_eq_fluidMixtureLaw lam hlam

example : (PlaneTree.geometricBienaymeLaw (SIR.infectionProbability 2 1)).real
    {T | Set.Infinite {u : PlaneTree.Address | PlaneTree.Present T u}} = 1 / 2 := by
  have h := SIR.geometric_sir_survival_real 2 (by norm_num)
  change (PlaneTree.geometricBienaymeLaw (SIR.infectionProbability 2 1)).real
    {T | ¬PlaneTree.FiniteVertices T} = 1 / 2
  norm_num at h ⊢
  exact h

#print axioms Freezing1.SIR.countsFullLaw_early_extinction_two_stage
#print axioms Freezing1.SIR.countsFullLaw_early_survival_eventually
#print axioms Freezing1.PlaneForward.fullLaw_finite_chainLimit_iff_absorbed
#print axioms Freezing1.PlaneForward.fullLaw_ever_absorbed_probability
#print axioms Freezing1.SIR.geometric_sir_survival_real
#print axioms Freezing1.SIR.geometricSurvivalPathLaw_eq_fluidMixtureLaw

