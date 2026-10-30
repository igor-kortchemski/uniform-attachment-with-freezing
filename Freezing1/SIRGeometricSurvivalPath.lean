module

public import Freezing1.SIRPathSpace
public import Freezing1.PlaneFiniteExtinction

/-!
# The same fluid mixture indexed by genuine Bienaymé survival

The event is infinitude of the complete geometric Bienaymé tree. Its proved
probability identifies this source formulation with the two-point path law.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Classical

noncomputable def geometricSurvivalPath (lam : ℝ≥0) (T : PlaneTree.Tree) : PopulationPath :=
  if ¬PlaneTree.FiniteVertices T then positiveProfilePath lam else zeroPopulationPath

theorem measurable_geometricSurvivalPath (lam : ℝ≥0) : Measurable (geometricSurvivalPath lam) :=
  Measurable.ite PlaneTree.measurableSet_finiteVertices.compl measurable_const measurable_const

noncomputable def geometricSurvivalPathLaw (lam : ℝ≥0) : ProbabilityMeasure PopulationPath :=
  ProbabilityMeasure.map
    (⟨PlaneTree.geometricBienaymeLaw (infectionProbability lam 1), inferInstance⟩ :
      ProbabilityMeasure PlaneTree.Tree) (geometricSurvivalPath lam)

theorem geometricSurvivalPathLaw_eq_fluidMixtureLaw (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ)) : geometricSurvivalPathLaw lam = fluidMixtureLaw lam := by
  let μ := PlaneTree.geometricBienaymeLaw (infectionProbability lam 1)
  let s : Set PlaneTree.Tree := {T | ¬PlaneTree.FiniteVertices T}
  have hs : MeasurableSet s := PlaneTree.measurableSet_finiteVertices.compl
  let X : PlaneTree.Tree → ℕ := s.indicator (fun _ => 1)
  let F : ℕ → PopulationPath := fun k => if k = 1 then positiveProfilePath lam else zeroPopulationPath
  have hmX : Measurable X := measurable_const.indicator hs
  have hmF : Measurable F := measurable_of_countable _
  have hX := hasLaw_indicator_bernoulliMeasure (P := μ) (1 : ℕ) hs.nullMeasurableSet
  have hp : (⟨μ.real s, by simp⟩ : unitInterval) = sirSurvivalParameter lam := by
    apply Subtype.ext
    change μ.real s = (sirSurvivalParameter lam : ℝ)
    rw [sirSurvivalParameter_coe hlam]
    exact geometric_sir_survival_real lam hlam
  have he : geometricSurvivalPath lam = F ∘ X := by
    funext T
    by_cases hT : ¬PlaneTree.FiniteVertices T <;>
      simp [geometricSurvivalPath, F, X, s, hT]
  apply Subtype.ext
  change μ.map (geometricSurvivalPath lam) =
    (bernoulliMeasure true false (sirSurvivalParameter lam)).map
      (fun b : Bool => if b then positiveProfilePath lam else zeroPopulationPath)
  calc
    _ = (μ.map X).map F := by rw [Measure.map_map hmF hmX, ← he]
    _ = (bernoulliMeasure (1 : ℕ) 0 (sirSurvivalParameter lam)).map F := by rw [hX.map_eq, hp]
    _ = bernoulliMeasure (positiveProfilePath lam) zeroPopulationPath (sirSurvivalParameter lam) := by
      rw [map_bernoulliMeasure]
      simp [F]
    _ = _ := by rw [map_bernoulliMeasure]; rfl

end Freezing1.SIR
