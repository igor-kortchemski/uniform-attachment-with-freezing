module

public import Freezing1.SIRGeometricSurvivalPath
public import Freezing1.TwoPointMixtureLimit

/-!
# Scalar mixtures on the same concrete Bienaymé survival event
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Classical

noncomputable def geometricSurvivalScalar (_lam : ℝ≥0) (c : ℝ) (T : PlaneTree.Tree) : ℝ :=
  if ¬PlaneTree.FiniteVertices T then c else 0

theorem measurable_geometricSurvivalScalar (lam : ℝ≥0) (c : ℝ) :
    Measurable (geometricSurvivalScalar lam c) :=
  Measurable.ite PlaneTree.measurableSet_finiteVertices.compl measurable_const measurable_const

noncomputable def geometricSurvivalScalarLaw (lam : ℝ≥0) (c : ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (⟨PlaneTree.geometricBienaymeLaw (infectionProbability lam 1), inferInstance⟩ :
      ProbabilityMeasure PlaneTree.Tree) (geometricSurvivalScalar lam c)

theorem geometricSurvivalScalarLaw_eq_twoPoint (lam : ℝ≥0) (hlam : 1 < (lam : ℝ)) (c : ℝ) :
    geometricSurvivalScalarLaw lam c = TwoPointMixture.law (sirSurvivalParameter lam) c := by
  let mu := PlaneTree.geometricBienaymeLaw (infectionProbability lam 1)
  let s : Set PlaneTree.Tree := {T | ¬PlaneTree.FiniteVertices T}
  have hs : MeasurableSet s := PlaneTree.measurableSet_finiteVertices.compl
  let X : PlaneTree.Tree → ℕ := s.indicator (fun _ => 1)
  let F : ℕ → ℝ := fun k => if k = 1 then c else 0
  have hmX : Measurable X := measurable_const.indicator hs
  have hX := hasLaw_indicator_bernoulliMeasure (P := mu) (1 : ℕ) hs.nullMeasurableSet
  have hp : (⟨mu.real s, by simp⟩ : unitInterval) = sirSurvivalParameter lam := by
    apply Subtype.ext
    change mu.real s = (sirSurvivalParameter lam : ℝ)
    rw [sirSurvivalParameter_coe hlam]
    exact geometric_sir_survival_real lam hlam
  have he : geometricSurvivalScalar lam c = F ∘ X := by
    funext T
    by_cases hT : ¬PlaneTree.FiniteVertices T <;>
      simp [geometricSurvivalScalar, F, X, s, hT]
  apply Subtype.ext
  change mu.map (geometricSurvivalScalar lam c) =
    bernoulliMeasure c 0 (sirSurvivalParameter lam)
  calc
    _ = (mu.map X).map F := by
      rw [Measure.map_map (measurable_of_countable F) hmX, ← he]
    _ = (bernoulliMeasure (1 : ℕ) 0 (sirSurvivalParameter lam)).map F := by rw [hX.map_eq, hp]
    _ = _ := by rw [map_bernoulliMeasure]; simp [F]

end Freezing1.SIR
