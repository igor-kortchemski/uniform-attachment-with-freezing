module

public import Freezing1.ForwardChronologicalPlaneBridge
public import Freezing1.ForwardAnnealedLifetime

/-!
# The actual annealed plane-tree limit

The limit is obtained by ordering the actual labelled local limit and
erasing labels. The finite chronological states give the same plane trees,
so both their almost-sure convergence and their weak limit law follow.
-/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open Forward ForwardInfiniteHistory Filter MeasureTheory
open scoped Topology Classical

noncomputable def planeLimit (H : History) : PlaneTree.Tree :=
  LocalTree.toPlaneTree (ForwardInfiniteHistory.localLimit H)

noncomputable def planeProbabilityLaw (p : unitInterval) (n : ℕ) :
    ProbabilityMeasure PlaneTree.Tree :=
  (localProbabilityLaw p n).map LocalTree.toPlaneTree

noncomputable def planeLimitLaw (p : unitInterval) : ProbabilityMeasure PlaneTree.Tree :=
  (localLimitLaw p).map LocalTree.toPlaneTree

theorem aemeasurable_planeLimit (p : unitInterval) (hp : (p : ℝ) < 1) :
    AEMeasurable planeLimit (fullLaw p) :=
  LocalTree.continuous_toPlaneTree.measurable.comp_aemeasurable (aemeasurable_localLimit p hp)

theorem fullLaw_tendsto_planeLimit (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ H ∂fullLaw p,
      Tendsto (fun n => LocalTree.toPlaneTree (localTreeOfState (H n))) atTop
        (𝓝 (planeLimit H)) := by
  filter_upwards [fullLaw_tendsto_localLimit p hp] with H hH
  exact (LocalTree.continuous_toPlaneTree.tendsto _).comp hH

theorem fullLaw_tendsto_projectedShape (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ H ∂fullLaw p,
      Tendsto (fun n => PlaneForward.shape (H n).toPlaneState) atTop
        (𝓝 (planeLimit H)) := by
  filter_upwards [fullLaw_tendsto_planeLimit p hp, fullLaw_shape_eq_toPlaneTree p]
    with H hH he
  exact hH.congr' (Eventually.of_forall fun n => (he n).symm)

theorem tendsto_planeProbabilityLaw (p : unitInterval) (hp : (p : ℝ) < 1) :
    Tendsto (planeProbabilityLaw p) atTop (𝓝 (planeLimitLaw p)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (localProbabilityLaw p) (localLimitLaw p) (tendsto_localProbabilityLaw p hp)
    LocalTree.continuous_toPlaneTree

theorem planeLimitLaw_eq_map (p : unitInterval) (hp : (p : ℝ) < 1) :
    (planeLimitLaw p : Measure PlaneTree.Tree) = (fullLaw p).map planeLimit := by
  change ((fullLaw p).map ForwardInfiniteHistory.localLimit).map LocalTree.toPlaneTree = _
  rw [AEMeasurable.map_map_of_aemeasurable LocalTree.continuous_toPlaneTree.measurable.aemeasurable
    (aemeasurable_localLimit p hp)]
  rfl

theorem planeProbabilityLaw_eq_chainShape (p : unitInterval) (n : ℕ) :
    (planeProbabilityLaw p n : Measure PlaneTree.Tree) =
      (PlaneForward.fullLaw p PlaneForward.initial).map (fun H => PlaneForward.shape (H n)) := by
  change ((treeLaw p n).map localTreeOfState).map LocalTree.toPlaneTree = _
  rw [Measure.map_map LocalTree.continuous_toPlaneTree.measurable measurable_from_top]
  exact map_treeLaw_toPlaneTree p n

end Freezing1.ForwardAnnealed
