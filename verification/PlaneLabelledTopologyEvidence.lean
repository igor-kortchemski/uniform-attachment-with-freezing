module

import Freezing1.PlaneTreeLabellings
import Freezing1.LocalTopologyVariants

open Filter Freezing1
open scoped Topology

namespace PlaneLabelledTopologyEvidence

example : PolishSpace PlaneTree.Tree := inferInstance

example (V E : Type*) [Countable V] [Countable E] : PolishSpace (PlaneLabelled.Tree V E) :=
  inferInstance

example : PolishSpace (PlaneLabelled.Tree (Option ℕ) ℕ) := inferInstance

example (V E : Type*) [Countable V] [Countable E] :
    ∃ m : MetricSpace (PlaneLabelled.Tree V E),
      m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace (PlaneLabelled.Tree V E)) ∧
      @CompleteSpace (PlaneLabelled.Tree V E) m.toUniformSpace ∧
      @TopologicalSpace.SeparableSpace (PlaneLabelled.Tree V E) m.toUniformSpace.toTopologicalSpace :=
  LocalTopologyVariants.plane_labelled_metric V E

example (S : ℕ → PlaneTree.Tree) (T : PlaneTree.Tree) :
    Tendsto S atTop (𝓝 T) ↔ ∀ h, 1 ≤ h → ∃ N : ℕ, ∀ n ≥ N, PlaneTree.ball (S n) h = PlaneTree.ball T h := by
  simpa only [eventually_atTop] using PlaneTree.tendsto_iff_positive_balls (l := atTop) S T

example {V E : Type*} (S : ℕ → PlaneLabelled.Tree V E) (T : PlaneLabelled.Tree V E) :
    Tendsto S atTop (𝓝 T) ↔ ∀ h, 1 ≤ h → ∃ N : ℕ, ∀ n ≥ N,
      PlaneLabelled.ball (S n) h = PlaneLabelled.ball T h := by
  simpa only [eventually_atTop] using PlaneLabelled.tendsto_iff_positive_balls (l := atTop) S T

example {V E : Type*} (T : PlaneTree.Tree) (v : PlaneLabelled.Vertex T → V)
    (e : PlaneLabelled.Edge T → E) :
    PlaneLabelled.shape (PlaneLabelled.decorate T v e) = T := PlaneLabelled.shape_decorate T v e

example {V E : Type*} (T : PlaneLabelled.Tree V E) :
    PlaneLabelled.decorate (PlaneLabelled.shape T) (PlaneLabelled.vertexLabel T)
      (PlaneLabelled.edgeLabel T) = T := PlaneLabelled.decorate_recovered T

#print axioms PlaneLabelled.isClopen_present
#print axioms PlaneLabelled.isClosed_valid
#print axioms PlaneLabelled.ball_restrict
#print axioms PlaneLabelled.tendsto_iff_balls
#print axioms PlaneLabelled.tendsto_iff_positive_balls
#print axioms PlaneLabelled.decorate
#print axioms PlaneLabelled.decorate_recovered
#print axioms PlaneLabelled.decorate_surjective
#print axioms LocalTopologyVariants.hasCompleteSeparableMetric
#print axioms LocalTopologyVariants.plane_metric
#print axioms LocalTopologyVariants.plane_labelled_metric
#print axioms LocalTopologyVariants.chronological_metric
#print axioms PlaneTree.tendsto_iff_positive_balls
#print axioms LocalTree.tendsto_iff_positive_balls

end PlaneLabelledTopologyEvidence
