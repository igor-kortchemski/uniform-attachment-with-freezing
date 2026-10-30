module

import Freezing1.UnorderedTreeTopology
import Freezing1.PlaneTreeLabellings

/-! Source-reconstructed topology statements by the integrating reviewer,
who did not author the broad-space construction or finite graph classification. -/

open Filter TopologicalSpace
open scoped Topology Classical
open Freezing1 Freezing1.UnorderedLocal

example : ∃ m : MetricSpace Tree,
    m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace Tree) ∧
      @CompleteSpace Tree m.toUniformSpace ∧
      @SeparableSpace Tree m.toUniformSpace.toTopologicalSpace :=
  complete_separable_metric

example : @CompleteSpace Tree localMetricSpace.toUniformSpace := localMetricSpace_complete

example : localMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace Tree) := localMetricSpace_topology

example (S : ℕ → Tree) (T : Tree) :
    Tendsto S atTop (𝓝 T) ↔
      ∀ h : ℕ, 1 ≤ h → ∃ N : ℕ, ∀ n ≥ N, finiteBall (S n) h = finiteBall T h :=
  tree_sequence_tendsto_iff S T

example (S T : PlaneSource) (h : ℕ) :
    finiteBall (ofPlane S) h = finiteBall (ofPlane T) h ↔
      Nonempty (PlaneLabelled.UnorderedIso (PlaneLabelled.finiteRooted S h).toPlaneLabelled
        (PlaneLabelled.finiteRooted T h).toPlaneLabelled) :=
  finiteBall_ofPlane_eq_iff_actualIso S T h

example (S T : PlaneSource) : ofPlane S = ofPlane T ↔
    ∃ e : (PlaneTree.graph (PlaneLabelled.shape S)).Iso (PlaneTree.graph (PlaneLabelled.shape T)),
      e (LocalTree.root (PlaneTree.auxiliaryTree (PlaneLabelled.shape S))) =
        LocalTree.root (PlaneTree.auxiliaryTree (PlaneLabelled.shape T)) ∧
      (∀ u, PlaneLabelled.vertexSlot S u.val =
        PlaneLabelled.vertexSlot T (PlaneLabelled.graphAddressEquiv e u).val) ∧
      (∀ u, PlaneLabelled.edgeSlot S u.val =
        PlaneLabelled.edgeSlot T (PlaneLabelled.graphAddressEquiv e u).val) :=
  ofPlane_eq_iff_graphIso S T

example (T : Tree) : ∃ P : PlaneSource, ofPlane P = T ∧
    (PlaneTree.graph (PlaneLabelled.shape P)).IsTree ∧
      Nonempty (PlaneTree.graph (PlaneLabelled.shape P)).LocallyFinite :=
  exists_actual_graph_representative T

example (B : BallTower) : ∃ T : Tree, ∀ h, finiteBall T h = B.val h := by
  obtain ⟨T, hT⟩ := localTreeEquiv.surjective B
  refine ⟨T, fun h => ?_⟩
  exact congrArg (fun C : BallTower => C.val h) hT

example (V E : Type*) [Countable V] [Countable E] : PolishSpace (PlaneLabelled.Tree V E) :=
  inferInstance

example (V E : Type*) [Countable V] [Countable E]
    (S : ℕ → PlaneLabelled.Tree V E) (T : PlaneLabelled.Tree V E) :
    Tendsto S atTop (𝓝 T) ↔
      ∀ h, 1 ≤ h → ∀ᶠ n in atTop, PlaneLabelled.ball (S n) h = PlaneLabelled.ball T h :=
  PlaneLabelled.tendsto_iff_positive_balls S T

#print axioms complete_separable_metric
#print axioms localMetricSpace_complete
#print axioms localMetricSpace_separable
#print axioms tree_sequence_tendsto_iff
#print axioms ofPlane_eq_iff_graphIso
#print axioms finiteBall_ofPlane_eq_iff_actualIso
#print axioms exists_actual_graph_representative
#print axioms localTreeEquiv
#print axioms PlaneLabelled.decorate_surjective
#print axioms PlaneLabelled.tendsto_iff_positive_balls
