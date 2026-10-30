module

import Freezing1.UnorderedTreeTopology

noncomputable section

open Freezing1 Filter
open scoped Topology

namespace UnorderedLocalTopologyEvidence

example : PolishSpace UnorderedLocal.Tree := inferInstance

example : ∃ m : MetricSpace UnorderedLocal.Tree,
    m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace UnorderedLocal.Tree) ∧
    @CompleteSpace UnorderedLocal.Tree m.toUniformSpace ∧
    @TopologicalSpace.SeparableSpace UnorderedLocal.Tree m.toUniformSpace.toTopologicalSpace :=
  UnorderedLocal.complete_separable_metric

example : @CompleteSpace UnorderedLocal.Tree UnorderedLocal.localMetricSpace.toUniformSpace :=
  UnorderedLocal.localMetricSpace_complete

example : UnorderedLocal.localMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace UnorderedLocal.Tree) := UnorderedLocal.localMetricSpace_topology

example : @TopologicalSpace.SeparableSpace UnorderedLocal.Tree
    UnorderedLocal.localMetricSpace.toUniformSpace.toTopologicalSpace :=
  UnorderedLocal.localMetricSpace_separable

example (S : ℕ → UnorderedLocal.Tree) (T : UnorderedLocal.Tree) :
    Tendsto S atTop (𝓝 T) ↔ ∀ h, 1 ≤ h → ∃ N : ℕ, ∀ n ≥ N,
      UnorderedLocal.finiteBall (S n) h = UnorderedLocal.finiteBall T h :=
  UnorderedLocal.tree_sequence_tendsto_iff S T

example (T : UnorderedLocal.PlaneSource) (h : ℕ) :
    UnorderedLocal.finiteBall (UnorderedLocal.ofPlane T) h =
      UnorderedLocal.ofRooted (PlaneLabelled.finiteRooted T h) := rfl

example (S T : UnorderedLocal.PlaneSource) (h : ℕ) :
    UnorderedLocal.finiteBall (UnorderedLocal.ofPlane S) h =
      UnorderedLocal.finiteBall (UnorderedLocal.ofPlane T) h ↔
      Nonempty (PlaneLabelled.UnorderedIso (PlaneLabelled.finiteRooted S h).toPlaneLabelled
        (PlaneLabelled.finiteRooted T h).toPlaneLabelled) :=
  UnorderedLocal.finiteBall_ofPlane_eq_iff_actualIso S T h

example (T : UnorderedLocal.Tree) :
    ∃ P : UnorderedLocal.PlaneSource, UnorderedLocal.ofPlane P = T ∧
      (PlaneTree.graph (PlaneLabelled.shape P)).IsTree ∧
      Nonempty (PlaneTree.graph (PlaneLabelled.shape P)).LocallyFinite :=
  UnorderedLocal.exists_actual_graph_representative T

example : UnorderedLocal.Tree ≃ UnorderedLocal.BallTower := UnorderedLocal.localTreeEquiv

example : PolishSpace PlaneTree.Tree := inferInstance

example (V E : Type*) [Countable V] [Countable E] : PolishSpace (PlaneLabelled.Tree V E) := inferInstance

#print axioms UnorderedLocal.finiteIsoReflection
#print axioms UnorderedLocal.localTreeEquiv
#print axioms UnorderedLocal.complete_separable_metric
#print axioms UnorderedLocal.localMetricSpace_complete
#print axioms UnorderedLocal.localMetricSpace_topology
#print axioms UnorderedLocal.localMetricSpace_separable
#print axioms UnorderedLocal.finiteBall_ofPlane_eq_iff_actualIso
#print axioms UnorderedLocal.ofPlane_eq_iff_graphIso
#print axioms UnorderedLocal.tree_tendsto_iff_balls
#print axioms UnorderedLocal.tree_tendsto_iff_positive_balls
#print axioms UnorderedLocal.tree_sequence_tendsto_iff
#print axioms UnorderedLocal.exists_actual_graph_representative

end UnorderedLocalTopologyEvidence
