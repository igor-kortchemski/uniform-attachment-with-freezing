module

public import Freezing1.UnorderedTreeQuotientCore
public import Freezing1.RootedUnorderedGraphIsoConverse
public import Freezing1.PlaneRootedGraphIso

/-!
# The source local topology on arbitrary unordered labelled locally finite trees

The finite reflection dependency is discharged by the proved finite graph
isomorphism converse. The domain is the actual forgetting-order quotient,
and the complete metric and all truncation criteria have no extra proof
premise. Edge and vertex labels may repeat and need not be chronological.
-/

@[expose] public section

namespace Freezing1.UnorderedLocal

open BinaryBijection Filter
open scoped Topology Classical

theorem finiteIsoReflection : FiniteIsoReflection := by
  intro s t he
  exact Rooted.unorderedEq_of_nonempty_unorderedIso he

noncomputable instance : TopologicalSpace Tree := topology finiteIsoReflection

instance : PolishSpace Tree := polishSpace_topology finiteIsoReflection

theorem complete_separable_metric : LocalTopologyVariants.HasCompleteSeparableMetric Tree :=
  completeSeparableMetric_topology finiteIsoReflection

@[instance_reducible] noncomputable def localMetricSpace : MetricSpace Tree :=
  TopologicalSpace.completelyMetrizableMetric Tree

theorem localMetricSpace_complete : @CompleteSpace Tree localMetricSpace.toUniformSpace :=
  TopologicalSpace.complete_completelyMetrizableMetric Tree

theorem localMetricSpace_topology :
    localMetricSpace.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace Tree) := rfl

theorem localMetricSpace_separable :
    @TopologicalSpace.SeparableSpace Tree localMetricSpace.toUniformSpace.toTopologicalSpace := by
  change TopologicalSpace.SeparableSpace Tree
  infer_instance

noncomputable def localDist (S T : Tree) : ℝ :=
  let : MetricSpace Tree := localMetricSpace
  dist S T

noncomputable def finiteBall (T : Tree) (h : ℕ) : FiniteTree := finiteTrunc finiteIsoReflection T h

@[simp] theorem finiteBall_ofPlane (T : PlaneSource) (h : ℕ) :
    finiteBall (ofPlane T) h = ofRooted (PlaneLabelled.finiteRooted T h) := rfl

theorem finiteBall_restrict (T : Tree) {h H : ℕ} (hh : h ≤ H) :
    truncate h (finiteBall T H) = finiteBall T h := (towerMap finiteIsoReflection T).truncate_ball hh

theorem finiteBall_ofPlane_eq_iff_actualIso (S T : PlaneSource) (h : ℕ) :
    finiteBall (ofPlane S) h = finiteBall (ofPlane T) h ↔
      Nonempty (PlaneLabelled.UnorderedIso (PlaneLabelled.finiteRooted S h).toPlaneLabelled
        (PlaneLabelled.finiteRooted T h).toPlaneLabelled) :=
  finiteClasses_eq_iff_actualIso finiteIsoReflection _ _

theorem ofPlane_eq_iff_graphIso (S T : PlaneSource) :
    ofPlane S = ofPlane T ↔
      ∃ e : (PlaneTree.graph (PlaneLabelled.shape S)).Iso (PlaneTree.graph (PlaneLabelled.shape T)),
        e (LocalTree.root (PlaneTree.auxiliaryTree (PlaneLabelled.shape S))) =
          LocalTree.root (PlaneTree.auxiliaryTree (PlaneLabelled.shape T)) ∧
        (∀ u, PlaneLabelled.vertexSlot S u.val =
          PlaneLabelled.vertexSlot T (PlaneLabelled.graphAddressEquiv e u).val) ∧
        (∀ u, PlaneLabelled.edgeSlot S u.val =
          PlaneLabelled.edgeSlot T (PlaneLabelled.graphAddressEquiv e u).val) :=
  (ofPlane_eq_iff S T).trans (PlaneLabelled.nonempty_unorderedIso_iff_graphIso S T)

noncomputable def localTreeEquiv : Tree ≃ BallTower := treeTowerEquiv finiteIsoReflection

theorem tree_tendsto_iff_balls {ι : Type*} {l : Filter ι} (S : ι → Tree) (T : Tree) :
    Tendsto S l (𝓝 T) ↔ ∀ h, ∀ᶠ i in l, finiteBall (S i) h = finiteBall T h :=
  quotient_tendsto_iff_balls finiteIsoReflection S T

theorem tree_tendsto_iff_positive_balls {ι : Type*} {l : Filter ι} (S : ι → Tree) (T : Tree) :
    Tendsto S l (𝓝 T) ↔ ∀ h, 1 ≤ h → ∀ᶠ i in l, finiteBall (S i) h = finiteBall T h :=
  quotient_tendsto_iff_positive_balls finiteIsoReflection S T

theorem tree_sequence_tendsto_iff (S : ℕ → Tree) (T : Tree) :
    Tendsto S atTop (𝓝 T) ↔ ∀ h, 1 ≤ h → ∃ N : ℕ, ∀ n ≥ N, finiteBall (S n) h = finiteBall T h := by
  simpa only [eventually_atTop] using tree_tendsto_iff_positive_balls (l := atTop) S T

theorem exists_actual_graph_representative (T : Tree) :
    ∃ P : PlaneSource, ofPlane P = T ∧ (PlaneTree.graph (PlaneLabelled.shape P)).IsTree ∧
      Nonempty (PlaneTree.graph (PlaneLabelled.shape P)).LocallyFinite := by
  obtain ⟨P, hp⟩ := exists_plane_representative T
  exact ⟨P, hp, PlaneTree.graph_isTree _, ⟨PlaneTree.graph_locallyFinite _⟩⟩

end Freezing1.UnorderedLocal
