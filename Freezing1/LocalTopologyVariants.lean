module

public import Freezing1.PlaneTreeLabelledTopology
public import Freezing1.LocalTreeGraph

/-!
# Compatible complete metrics and the source's positive-radius criteria

The plane cases use all locally finite Ulam--Harris shapes, with arbitrary
countable discrete labels in the labelled case. The separate chronological
case retains its existing, more specialized domain.
-/

@[expose] public section

namespace Freezing1

open Filter TopologicalSpace
open scoped Topology Classical

namespace LocalTopologyVariants

def HasCompleteSeparableMetric (X : Type*) [t : TopologicalSpace X] : Prop :=
  ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace ∧
    @SeparableSpace X m.toUniformSpace.toTopologicalSpace

theorem hasCompleteSeparableMetric (X : Type*) [TopologicalSpace X] [PolishSpace X] :
    HasCompleteSeparableMetric X := by
  obtain ⟨m, hm, hc⟩ := (inferInstance : TopologicalSpace.IsCompletelyMetrizableSpace X).complete
  refine ⟨m, hm, hc, ?_⟩
  rw [hm]
  infer_instance

theorem plane_metric : HasCompleteSeparableMetric PlaneTree.Tree :=
  hasCompleteSeparableMetric _

theorem plane_labelled_metric (V E : Type*) [Countable V] [Countable E] :
    HasCompleteSeparableMetric (PlaneLabelled.Tree V E) := hasCompleteSeparableMetric _

theorem chronological_metric : HasCompleteSeparableMetric LocalTree.Tree :=
  hasCompleteSeparableMetric _

end LocalTopologyVariants

namespace PlaneTree

theorem tendsto_iff_positive_balls {ι : Type*} {l : Filter ι} (S : ι → Tree) (T : Tree) :
    Tendsto S l (𝓝 T) ↔ ∀ h, 1 ≤ h → ∀ᶠ i in l, ball (S i) h = ball T h := by
  rw [tendsto_iff_balls]
  constructor
  · exact fun hc h _ => hc h
  · intro hc h
    by_cases hh : 1 ≤ h
    · exact hc h hh
    · have hz : h = 0 := by omega
      subst h
      exact Eventually.of_forall (fun _ => by simp [ball, generation])

end PlaneTree

namespace LocalTree

theorem tendsto_iff_positive_balls {ι : Type*} {l : Filter ι} (S : ι → Tree) (T : Tree) :
    Tendsto S l (𝓝 T) ↔ ∀ h, 1 ≤ h → ∀ᶠ i in l, (S i).val h = T.val h := by
  rw [tendsto_iff_balls]
  constructor
  · exact fun hc h _ => hc h
  · intro hc h
    by_cases hh : 1 ≤ h
    · exact hc h hh
    · have hz : h = 0 := by omega
      subst h
      filter_upwards [hc 1 le_rfl] with i hi
      simpa only [Tree.restrict_ball _ (by omega : 0 ≤ 1)] using
        congrArg (restrict 0) hi

end LocalTree

end Freezing1
