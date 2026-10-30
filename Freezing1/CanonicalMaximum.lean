module

public import Freezing1.CanonicalUniformSampling
public import Freezing1.TreeSourceChecks

/-! # Transfer of the actual maximum height through T05 -/

@[expose] public section

namespace Freezing1.CanonicalTree

open MeasureTheory

theorem reverseState_treeHeight {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    Forward.treeHeight (reverseState F) = reverseMaximum F.forest := by
  unfold Forward.treeHeight reverseMaximum
  change (F.forest.vertices.image F.edgeTime).sup (reverseState F).height = _
  rw [Finset.sup_image]
  apply Finset.sup_congr rfl
  intro v hv
  exact (reverseState_vertex_data hinj hv).2.1

theorem forward_maximum_law_eq_reverse (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (Forward.treeLaw x n).map Forward.treeHeight =
      (Reverse.treeLaw x n).map reverseMaximum := by
  rw [← reverseStateLaw_eq_forward_treeLaw x n hn, reverseStateLaw,
    Measure.map_map measurable_from_top measurable_from_top,
    ← ReverseStamped.map_treeLaw x n,
    Measure.map_map measurable_from_top measurable_from_top]
  apply Measure.map_congr
  filter_upwards [ReverseStamped.treeLaw_canonical_ids x n hn] with F hF
  exact reverseState_treeHeight hF.1

end Freezing1.CanonicalTree
