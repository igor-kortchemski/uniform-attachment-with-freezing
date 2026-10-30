module

public import Freezing1.ForwardLocalTree
public import Freezing1.ForwardDegree

/-!
# Root degree is a continuous local observable

The radius-one ball contains the root and precisely its neighbours. Its
cardinality therefore recovers the genuine graph degree of a forward state.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped Classical

namespace LocalTree

def rootDegree (T : Tree) : ℕ := (T.val 1).card - 1

theorem continuous_rootDegree : Continuous rootDegree :=
  (continuous_of_discreteTopology : Continuous (fun B : Ball => B.card - 1)).comp
    ((continuous_apply 1).comp continuous_subtype_val)

end LocalTree

namespace Forward

theorem localBall_eq_image (s : State) (h : ℕ) :
    localBall s h = (s.vertices.filter fun v => s.height v ≤ h).image (localRecord s) := by
  ext r
  rw [mem_localBall_iff]
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨v, hv, he, hh⟩
    exact ⟨v, ⟨hv, hh⟩, he⟩
  · rintro ⟨v, ⟨hv, hh⟩, he⟩
    exact ⟨v, hv, he, hh⟩

theorem card_localBall (s : State) (h : ℕ) :
    (localBall s h).card = (s.vertices.filter fun v => s.height v ≤ h).card := by
  rw [localBall_eq_image]
  exact Finset.card_image_of_injective _ (localRecord_injective s)

theorem ValidAt.height_one_ball {n : ℕ} {s : State} (hs : ValidAt n s) :
    s.vertices.filter (fun v => s.height v ≤ 1) =
      insert 0 (s.vertices.filter fun v => s.graph.Adj 0 v) := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hv, hh⟩
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    · right
      refine ⟨hv, ?_⟩
      have hne : s.height v ≠ 0 := by
        intro he
        rw [hs.height_eq_dist v hv] at he
        exact hv0 ((hs.reachable v hv).dist_eq_zero_iff.mp he).symm
      have he : s.height v = 1 := by omega
      rw [hs.height_eq_dist v hv] at he
      exact s.graph.dist_eq_one_iff_adj.mp he
  · rintro (rfl | ⟨hv, hadj⟩)
    · exact ⟨hs.root_mem, by rw [hs.height_root]; omega⟩
    · exact ⟨hv, by rw [hs.height_eq_dist v hv, s.graph.dist_eq_one_iff_adj.mpr hadj]⟩

theorem ValidAt.card_localBall_one {n : ℕ} {s : State} (hs : ValidAt n s) :
    (localBall s 1).card = rootDegree s + 1 := by
  rw [card_localBall, hs.height_one_ball, Finset.card_insert_of_notMem]
  · rfl
  · simp

theorem ValidAt.localTree_rootDegree {n : ℕ} {s : State} (hs : ValidAt n s) :
    LocalTree.rootDegree (localTreeOfState s) = rootDegree s := by
  simp only [LocalTree.rootDegree, hs.localTreeOfState_balls, hs.card_localBall_one,
    Nat.add_sub_cancel]

theorem localTreeLaw_map_rootDegree (x : SignSequence) (n : ℕ) :
    (localTreeLaw x n).map LocalTree.rootDegree = (treeLaw x n).map rootDegree := by
  rw [localTreeLaw, Measure.map_map LocalTree.continuous_rootDegree.measurable measurable_from_top]
  apply Measure.map_congr
  exact (treeLaw_valid x n).mono fun _ hs => hs.localTree_rootDegree

end Forward
end Freezing1
