module

public import Freezing1.CanonicalCutHeight
public import Freezing1.ForwardComponentPopulation
public import Freezing1.RootedForestCoalescence

/-!
# Cut ancestors are the actual graph-component roots

The forward parent recursion returns the canonical ID of the root of the
corresponding reverse phase forest. Equality of these IDs therefore means
membership in the same actual graph component, under the verified cut-graph
isomorphism. This supplies the geometric meaning of the population observable.
-/

@[expose] public section

namespace Freezing1.ReverseStampedHistory

open ReverseStamped CanonicalTree
open scoped Classical

theorem cutAncestor_eq_stage_root {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i))
    {i : ℕ} (hi : i ≤ n) {v : ℕ ⊕ ℕ} (hv : v ∈ (stage H i).forest.vertices) :
    Forward.cutAncestor (reverseState H.current) i (H.current.edgeTime v) =
      H.current.edgeTime ((stage H i).forest.root v) := by
  have hcuts := (stage_eq_terminal_cuts hd hs i hi).1
  have hzero := hd 0 (Nat.zero_le _)
  have hinj := current_times_injective hd
  have hrec : ∀ m : ℕ, ∀ w ∈ (stage H i).forest.vertices,
      H.current.forest.depth w = m →
      Forward.cutAncestorAux (reverseState H.current) i m (H.current.edgeTime w) =
        H.current.edgeTime ((stage H i).forest.root w) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro w hw hm
      have hw0 := phase_vertices_subset_current hd hi hw
      have hpw := congrFun hcuts w
      by_cases hwi : H.current.edgeTime w ≤ i
      · have hp : (stage H i).forest.parent w = w := by
          simpa only [parentCut, ite_eq_right (Nat.not_lt.mpr hwi)] using hpw
        have hr : (stage H i).forest.root w = w := by
          by_contra hr
          exact (stage H i).forest.parent_ne hw (Ne.symm hr) hp
        rw [hr]
        exact Forward.cutAncestorAux_of_le _ i m _ hwi
      · have hlt : i < H.current.edgeTime w := Nat.lt_of_not_ge hwi
        have hnr : w ≠ H.current.forest.root w := by
          intro he
          have hz := (hzero.times.root_zero w hw0).mpr (RootedForest.mem_roots.mpr ⟨hw0, he.symm⟩)
          change H.current.edgeTime w = 0 at hz
          omega
        have hp : (stage H i).forest.parent w = H.current.forest.parent w := by
          simpa only [parentCut, ite_eq_left hlt] using hpw
        have hpI : H.current.forest.parent w ∈ (stage H i).forest.vertices :=
          hp ▸ (stage H i).forest.parent_mem w hw
        have hdepth := H.current.forest.depth_parent w hw0 hnr
        have hsm : H.current.forest.depth (H.current.forest.parent w) < m := by omega
        have ihp := ih _ hsm _ hpI rfl
        have hparent := (reverseState_vertex_data hinj hw0).1
        calc
          _ = Forward.cutAncestorAux (reverseState H.current) i
              (H.current.forest.depth (H.current.forest.parent w) + 1) (H.current.edgeTime w) := by
            rw [hdepth, hm]
          _ = Forward.cutAncestorAux (reverseState H.current) i
              (H.current.forest.depth (H.current.forest.parent w))
              ((reverseState H.current).parent (H.current.edgeTime w)) := by
            simp only [Forward.cutAncestorAux, ite_eq_right hwi]
          _ = H.current.edgeTime ((stage H i).forest.root (H.current.forest.parent w)) := by
            rw [hparent, ihp]
          _ = H.current.edgeTime ((stage H i).forest.root w) := by
            rw [← hp, (stage H i).forest.root_parent w hw]
  unfold Forward.cutAncestor
  rw [(reverseState_vertex_data hinj (phase_vertices_subset_current hd hi hv)).2.1]
  exact hrec _ v hv rfl

/-- Two surviving vertices have the same computed cut ancestor exactly when
they are connected in the actual phase forest, hence in its canonical cut graph. -/
theorem cutAncestor_eq_iff_stage_reachable {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i))
    {i : ℕ} (hi : i ≤ n) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ (stage H i).forest.vertices) (hv : v ∈ (stage H i).forest.vertices) :
    Forward.cutAncestor (reverseState H.current) i (H.current.edgeTime u) =
        Forward.cutAncestor (reverseState H.current) i (H.current.edgeTime v) ↔
      (stage H i).forest.graph.Reachable u v := by
  rw [cutAncestor_eq_stage_root hd hs hi hu, cutAncestor_eq_stage_root hd hs hi hv,
    ← (stage H i).forest.root_eq_iff_reachable hu hv]
  constructor
  · exact current_times_injective hd _
      (phase_vertices_subset_current hd hi ((stage H i).forest.root_mem u hu)) _
      (phase_vertices_subset_current hd hi ((stage H i).forest.root_mem v hv))
  · exact congrArg H.current.edgeTime

end Freezing1.ReverseStampedHistory
