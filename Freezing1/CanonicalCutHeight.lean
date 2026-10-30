module

public import Freezing1.CanonicalCutForest
public import Freezing1.RootedForestFiniteDistance

/-!
# Forward cut heights equal the actual reverse phase depths

The parent recursion is stopped exactly at the roots of the cut forest.
Its fuel is the actual terminal depth; induction on that depth proves the
recursion equals the recorded phase depth. Graph isomorphism then certifies
the interpretation as height in the finite forward cut forest.
-/

@[expose] public section

namespace Freezing1.ReverseStampedHistory

open ReverseStamped CanonicalTree
open scoped Classical

theorem cutHeight_eq_stage_depth {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i))
    {i : ℕ} (hi : i ≤ n) {v : ℕ ⊕ ℕ} (hv : v ∈ (stage H i).forest.vertices) :
    Forward.cutHeight (reverseState H.current) i (H.current.edgeTime v) =
      (stage H i).forest.depth v := by
  have hcuts := (stage_eq_terminal_cuts hd hs i hi).1
  have hzero := hd 0 (Nat.zero_le _)
  have hinj := current_times_injective hd
  have hrec : ∀ m : ℕ, ∀ w ∈ (stage H i).forest.vertices,
      H.current.forest.depth w = m →
      Forward.cutHeightAux (reverseState H.current) i m (H.current.edgeTime w) =
        (stage H i).forest.depth w := by
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
        rw [(stage H i).forest.depth_eq_zero_iff hw |>.mpr hr]
        exact Forward.cutHeightAux_eq_zero_of_le _ i m _ hwi
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
        have hnrI : w ≠ (stage H i).forest.root w := by
          intro he
          have hp' := (stage H i).forest.parent_of_root (RootedForest.mem_roots.mpr ⟨hw, he.symm⟩)
          exact H.current.forest.parent_ne hw0 hnr (hp.symm.trans hp')
        have hdepth := H.current.forest.depth_parent w hw0 hnr
        have hdepthI := (stage H i).forest.depth_parent w hw hnrI
        have hsm : H.current.forest.depth (H.current.forest.parent w) < m := by omega
        have ihp := ih _ hsm _ hpI rfl
        have hparent := (reverseState_vertex_data hinj hw0).1
        calc
          _ = Forward.cutHeightAux (reverseState H.current) i
              (H.current.forest.depth (H.current.forest.parent w) + 1) (H.current.edgeTime w) := by
            rw [hdepth, hm]
          _ = Forward.cutHeightAux (reverseState H.current) i
              (H.current.forest.depth (H.current.forest.parent w))
              ((reverseState H.current).parent (H.current.edgeTime w)) + 1 := by
            simp only [Forward.cutHeightAux, ite_eq_right hwi]
          _ = (stage H i).forest.depth (H.current.forest.parent w) + 1 := by rw [hparent, ihp]
          _ = (stage H i).forest.depth w := by simpa only [hp] using hdepthI
  unfold Forward.cutHeight
  rw [(reverseState_vertex_data hinj (phase_vertices_subset_current hd hi hv)).2.1]
  exact hrec _ v hv rfl

set_option backward.isDefEq.respectTransparency false in
/-- Graph isomorphisms preserve the shortest-path distance on connected pairs. -/
theorem graphIso_dist_eq_of_reachable {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}
    (e : G ≃g K) {u v : V} (hr : G.Reachable u v) :
    G.dist u v = K.dist (e u) (e v) := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := (hr.map e.toHom).exists_walk_length_eq_dist
  change q.length = K.dist (e u) (e v) at hq
  apply le_antisymm
  · have h := G.dist_le (q.map e.symm.toHom)
    change G.dist (e.symm (e u)) (e.symm (e v)) ≤ (q.map e.symm.toHom).length at h
    rw [SimpleGraph.Walk.length_map, hq] at h
    simpa only [e.symm_apply_apply] using h
  · have h := K.dist_le (p.map e.toHom)
    change K.dist (e u) (e v) ≤ (p.map e.toHom).length at h
    rw [SimpleGraph.Walk.length_map, hp] at h
    exact h

/-- The computed forward cut height is exactly distance from the image of
the component root in the finite cut graph. -/
theorem cutHeight_eq_cutGraph_dist {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i))
    (ho : TimestampOrder H.current) {i : ℕ} (hi : i ≤ n)
    {v : ℕ ⊕ ℕ} (hv : v ∈ (stage H i).forest.vertices) :
    Forward.cutHeight (reverseState H.current) i (H.current.edgeTime v) =
      ((Forward.cutGraph (reverseState H.current) i).induce
        (Forward.cutVertices (reverseState H.current) i : Set ℕ)).dist
          (cutGraphIso hd hs ho hi ⟨(stage H i).forest.root v, (stage H i).forest.root_mem v hv⟩)
          (cutGraphIso hd hs ho hi ⟨v, hv⟩) := by
  rw [cutHeight_eq_stage_depth hd hs hi hv, (stage H i).forest.depth_eq_tree_dist hv]
  apply graphIso_dist_eq_of_reachable
  obtain ⟨p, _⟩ := (stage H i).forest.exists_root_walk hv
  exact ⟨p.induce ((stage H i).forest.vertices : Set (ℕ ⊕ ℕ))
    ((stage H i).forest.walk_support_mem p ((stage H i).forest.root_mem v hv))⟩

end Freezing1.ReverseStampedHistory
