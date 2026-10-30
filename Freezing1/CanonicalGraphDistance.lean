module

public import Freezing1.ConstructionEquivalence

/-!
# Graph distances in canonical coordinates

The two explicit graph homomorphisms preserve walks in both directions on
the actual finite vertex set. Connected distances are therefore unchanged
by replacing reverse labels with incoming-edge timestamps.
-/

@[expose] public section

namespace Freezing1.CanonicalTree

open scoped Classical

noncomputable def reverseVertex (F : ReverseStamped.Forest) (t : ℕ) : ℕ ⊕ ℕ :=
  if ht : t ∈ (reverse F).vertices then vertexOfId F t ht else .inl 0

theorem reverseVertex_edgeTime {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices) :
    reverseVertex F (F.edgeTime v) = v := by
  have ht : F.edgeTime v ∈ (reverse F).vertices := Finset.mem_image_of_mem _ hv
  simp only [reverseVertex, dite_eq_left ht, vertexOfId_eq hinj hv]

noncomputable def reverseGraphForward (F : ReverseStamped.Forest)
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) : F.forest.graph →g (reverseState F).graph where
  toFun := F.edgeTime
  map_rel' := by
    intro u v huv
    exact (reverse_adj_iff hinj huv.1 huv.2.1).mpr huv

noncomputable def reverseGraphBackward (F : ReverseStamped.Forest)
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) : (reverseState F).graph →g F.forest.graph where
  toFun := reverseVertex F
  map_rel' := by
    intro u v huv
    obtain ⟨_, a, ha, b, hb, rfl, rfl, hab⟩ := huv
    simpa only [reverseVertex_edgeTime hinj ha, reverseVertex_edgeTime hinj hb] using hab

theorem reverseState_graph_dist {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.forest.vertices) (hv : v ∈ F.forest.vertices)
    (hr : F.forest.graph.Reachable u v) :
    (reverseState F).graph.dist (F.edgeTime u) (F.edgeTime v) = F.forest.graph.dist u v := by
  let f := reverseGraphForward F hinj
  let g := reverseGraphBackward F hinj
  have hf : ∀ w, f w = F.edgeTime w := fun _ => rfl
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    have he := (reverseState F).graph.dist_le (p.map f)
    simpa only [SimpleGraph.Walk.length_map, hp, hf] using he
  · obtain ⟨p, hp⟩ := (hr.map f).exists_walk_length_eq_dist
    have he := F.forest.graph.dist_le (p.map g)
    have hu' : g (f u) = u := reverseVertex_edgeTime hinj hu
    have hv' : g (f v) = v := reverseVertex_edgeTime hinj hv
    rw [SimpleGraph.Walk.length_map, hp, hu', hv', hf, hf] at he
    exact he

end Freezing1.CanonicalTree
