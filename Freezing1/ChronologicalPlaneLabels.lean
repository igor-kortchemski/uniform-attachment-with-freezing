module

public import Freezing1.ChronologicalPlaneVertices

/-!
# The genuine labelled plane representative of a chronological tree

The incoming edge label is exactly the actual vertex's birth timestamp;
the vertex label is exactly its frozen/active label. No labels are erased
or replaced by the auxiliary graph IDs used in the generic realization.
-/

@[expose] public section

namespace Freezing1.LocalTree

open Filter
open scoped Topology Classical

noncomputable def toLabelledPlaneTree (T : Tree) : PlaneLabelled.Tree (Option ℕ) ℕ :=
  PlaneLabelled.decorate (toPlaneTree T)
    (fun u => (addressVertex T u).val.frozenAt)
    (fun u => (addressVertex T ⟨u.val, u.property.1⟩).val.birth)

@[simp] theorem shape_toLabelledPlaneTree (T : Tree) :
    PlaneLabelled.shape (toLabelledPlaneTree T) = toPlaneTree T := rfl

theorem follow_none_of_not_present (T : Tree) (u : PlaneTree.Address)
    (hu : ¬PlaneTree.Present (toPlaneTree T) u) : follow T 0 u = none := by
  cases hf : follow T 0 u with
  | none => rfl
  | some b =>
    exfalso
    apply hu
    apply (present_toPlaneTree_iff_follow T u).mpr
    simp only [hf, Option.isSome_some]

theorem vertexSlot_toLabelledPlaneTree (T : Tree) (u : PlaneLabelled.Vertex (toPlaneTree T)) :
    (PlaneLabelled.vertexSlot (toLabelledPlaneTree T) u.val).label =
      some (addressVertex T u).val.frozenAt :=
  PlaneLabelled.vertexSlot_decorate _ _ _ u

theorem edgeSlot_toLabelledPlaneTree (T : Tree) (u : PlaneLabelled.Edge (toPlaneTree T)) :
    (PlaneLabelled.edgeSlot (toLabelledPlaneTree T) u.val).label =
      some (addressVertex T ⟨u.val, u.property.1⟩).val.birth :=
  PlaneLabelled.edgeSlot_decorate _ _ _ u

theorem vertexSlot_toLabelledPlaneTree_label (T : Tree) (u : PlaneTree.Address) :
    (PlaneLabelled.vertexSlot (toLabelledPlaneTree T) u).label =
      (follow T 0 u).bind (fun b => (recordAt T b).map VertexRecord.frozenAt) := by
  by_cases hu : PlaneTree.Present (toPlaneTree T) u
  · rw [vertexSlot_toLabelledPlaneTree T ⟨u, hu⟩, follow_addressVertex T ⟨u, hu⟩,
      Option.bind_some, recordAt_vertex, Option.map_some]
  · have hs := PlaneLabelled.vertexSlot_empty_of_absent (toLabelledPlaneTree T) u
      (by simpa only [shape_toLabelledPlaneTree] using hu)
    rw [hs, follow_none_of_not_present T u hu]
    rfl

theorem edgeSlot_toLabelledPlaneTree_label (T : Tree) (u : PlaneTree.Address) :
    (PlaneLabelled.edgeSlot (toLabelledPlaneTree T) u).label =
      if u = [] then none else follow T 0 u := by
  by_cases hroot : u = []
  · subst u
    rw [PlaneLabelled.root_edgeSlot]
    simp [PlaneLabelled.emptySlot]
  · rw [ite_eq_right hroot]
    by_cases hu : PlaneTree.Present (toPlaneTree T) u
    · rw [edgeSlot_toLabelledPlaneTree T ⟨u, hu, hroot⟩, follow_addressVertex T ⟨u, hu⟩]
    · have hs := PlaneLabelled.edgeSlot_empty_of_absent (toLabelledPlaneTree T) u
        (by simpa only [shape_toLabelledPlaneTree] using hu)
      rw [hs, follow_none_of_not_present T u hu]
      rfl

theorem labelledVertexSlot_eventually_eq {ι : Type*} {l : Filter ι} {S : ι → Tree} {T : Tree}
    (hc : ∀ h, ∀ᶠ i in l, (S i).val h = T.val h) (u : PlaneTree.Address) :
    ∀ᶠ i in l, PlaneLabelled.vertexSlot (toLabelledPlaneTree (S i)) u =
      PlaneLabelled.vertexSlot (toLabelledPlaneTree T) u := by
  cases hf : follow T 0 u with
  | none =>
    filter_upwards [follow_eventually_eq hc 0 u] with i hi
    apply PlaneLabelled.LabelSlot.ext_label
    simp only [vertexSlot_toLabelledPlaneTree_label, hi, hf, Option.bind_none]
  | some b =>
    filter_upwards [follow_eventually_eq hc 0 u, recordAt_eventually_eq hc b] with i hi hr
    apply PlaneLabelled.LabelSlot.ext_label
    simp only [vertexSlot_toLabelledPlaneTree_label, hi, hf, Option.bind_some, hr]

theorem labelledEdgeSlot_eventually_eq {ι : Type*} {l : Filter ι} {S : ι → Tree} {T : Tree}
    (hc : ∀ h, ∀ᶠ i in l, (S i).val h = T.val h) (u : PlaneTree.Address) :
    ∀ᶠ i in l, PlaneLabelled.edgeSlot (toLabelledPlaneTree (S i)) u =
      PlaneLabelled.edgeSlot (toLabelledPlaneTree T) u := by
  filter_upwards [follow_eventually_eq hc 0 u] with i hi
  apply PlaneLabelled.LabelSlot.ext_label
  simp only [edgeSlot_toLabelledPlaneTree_label, hi]

theorem tendsto_toLabelledPlaneTree {ι : Type*} {l : Filter ι} {S : ι → Tree} {T : Tree}
    (hc : Tendsto S l (𝓝 T)) :
    Tendsto (fun i => toLabelledPlaneTree (S i)) l (𝓝 (toLabelledPlaneTree T)) := by
  apply (PlaneLabelled.tendsto_iff_coordinates _ _).mpr
  have hb := (tendsto_iff_balls S T).mp hc
  exact ⟨by simpa only [shape_toLabelledPlaneTree] using tendsto_toPlaneTree hc,
    labelledVertexSlot_eventually_eq hb, labelledEdgeSlot_eventually_eq hb⟩

theorem continuous_toLabelledPlaneTree : Continuous toLabelledPlaneTree := by
  apply continuous_iff_continuousAt.mpr
  intro T
  exact tendsto_toLabelledPlaneTree (S := id) (l := 𝓝 T) tendsto_id

end Freezing1.LocalTree
