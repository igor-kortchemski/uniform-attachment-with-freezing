module

public import Freezing1.ChronologicalPlaneVertexEquiv
public import Freezing1.ChronologicalPlaneLabels
public import Freezing1.UnorderedTreeProjection

/-! Chronological records recover root, height and parents from genuine labelled vertices. -/

@[expose] public section

namespace Freezing1.PlaneLabelled

variable {V E : Type*} {T : Tree V E} {h : ℕ}

def BallVertex.parent (u : BallVertex T h) (_hu : u.val ≠ []) : BallVertex T h :=
  ⟨u.val.dropLast, (PlaneTree.mem_ball _ _ _).mpr
    ⟨PlaneTree.present_of_prefix u.val.dropLast_prefix u.vertex.property,
      by have hh := u.length_le; simp only [List.length_dropLast]; omega⟩⟩

theorem BallVertex.parent_rel (u : BallVertex T h) (hu : u.val ≠ []) :
    Parent (u.parent hu).vertex u.vertex := ⟨hu, rfl⟩

def parentVertex (u : Vertex (shape T)) (_hu : u.val ≠ []) : Vertex (shape T) :=
  ⟨u.val.dropLast, PlaneTree.present_of_prefix u.val.dropLast_prefix u.property⟩

theorem parentVertex_rel (u : Vertex (shape T)) (hu : u.val ≠ []) :
    Parent (parentVertex u hu) u := ⟨hu, rfl⟩

end Freezing1.PlaneLabelled

namespace Freezing1.LocalTree

open scoped Classical

theorem vertex_parent_zero_of_birth_zero (T : Tree) (v : Vertex T) (hv : v.val.birth = 0) :
    v.val.parent = 0 := by
  obtain ⟨h, hh⟩ := v.property
  exact ((T.property h).1.root_data v.val hh hv).1

theorem addressVertex_birth_zero_iff (T : Tree) (u : PlaneLabelled.Vertex (toPlaneTree T)) :
    (addressVertex T u).val.birth = 0 ↔ u.val = [] := by
  constructor
  · intro hb
    have hh := vertex_height_le_birth T (addressVertex T u)
    rw [addressVertex_height] at hh
    apply List.length_eq_zero_iff.mp
    omega
  · intro hu
    have hf := follow_addressVertex T u
    rw [hu, follow] at hf
    exact (Option.some.inj hf).symm

theorem addressVertex_parent (T : Tree)
    (u v : PlaneLabelled.Vertex (toPlaneTree T)) (hp : PlaneLabelled.Parent u v) :
    (addressVertex T v).val.birth ≠ 0 ∧
      (addressVertex T v).val.parent = (addressVertex T u).val.birth := by
  obtain ⟨p, j, hv⟩ := PlaneTree.exists_append_singleton_of_ne_nil v.val hp.1
  have hu : p = u.val := by simpa only [hv, List.dropLast_concat] using hp.2
  have hf := follow_addressVertex T v
  rw [hv] at hf
  obtain ⟨b, hb, _, hi⟩ := (follow_append_singleton_eq_some_iff T 0 p j _).mp hf
  rw [hu] at hb
  have hbirth : b = (addressVertex T u).val.birth :=
    Option.some.inj (hb.symm.trans (follow_addressVertex T u))
  apply (mem_childList_iff T (addressVertex T u) (addressVertex T v)).mp
  rw [← hbirth]
  exact List.mem_of_getElem? hi

theorem addressVertex_parent_iff (T : Tree)
    (u v : PlaneLabelled.Vertex (toPlaneTree T)) :
    PlaneLabelled.Parent u v ↔
      (addressVertex T v).val.birth ≠ 0 ∧
        (addressVertex T v).val.parent = (addressVertex T u).val.birth := by
  constructor
  · exact addressVertex_parent T u v
  · rintro ⟨hv, hp⟩
    have hv' : v.val ≠ [] := by
      intro hh
      exact hv ((addressVertex_birth_zero_iff T v).mpr hh)
    let p : PlaneLabelled.Vertex (toPlaneTree T) :=
      ⟨v.val.dropLast, PlaneTree.present_of_prefix v.val.dropLast_prefix v.property⟩
    have hparent : PlaneLabelled.Parent p v := ⟨hv', rfl⟩
    have hbirth := (addressVertex_parent T p v hparent).2
    have heq : addressVertex T p = addressVertex T u :=
      vertex_birth_injective T (hbirth.symm.trans hp)
    have hpu : p = u := addressVertex_injective T heq
    exact hpu ▸ hparent

theorem VertexRecord.ext_fields {r s : VertexRecord}
    (hb : r.birth = s.birth) (hp : r.parent = s.parent) (hh : r.height = s.height)
    (hf : r.frozenAt = s.frozenAt) : r = s := by
  cases r
  cases s
  cases hb
  cases hp
  cases hh
  cases hf
  rfl

end Freezing1.LocalTree
