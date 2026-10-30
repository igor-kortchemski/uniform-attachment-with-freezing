module

public import Freezing1.ChronologicalPlaneGeometry

/-! Genuine labelled ball isomorphisms preserve all chronological records,
including the parent and height fields, which are redundant on this support. -/

@[expose] public section

namespace Freezing1.LocalTree

open scoped Classical

def ballAddress (T : Tree) (h : ℕ)
    (u : PlaneLabelled.BallVertex (toLabelledPlaneTree T) h) :
    PlaneLabelled.Vertex (toPlaneTree T) := ⟨u.val, u.vertex.property⟩

noncomputable def ballRecord (T : Tree) (h : ℕ)
    (u : PlaneLabelled.BallVertex (toLabelledPlaneTree T) h) :
    {r : VertexRecord // r ∈ T.val h} :=
  ⟨(addressVertex T (ballAddress T h u)).val, (vertex_mem_ball_iff T _ h).mpr
    (by rw [addressVertex_height]; exact u.length_le)⟩

theorem ballRecord_injective (T : Tree) (h : ℕ) :
    Function.Injective (ballRecord T h) := by
  intro u v huv
  have hr : (addressVertex T (ballAddress T h u)).val =
      (addressVertex T (ballAddress T h v)).val :=
    congrArg (fun r : {r : VertexRecord // r ∈ T.val h} => r.val) huv
  have he : addressVertex T (ballAddress T h u) = addressVertex T (ballAddress T h v) :=
    Subtype.ext hr
  apply Subtype.ext
  exact congrArg (fun v : PlaneLabelled.Vertex (toPlaneTree T) => v.val)
    (addressVertex_injective T he)

theorem ballRecord_surjective (T : Tree) (h : ℕ) :
    Function.Surjective (ballRecord T h) := by
  intro r
  let v : Vertex T := ⟨r.val, ⟨h, r.property⟩⟩
  obtain ⟨u, hu⟩ := addressVertex_surjective T v
  have hh : u.val.length ≤ h := by
    rw [← addressVertex_height T u, hu]
    exact (vertex_mem_ball_iff T v h).mp r.property
  refine ⟨PlaneLabelled.vertexInBall (toLabelledPlaneTree T) u h hh, ?_⟩
  apply Subtype.ext
  change (addressVertex T u).val = r.val
  exact congrArg (fun v : Vertex T => v.val) hu

noncomputable def chronologicalBallVertexEquiv (T : Tree) (h : ℕ) :
    PlaneLabelled.BallVertex (toLabelledPlaneTree T) h ≃ {r : VertexRecord // r ∈ T.val h} :=
  Equiv.ofBijective (ballRecord T h) ⟨ballRecord_injective T h, ballRecord_surjective T h⟩

theorem ballIso_birth {T U : Tree} {h : ℕ}
    (e : PlaneLabelled.BallIso (toLabelledPlaneTree T) (toLabelledPlaneTree U) h)
    (u : PlaneLabelled.BallVertex (toLabelledPlaneTree T) h) :
    (ballRecord T h u).val.birth = (ballRecord U h (e.toEquiv u)).val.birth := by
  by_cases hu : u.val = []
  · have ht : (e.toEquiv u).val = [] := by
      apply List.length_eq_zero_iff.mp
      rw [e.length_eq, hu]
      rfl
    exact (addressVertex_birth_zero_iff T (ballAddress T h u)).mpr hu |>.trans
      ((addressVertex_birth_zero_iff U (ballAddress U h (e.toEquiv u))).mpr ht).symm
  · have ht : (e.toEquiv u).val ≠ [] := by
      intro he
      apply hu
      apply List.length_eq_zero_iff.mp
      rw [← e.length_eq, he]
      rfl
    have he := congrArg PlaneLabelled.LabelSlot.label (e.edge_labels u)
    rw [edgeSlot_toLabelledPlaneTree T ⟨u.val, u.vertex.property, hu⟩,
      edgeSlot_toLabelledPlaneTree U
        ⟨(e.toEquiv u).val, (e.toEquiv u).vertex.property, ht⟩] at he
    exact Option.some.inj he

theorem ballIso_frozenAt {T U : Tree} {h : ℕ}
    (e : PlaneLabelled.BallIso (toLabelledPlaneTree T) (toLabelledPlaneTree U) h)
    (u : PlaneLabelled.BallVertex (toLabelledPlaneTree T) h) :
    (ballRecord T h u).val.frozenAt = (ballRecord U h (e.toEquiv u)).val.frozenAt := by
  have he := congrArg PlaneLabelled.LabelSlot.label (e.vertex_labels u)
  rw [vertexSlot_toLabelledPlaneTree T ⟨u.val, u.vertex.property⟩,
    vertexSlot_toLabelledPlaneTree U ⟨(e.toEquiv u).val, (e.toEquiv u).vertex.property⟩] at he
  exact Option.some.inj he

theorem ballIso_record {T U : Tree} {h : ℕ}
    (e : PlaneLabelled.BallIso (toLabelledPlaneTree T) (toLabelledPlaneTree U) h)
    (u : PlaneLabelled.BallVertex (toLabelledPlaneTree T) h) :
    (ballRecord T h u).val = (ballRecord U h (e.toEquiv u)).val := by
  apply VertexRecord.ext_fields
  · exact ballIso_birth e u
  · by_cases hu : u.val = []
    · have hb := (addressVertex_birth_zero_iff T (ballAddress T h u)).mpr hu
      have hb' : (addressVertex U (ballAddress U h (e.toEquiv u))).val.birth = 0 :=
        (ballIso_birth e u).symm.trans hb
      exact (vertex_parent_zero_of_birth_zero T _ hb).trans
        (vertex_parent_zero_of_birth_zero U _ hb').symm
    · have hs := addressVertex_parent T (ballAddress T h (u.parent hu))
        (ballAddress T h u) (u.parent_rel hu)
      have ht := addressVertex_parent U (ballAddress U h (e.toEquiv (u.parent hu)))
        (ballAddress U h (e.toEquiv u)) ((e.parent_iff _ _).mp (u.parent_rel hu))
      exact hs.2.trans ((ballIso_birth e (u.parent hu)).trans ht.2.symm)
  · change (addressVertex T (ballAddress T h u)).val.height =
      (addressVertex U (ballAddress U h (e.toEquiv u))).val.height
    rw [addressVertex_height, addressVertex_height]
    exact (e.length_eq u).symm
  · exact ballIso_frozenAt e u

theorem rawBall_subset_of_ballIso {T U : Tree} {h : ℕ}
    (e : PlaneLabelled.BallIso (toLabelledPlaneTree T) (toLabelledPlaneTree U) h) :
    T.val h ⊆ U.val h := by
  intro r hr
  let u := (chronologicalBallVertexEquiv T h).symm ⟨r, hr⟩
  have hu : (ballRecord T h u).val = r :=
    congrArg Subtype.val ((chronologicalBallVertexEquiv T h).apply_symm_apply ⟨r, hr⟩)
  rw [← hu, ballIso_record e u]
  exact (ballRecord U h (e.toEquiv u)).property

theorem rawBall_eq_of_ballIso {T U : Tree} {h : ℕ}
    (e : PlaneLabelled.BallIso (toLabelledPlaneTree T) (toLabelledPlaneTree U) h) :
    T.val h = U.val h :=
  Finset.Subset.antisymm (rawBall_subset_of_ballIso e) (rawBall_subset_of_ballIso e.symm)

end Freezing1.LocalTree
