module

public import Freezing1.ChronologicalBallRecords

/-! On chronological support, genuine unordered labelled balls and the raw
chronological record balls have exactly the same equality relation at each radius. -/

@[expose] public section

namespace Freezing1.LocalTree

open scoped Classical

noncomputable def ballIsoOfRawBallEq {T U : Tree} {h : ℕ} (hh : T.val h = U.val h) :
    PlaneLabelled.BallIso (toLabelledPlaneTree T) (toLabelledPlaneTree U) h := by
  let r : {r : VertexRecord // r ∈ T.val h} ≃ {r : VertexRecord // r ∈ U.val h} :=
    { toFun r := ⟨r.val, by rw [← hh]; exact r.property⟩
      invFun r := ⟨r.val, by rw [hh]; exact r.property⟩
      left_inv _ := Subtype.ext rfl
      right_inv _ := Subtype.ext rfl }
  let f := (chronologicalBallVertexEquiv T h).trans
    (r.trans (chronologicalBallVertexEquiv U h).symm)
  have hrec (u : PlaneLabelled.BallVertex (toLabelledPlaneTree T) h) :
      (ballRecord T h u).val = (ballRecord U h (f u)).val := by
    exact (congrArg Subtype.val ((chronologicalBallVertexEquiv U h).apply_symm_apply
      (r ((chronologicalBallVertexEquiv T h) u)))).symm
  have hlen (u : PlaneLabelled.BallVertex (toLabelledPlaneTree T) h) :
      (f u).val.length = u.val.length := by
    change (ballAddress U h (f u)).val.length = (ballAddress T h u).val.length
    rw [← addressVertex_height U (ballAddress U h (f u)),
      ← addressVertex_height T (ballAddress T h u)]
    exact congrArg VertexRecord.height (hrec u).symm
  refine
    { toEquiv := f
      root_eq := ?_
      length_eq := hlen
      parent_iff := ?_
      vertex_labels := ?_
      edge_labels := ?_ }
  · apply Subtype.ext
    apply List.length_eq_zero_iff.mp
    exact hlen (PlaneLabelled.rootBall (toLabelledPlaneTree T) h)
  · intro u v
    change PlaneLabelled.Parent (ballAddress T h u) (ballAddress T h v) ↔
      PlaneLabelled.Parent (ballAddress U h (f u)) (ballAddress U h (f v))
    rw [addressVertex_parent_iff, addressVertex_parent_iff]
    change ((ballRecord T h v).val.birth ≠ 0 ∧
      (ballRecord T h v).val.parent = (ballRecord T h u).val.birth) ↔
      ((ballRecord U h (f v)).val.birth ≠ 0 ∧
        (ballRecord U h (f v)).val.parent = (ballRecord U h (f u)).val.birth)
    rw [← hrec u, ← hrec v]
  · intro u
    apply PlaneLabelled.LabelSlot.ext_label
    rw [vertexSlot_toLabelledPlaneTree T ⟨u.val, u.vertex.property⟩,
      vertexSlot_toLabelledPlaneTree U ⟨(f u).val, (f u).vertex.property⟩]
    exact congrArg (fun r : VertexRecord => some r.frozenAt) (hrec u)
  · intro u
    apply PlaneLabelled.LabelSlot.ext_label
    by_cases hu : u.val = []
    · have hf : (f u).val = [] := by
        apply List.length_eq_zero_iff.mp
        rw [hlen, hu]
        rfl
      rw [hu, hf, PlaneLabelled.root_edgeSlot, PlaneLabelled.root_edgeSlot]
    · have hf : (f u).val ≠ [] := by
        intro hf
        apply hu
        apply List.length_eq_zero_iff.mp
        rw [← hlen, hf]
        rfl
      rw [edgeSlot_toLabelledPlaneTree T ⟨u.val, u.vertex.property, hu⟩,
        edgeSlot_toLabelledPlaneTree U ⟨(f u).val, (f u).vertex.property, hf⟩]
      exact congrArg (fun r : VertexRecord => some r.birth) (hrec u)

theorem nonempty_ballIso_iff_rawBall_eq (T U : Tree) (h : ℕ) :
    Nonempty (PlaneLabelled.BallIso (toLabelledPlaneTree T) (toLabelledPlaneTree U) h) ↔
      T.val h = U.val h := by
  constructor
  · rintro ⟨e⟩
    exact rawBall_eq_of_ballIso e
  · intro hh
    exact ⟨ballIsoOfRawBallEq hh⟩

noncomputable def toUnordered (T : Tree) : UnorderedLocal.Tree :=
  UnorderedLocal.ofPlane (toLabelledPlaneTree T)

theorem finiteBall_toUnordered_eq_iff (T U : Tree) (h : ℕ) :
    UnorderedLocal.finiteBall (toUnordered T) h = UnorderedLocal.finiteBall (toUnordered U) h ↔
      T.val h = U.val h :=
  (UnorderedLocal.finiteBall_ofPlane_eq_iff_ballIso _ _ h).trans
    (nonempty_ballIso_iff_rawBall_eq T U h)

end Freezing1.LocalTree
