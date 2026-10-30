module

public import Freezing1.PlaneCoherentIso

/-! Restrict actual global isomorphisms and extend bounded finite-ball witnesses. -/

@[expose] public section

namespace Freezing1.PlaneLabelled

open scoped Classical

variable {V E : Type*} {R S T : Tree V E} {h : ℕ}

def ballVertexEquiv (T : Tree V E) (h : ℕ) :
    BallVertex T h ≃ {u : Vertex (shape T) // u.val.length ≤ h} where
  toFun u := ⟨u.vertex, u.length_le⟩
  invFun u := vertexInBall T u.val h u.property
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

noncomputable def UnorderedIso.toBallIso (e : UnorderedIso S T) (h : ℕ) : BallIso S T h where
  toEquiv := (ballVertexEquiv S h).trans
    ((Equiv.subtypeEquiv e.toEquiv (fun u => by rw [e.length_eq u])).trans
      (ballVertexEquiv T h).symm)
  root_eq := by
    apply Subtype.ext
    exact congrArg (fun u : Vertex (shape T) => u.val) e.root_eq
  length_eq u := e.length_eq u.vertex
  parent_iff u v := e.parent_iff u.vertex v.vertex
  vertex_labels u := e.vertex_labels u.vertex
  edge_labels u := e.edge_labels u.vertex

def BallIso.trans (e : BallIso R S h) (f : BallIso S T h) : BallIso R T h where
  toEquiv := e.toEquiv.trans f.toEquiv
  root_eq := by simp only [Equiv.trans_apply, e.root_eq, f.root_eq]
  length_eq u := (f.length_eq (e.toEquiv u)).trans (e.length_eq u)
  parent_iff u v := (e.parent_iff u v).trans (f.parent_iff (e.toEquiv u) (e.toEquiv v))
  vertex_labels u := (e.vertex_labels u).trans (f.vertex_labels (e.toEquiv u))
  edge_labels u := (e.edge_labels u).trans (f.edge_labels (e.toEquiv u))

noncomputable def BallIso.of_ball_eq (S T : Tree V E) (h : ℕ) (hh : ball S h = ball T h) :
    BallIso S T h := by
  have ha : PlaneTree.ball (shape S) h = PlaneTree.ball (shape T) h := by
    simpa only [addresses_ball] using congrArg (Finset.image Prod.fst) hh
  have hd (u : BallVertex S h) :
      vertexSlot S u.val = vertexSlot T u.val ∧ edgeSlot S u.val = edgeSlot T u.val := by
    have hm : (u.val, vertexSlot S u.val, edgeSlot S u.val) ∈ ball S h :=
      (mem_ball _ _ _ _ _).mpr ⟨u.vertex.property, u.length_le, rfl, rfl⟩
    rw [hh] at hm
    have hp := (mem_ball _ _ _ _ _).mp hm |>.2.2
    exact ⟨hp.1.symm, hp.2.symm⟩
  let f : BallVertex S h ≃ BallVertex T h :=
    Equiv.subtypeEquiv (Equiv.refl PlaneTree.Address) (fun u => by
      change u ∈ PlaneTree.ball (shape S) h ↔ u ∈ PlaneTree.ball (shape T) h
      rw [ha])
  exact
    { toEquiv := f
      root_eq := Subtype.ext rfl
      length_eq _ := rfl
      parent_iff _ _ := Iff.rfl
      vertex_labels u := (hd u).1
      edge_labels u := (hd u).2 }

def fullBallEquiv (T : Tree V E) (h : ℕ) (hb : ∀ u : Vertex (shape T), u.val.length ≤ h) :
    Vertex (shape T) ≃ BallVertex T h where
  toFun u := vertexInBall T u h (hb u)
  invFun u := u.vertex
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

noncomputable def BallIso.toUnorderedIso (e : BallIso S T h)
    (hS : ∀ u : Vertex (shape S), u.val.length ≤ h)
    (hT : ∀ u : Vertex (shape T), u.val.length ≤ h) : UnorderedIso S T where
  toEquiv := (fullBallEquiv S h hS).trans (e.toEquiv.trans (fullBallEquiv T h hT).symm)
  root_eq := by
    apply Subtype.ext
    exact congrArg (fun u : BallVertex T h => u.val) e.root_eq
  parent_iff u v := e.parent_iff (vertexInBall S u h (hS u)) (vertexInBall S v h (hS v))
  vertex_labels u := e.vertex_labels (vertexInBall S u h (hS u))
  edge_labels u := e.edge_labels (vertexInBall S u h (hS u))

theorem nonempty_unorderedIso_of_ball_eq_of_bounded (S T : Tree V E) (h : ℕ)
    (hS : ∀ u : Vertex (shape S), u.val.length ≤ h)
    (hT : ∀ u : Vertex (shape T), u.val.length ≤ h)
    (hh : ball S h = ball T h) : Nonempty (UnorderedIso S T) :=
  ⟨(BallIso.of_ball_eq S T h hh).toUnorderedIso hS hT⟩

end Freezing1.PlaneLabelled
