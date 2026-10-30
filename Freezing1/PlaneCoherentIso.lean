module

public import Freezing1.PlaneBallIso

/-! Coherent genuine finite-ball isomorphisms give an actual global isomorphism. -/

@[expose] public section

namespace Freezing1.PlaneLabelled

open scoped Classical

variable {V E : Type*} {S T : Tree V E} {h H : ℕ}

def vertexInBall (T : Tree V E) (u : Vertex (shape T)) (h : ℕ) (hu : u.val.length ≤ h) : BallVertex T h :=
  ⟨u.val, (PlaneTree.mem_ball _ _ _).mpr ⟨u.property, hu⟩⟩

def BallIso.symm (e : BallIso S T h) : BallIso T S h where
  toEquiv := e.toEquiv.symm
  root_eq := by
    apply e.toEquiv.injective
    simpa only [Equiv.apply_symm_apply] using e.root_eq.symm
  length_eq u := by
    simpa only [Equiv.apply_symm_apply] using (e.length_eq (e.toEquiv.symm u)).symm
  parent_iff u v := by
    simpa only [Equiv.apply_symm_apply] using
      (e.parent_iff (e.toEquiv.symm u) (e.toEquiv.symm v)).symm
  vertex_labels u := by
    simpa only [Equiv.apply_symm_apply] using (e.vertex_labels (e.toEquiv.symm u)).symm
  edge_labels u := by
    simpa only [Equiv.apply_symm_apply] using (e.edge_labels (e.toEquiv.symm u)).symm

@[simp] theorem BallIso.symm_symm (e : BallIso S T h) : e.symm.symm = e := by
  apply BallIso.ext
  exact Equiv.symm_symm _

theorem BallIso.restrict_symm (e : BallIso S T H) (hh : h ≤ H) :
    (e.restrict hh).symm = e.symm.restrict hh := by
  apply BallIso.ext
  apply Equiv.ext
  intro u
  apply Subtype.ext
  rfl

def CoherentBallIsos (e : ∀ h, BallIso S T h) : Prop :=
  ∀ h, (e (h + 1)).restrict (by omega : h ≤ h + 1) = e h

theorem coherent_restrict (e : ∀ h, BallIso S T h) (he : CoherentBallIsos e)
    {h H : ℕ} (hh : h ≤ H) : (e H).restrict hh = e h := by
  induction H, hh using Nat.le_induction with
  | base => exact BallIso.restrict_self _
  | succ H hH ih =>
    rw [← BallIso.restrict_restrict (e (H + 1)) hH (by omega : H ≤ H + 1), he H, ih]

theorem coherent_symm (e : ∀ h, BallIso S T h) (he : CoherentBallIsos e) :
    CoherentBallIsos (fun h => (e h).symm) := by
  intro h
  rw [← BallIso.restrict_symm, he h]

def coherentMap (e : ∀ h, BallIso S T h) (u : Vertex (shape S)) : Vertex (shape T) :=
  ((e u.val.length).toEquiv (vertexInBall S u u.val.length le_rfl)).vertex

theorem coherentMap_length (e : ∀ h, BallIso S T h) (u : Vertex (shape S)) :
    (coherentMap e u).val.length = u.val.length :=
  (e u.val.length).length_eq (vertexInBall S u u.val.length le_rfl)

theorem coherentMap_eq_at (e : ∀ h, BallIso S T h) (he : CoherentBallIsos e)
    (u : Vertex (shape S)) (H : ℕ) (hu : u.val.length ≤ H) :
    coherentMap e u = ((e H).toEquiv (vertexInBall S u H hu)).vertex := by
  apply Subtype.ext
  have hh := congrArg (fun f : BallIso S T u.val.length =>
    (f.toEquiv (vertexInBall S u u.val.length le_rfl)).val) (coherent_restrict e he hu)
  exact hh.symm

theorem coherentMap_leftInverse (e : ∀ h, BallIso S T h) (he : CoherentBallIsos e) :
    Function.LeftInverse (coherentMap (fun h => (e h).symm)) (coherentMap e) := by
  intro u
  have hlen : (coherentMap e u).val.length ≤ u.val.length := (coherentMap_length e u).le
  rw [coherentMap_eq_at (fun h => (e h).symm) (coherent_symm e he) (coherentMap e u) u.val.length hlen]
  have hb : vertexInBall T (coherentMap e u) u.val.length hlen =
      (e u.val.length).toEquiv (vertexInBall S u u.val.length le_rfl) := Subtype.ext rfl
  change ((e u.val.length).toEquiv.symm (vertexInBall T (coherentMap e u) u.val.length hlen)).vertex = u
  rw [hb, Equiv.symm_apply_apply]
  exact Subtype.ext rfl

noncomputable def coherentIso (e : ∀ h, BallIso S T h) (he : CoherentBallIsos e) : UnorderedIso S T where
  toEquiv :=
    { toFun := coherentMap e
      invFun := coherentMap (fun h => (e h).symm)
      left_inv := coherentMap_leftInverse e he
      right_inv := by
        intro u
        simpa only [BallIso.symm_symm] using
          coherentMap_leftInverse (fun h => (e h).symm) (coherent_symm e he) u }
  root_eq := by
    apply Subtype.ext
    exact congrArg (fun u : BallVertex T 0 => u.val) (e 0).root_eq
  parent_iff u v := by
    let N := max u.val.length v.val.length
    have hu : u.val.length ≤ N := le_max_left _ _
    have hv : v.val.length ≤ N := le_max_right _ _
    change Parent u v ↔ Parent (coherentMap e u) (coherentMap e v)
    rw [coherentMap_eq_at e he u N hu, coherentMap_eq_at e he v N hv]
    exact (e N).parent_iff (vertexInBall S u N hu) (vertexInBall S v N hv)
  vertex_labels u := (e u.val.length).vertex_labels (vertexInBall S u u.val.length le_rfl)
  edge_labels u := (e u.val.length).edge_labels (vertexInBall S u u.val.length le_rfl)

/-- The finite-radius witnesses are genuine isomorphisms, and all of them
can be made compatible before constructing this global witness. -/
theorem nonempty_unorderedIso_of_ball_isos (S T : Tree V E) (hn : ∀ h, Nonempty (BallIso S T h)) :
    Nonempty (UnorderedIso S T) := by
  obtain ⟨e, he⟩ := exists_coherent_ball_isos S T hn
  exact ⟨coherentIso e he⟩

end Freezing1.PlaneLabelled
