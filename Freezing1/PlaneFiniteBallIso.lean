module

public import Freezing1.PlaneCoherentIso
public import Freezing1.PlaneFiniteRootedCorrectness
public import Freezing1.RootedPlaneHeightBound
public import Freezing1.RootedUnorderedGraphIso

/-!
# Equal finite unordered classes give actual finite-ball isomorphisms

The finite source quotient is connected to real vertex/parent/label maps
by the independent finite isomorphism theorem. Compactness then supplies
an actual global rooted labelled isomorphism, with no convergence premise.
-/

@[expose] public section

namespace Freezing1.PlaneLabelled

open BinaryBijection
open scoped Classical

def finiteRootedVertexEquiv (T : Tree (Option ℕ) ℕ) (h : ℕ) :
    Vertex (shape (finiteRooted T h).toPlaneLabelled) ≃ BallVertex T h where
  toFun u := by
    have hp : PlaneTree.Present (finiteRooted T h).toPlaneTree u.val := u.property
    have hu := Rooted.present_length_of_fits (finiteRooted T h) h
      (finiteRooted_truncate T h h le_rfl) u.val hp
    exact ⟨u.val, (PlaneTree.mem_ball _ _ _).mpr
      ⟨(present_finiteRooted T h u.val hu).mp hp, hu⟩⟩
  invFun u := ⟨u.val, (present_finiteRooted T h u.val u.length_le).mpr u.vertex.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem nonempty_ballIso_of_finiteRooted_eq (S T : Tree (Option ℕ) ℕ) (h : ℕ)
    (hh : UnorderedLocal.ofRooted (finiteRooted S h) = UnorderedLocal.ofRooted (finiteRooted T h)) :
    Nonempty (BallIso S T h) := by
  have he := (UnorderedLocal.ofRooted_eq_iff _ _).mp hh
  obtain ⟨e⟩ := he.nonempty_unorderedIso
  let a := finiteRootedVertexEquiv S h
  let b := finiteRootedVertexEquiv T h
  let f := a.symm.trans (e.toEquiv.trans b)
  refine ⟨{ toEquiv := f
            root_eq := ?_
            length_eq := ?_
            parent_iff := ?_
            vertex_labels := ?_
            edge_labels := ?_ }⟩
  · apply Subtype.ext
    exact congrArg (fun u : Vertex (shape (finiteRooted T h).toPlaneLabelled) => u.val) e.root_eq
  · intro u
    exact e.length_eq (a.symm u)
  · intro u v
    exact e.parent_iff (a.symm u) (a.symm v)
  · intro u
    have hl := e.vertex_labels (a.symm u)
    change (finiteRooted S h).vertexCode u.val = (finiteRooted T h).vertexCode (f u).val at hl
    rw [vertexCode_finiteRooted S h u.val u.length_le,
      vertexCode_finiteRooted T h (f u).val (f u).length_le] at hl
    exact hl
  · intro u
    have hl := e.edge_labels (a.symm u)
    change (finiteRooted S h).edgeCode u.val = (finiteRooted T h).edgeCode (f u).val at hl
    rw [edgeCode_finiteRooted S h u.val u.length_le,
      edgeCode_finiteRooted T h (f u).val (f u).length_le] at hl
    exact hl

theorem nonempty_ballIso_of_tower_eq (S T : Tree (Option ℕ) ℕ)
    (hh : toBallTower S = toBallTower T) (h : ℕ) : Nonempty (BallIso S T h) :=
  nonempty_ballIso_of_finiteRooted_eq S T h
    (congrArg (fun B : UnorderedLocal.BallTower => B.val h) hh)

/-- Equal complete unordered radius classes force an actual global rooted
labelled graph isomorphism, via finite witnesses and compactness. -/
theorem nonempty_unorderedIso_of_tower_eq (S T : Tree (Option ℕ) ℕ)
    (hh : toBallTower S = toBallTower T) : Nonempty (UnorderedIso S T) :=
  nonempty_unorderedIso_of_ball_isos S T (fun h => nonempty_ballIso_of_tower_eq S T hh h)

end Freezing1.PlaneLabelled
