module

import Freezing1.RootedUnorderedGraphIso

/-! Author-created expanded finite semantic statement and axiom probe. -/

open scoped Classical
open Freezing1 Freezing1.BinaryBijection

set_option backward.isDefEq.respectTransparency false

example (s t : Rooted) (h : s.UnorderedEq t) :
    Nonempty (PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled) :=
  h.nonempty_unorderedIso

example (s t : Rooted) (h : s.UnorderedEq t) :
    ∃ f : Rooted.ActualVertex s ≃ Rooted.ActualVertex t,
      f (PlaneLabelled.rootVertex s.toPlaneLabelled) = PlaneLabelled.rootVertex t.toPlaneLabelled ∧
      (∀ u v, (v.val ≠ [] ∧ v.val.dropLast = u.val) ↔
        ((f v).val ≠ [] ∧ (f v).val.dropLast = (f u).val)) ∧
      (∀ u, PlaneLabelled.vertexSlot s.toPlaneLabelled u.val =
        PlaneLabelled.vertexSlot t.toPlaneLabelled (f u).val) ∧
      (∀ u, PlaneLabelled.edgeSlot s.toPlaneLabelled u.val =
        PlaneLabelled.edgeSlot t.toPlaneLabelled (f u).val) := by
  let e := h.nonempty_unorderedIso.some
  exact ⟨e.toEquiv, e.root_eq, e.parent_iff, e.vertex_labels, e.edge_labels⟩

example (s t : Rooted) (h : s.UnorderedEq t) :
    Nonempty ((PlaneTree.graph (PlaneLabelled.shape s.toPlaneLabelled)).Iso
      (PlaneTree.graph (PlaneLabelled.shape t.toPlaneLabelled))) :=
  ⟨h.nonempty_unorderedIso.some.graphIso⟩

/-- Both edge labels repeat, and one child repeats the root's vertex label. -/
example : Nonempty (PlaneLabelled.UnorderedIso
    (Rooted.node (some 5) [(7, .node none []), (7, .node (some 5) [])]).toPlaneLabelled
    (Rooted.node (some 5) [(7, .node (some 5) []), (7, .node none [])]).toPlaneLabelled) := by
  apply Rooted.UnorderedEq.nonempty_unorderedIso
  exact .perm _ (List.Perm.swap _ _ [])

example (label : Option ℕ) (C : List (ℕ × Rooted)) :
    Nonempty ((Unit ⊕ Σ j : Fin C.length, Rooted.ActualVertex C[j].2) ≃
      Rooted.ActualVertex (.node label C)) :=
  ⟨Rooted.nodeVertexEquiv label C⟩

example (label : Option ℕ) (L M : List (ℕ × Rooted)) (φ : Fin L.length ≃ Fin M.length)
    (hedge : ∀ j, L[j].1 = M[φ j].1)
    (e : ∀ j, PlaneLabelled.UnorderedIso L[j].2.toPlaneLabelled M[φ j].2.toPlaneLabelled) :
    Nonempty (PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node label M).toPlaneLabelled) :=
  ⟨Rooted.nodeGluedIso label L M φ hedge e⟩

example (L M : List (ℕ × Rooted)) (h : L.Perm M) :
    ∃ φ : Fin L.length ≃ Fin M.length, ∀ j, L[j] = M[φ j] :=
  ⟨Rooted.permPositionEquiv h, fun j => (Rooted.permPositionEquiv_get h j).symm⟩

#print axioms Rooted.nodeVertexEquiv
#print axioms Rooted.nodeGluedIso
#print axioms Rooted.position_fiber_card
#print axioms Rooted.permPositionEquiv
#print axioms Rooted.nodePermIso
#print axioms Rooted.nodeIso_of_forall₂
#print axioms Rooted.UnorderedEq.nonempty_unorderedIso
#print axioms PlaneLabelled.UnorderedIso.graphIso
