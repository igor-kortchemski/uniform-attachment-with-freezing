module

import Freezing1.RootedUnorderedGraphIsoConverse

/-! Author-created expanded finite reflection and axiom probe. -/

open scoped Classical
open Freezing1 Freezing1.BinaryBijection

set_option backward.isDefEq.respectTransparency false

example (s t : Rooted)
    (h : Nonempty (PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled)) :
    s.UnorderedEq t := Rooted.unorderedEq_of_nonempty_unorderedIso h

example (s t : Rooted) :
    s.UnorderedEq t ↔ Nonempty (PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled) :=
  Rooted.unorderedEq_iff_nonempty_unorderedIso s t

example (s t : Rooted) :
    (Quotient.mk Rooted.unorderedSetoid s = Quotient.mk Rooted.unorderedSetoid t) ↔
      Nonempty (PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled) := by
  exact Quotient.eq.trans (Rooted.unorderedEq_iff_nonempty_unorderedIso s t)

example (label other : Option ℕ) (L M : List (ℕ × Rooted))
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) :
    label = other ∧ ∃ φ : Fin L.length ≃ Fin M.length,
      (∀ j, L[j].1 = M[φ j].1) ∧
      ∀ j : Fin L.length,
        Nonempty (PlaneLabelled.UnorderedIso L[j].2.toPlaneLabelled M[φ j].2.toPlaneLabelled) :=
  ⟨Rooted.labelledIso_rootLabel_eq e, Rooted.rootChildIndexEquiv e,
    Rooted.rootChildIndexEquiv_edge e, fun j => ⟨Rooted.childIso e j⟩⟩

example (label other : Option ℕ) (L M : List (ℕ × Rooted))
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) (j : Fin L.length) :
    ∃ f : Rooted.ActualVertex L[j].2 ≃
        Rooted.ActualVertex M[Rooted.rootChildIndexEquiv e j].2,
      (∀ u, e.toEquiv (Rooted.branchVertex label L j u) =
        Rooted.branchVertex other M (Rooted.rootChildIndexEquiv e j) (f u)) ∧
      f (PlaneLabelled.rootVertex L[j].2.toPlaneLabelled) =
        PlaneLabelled.rootVertex M[Rooted.rootChildIndexEquiv e j].2.toPlaneLabelled ∧
      (∀ u v, (v.val ≠ [] ∧ v.val.dropLast = u.val) ↔
        ((f v).val ≠ [] ∧ (f v).val.dropLast = (f u).val)) ∧
      (∀ u, PlaneLabelled.vertexSlot L[j].2.toPlaneLabelled u.val =
        PlaneLabelled.vertexSlot M[Rooted.rootChildIndexEquiv e j].2.toPlaneLabelled (f u).val) ∧
      (∀ u, PlaneLabelled.edgeSlot L[j].2.toPlaneLabelled u.val =
        PlaneLabelled.edgeSlot M[Rooted.rootChildIndexEquiv e j].2.toPlaneLabelled (f u).val) := by
  let c := Rooted.childIso e j
  exact ⟨c.toEquiv, Rooted.childVertexEquiv_spec e j, c.root_eq,
    c.parent_iff, c.vertex_labels, c.edge_labels⟩

/-- The input is an actual isomorphism; repeated edge and vertex labels impose no premise. -/
example (e : PlaneLabelled.UnorderedIso
    (Rooted.node (some 5) [(7, .node none []), (7, .node (some 5) [])]).toPlaneLabelled
    (Rooted.node (some 5) [(7, .node (some 5) []), (7, .node none [])]).toPlaneLabelled) :
    (Rooted.node (some 5) [(7, .node none []), (7, .node (some 5) [])]).UnorderedEq
    (Rooted.node (some 5) [(7, .node (some 5) []), (7, .node none [])]) :=
  Rooted.unorderedEq_of_nonempty_unorderedIso ⟨e⟩

example (k : ℕ) (L M : List (ℕ × Rooted)) :
    ¬ Nonempty (PlaneLabelled.UnorderedIso (Rooted.node none L).toPlaneLabelled
      (Rooted.node (some k) M).toPlaneLabelled) := by
  rintro ⟨e⟩
  have h := Rooted.labelledIso_rootLabel_eq e
  simp only [Rooted.rootLabel] at h
  cases h

example (label : Option ℕ) (L M : List (ℕ × Rooted))
    (φ : Fin L.length ≃ Fin M.length)
    (hedge : ∀ j : Fin L.length, L[j].1 = M[φ j].1)
    (hchild : ∀ j : Fin L.length, L[j].2.UnorderedEq M[φ j].2) :
    (Rooted.node label L).UnorderedEq (Rooted.node label M) :=
  Rooted.unorderedEq_node_of_indexEquiv label φ hedge hchild

#print axioms Rooted.rootChildEquiv
#print axioms Rooted.rootChildrenIsoEquiv
#print axioms Rooted.rootChildIndexEquiv
#print axioms Rooted.labelledIso_rootLabel_eq
#print axioms Rooted.rootChildIndexEquiv_edge
#print axioms Rooted.image_branch_exists
#print axioms Rooted.childVertexEquiv
#print axioms Rooted.childIso
#print axioms Rooted.unorderedEq_node_of_indexEquiv
#print axioms Rooted.unorderedEq_of_nonempty_unorderedIso
#print axioms Rooted.unorderedEq_iff_nonempty_unorderedIso
#print axioms PlaneLabelled.UnorderedIso.graphIso
