module

public import Freezing1.PlaneTreeGraph

/-!
# Forgetting plane order means an actual rooted labelled isomorphism

The witness bijects actual Ulam--Harris vertices, fixes the root, preserves
the parent relation in both directions, and preserves actual vertex and
incoming-edge labels. Auxiliary graph vertex IDs are never source labels.
-/

@[expose] public section

namespace Freezing1.PlaneTree

open scoped Classical

theorem graph_adj_address (T : Tree) (u v : {u : Address // Present T u}) :
    (graph T).Adj (vertexOfAddress T u) (vertexOfAddress T v) ↔
      u ≠ v ∧ ((u.val ≠ [] ∧ u.val.dropLast = v.val) ∨
        (v.val ≠ [] ∧ v.val.dropLast = u.val)) := by
  change (vertexOfAddress T u ≠ vertexOfAddress T v ∧
    ((addressCode u.val ≠ 0 ∧ addressCode u.val.dropLast = addressCode v.val) ∨
      (addressCode v.val ≠ 0 ∧ addressCode v.val.dropLast = addressCode u.val))) ↔ _
  simp only [ne_eq, (vertexOfAddress_injective T).eq_iff, addressCode_eq_zero_iff,
    addressCode_injective.eq_iff]

theorem vertexOfAddress_root (T : Tree) :
    vertexOfAddress T ⟨[], present_nil T⟩ = LocalTree.root (auxiliaryTree T) := by
  apply LocalTree.vertex_birth_injective _
  change 0 = (LocalTree.root (auxiliaryTree T)).val.birth
  rw [LocalTree.root_birth]

end Freezing1.PlaneTree

namespace Freezing1.PlaneLabelled

open scoped Classical

variable {V E : Type*}

def rootVertex (T : Tree V E) : Vertex (shape T) := ⟨[], PlaneTree.present_nil _⟩

def Parent {T : PlaneTree.Tree} (u v : Vertex T) : Prop :=
  v.val ≠ [] ∧ v.val.dropLast = u.val

structure UnorderedIso (S T : Tree V E) where
  toEquiv : Vertex (shape S) ≃ Vertex (shape T)
  root_eq : toEquiv (rootVertex S) = rootVertex T
  parent_iff : ∀ u v, Parent u v ↔ Parent (toEquiv u) (toEquiv v)
  vertex_labels : ∀ u, vertexSlot S u.val = vertexSlot T (toEquiv u).val
  edge_labels : ∀ u, edgeSlot S u.val = edgeSlot T (toEquiv u).val

def UnorderedIso.refl (T : Tree V E) : UnorderedIso T T where
  toEquiv := Equiv.refl _
  root_eq := rfl
  parent_iff _ _ := Iff.rfl
  vertex_labels _ := rfl
  edge_labels _ := rfl

def UnorderedIso.symm {S T : Tree V E} (e : UnorderedIso S T) : UnorderedIso T S where
  toEquiv := e.toEquiv.symm
  root_eq := by
    apply e.toEquiv.injective
    simpa only [Equiv.apply_symm_apply] using e.root_eq.symm
  parent_iff u v := by
    simpa only [Equiv.apply_symm_apply] using
      (e.parent_iff (e.toEquiv.symm u) (e.toEquiv.symm v)).symm
  vertex_labels u := by
    simpa only [Equiv.apply_symm_apply] using (e.vertex_labels (e.toEquiv.symm u)).symm
  edge_labels u := by
    simpa only [Equiv.apply_symm_apply] using (e.edge_labels (e.toEquiv.symm u)).symm

def UnorderedIso.trans {R S T : Tree V E} (e : UnorderedIso R S) (f : UnorderedIso S T) :
    UnorderedIso R T where
  toEquiv := e.toEquiv.trans f.toEquiv
  root_eq := by simp only [Equiv.trans_apply, e.root_eq, f.root_eq]
  parent_iff u v := (e.parent_iff u v).trans (f.parent_iff (e.toEquiv u) (e.toEquiv v))
  vertex_labels u := (e.vertex_labels u).trans (f.vertex_labels (e.toEquiv u))
  edge_labels u := (e.edge_labels u).trans (f.edge_labels (e.toEquiv u))

theorem UnorderedIso.adj_iff {S T : Tree V E} (e : UnorderedIso S T)
    (u v : Vertex (shape S)) :
    (PlaneTree.graph (shape S)).Adj (PlaneTree.vertexOfAddress _ u) (PlaneTree.vertexOfAddress _ v) ↔
    (PlaneTree.graph (shape T)).Adj (PlaneTree.vertexOfAddress _ (e.toEquiv u))
      (PlaneTree.vertexOfAddress _ (e.toEquiv v)) := by
  rw [PlaneTree.graph_adj_address, PlaneTree.graph_adj_address]
  change (u ≠ v ∧ (Parent v u ∨ Parent u v)) ↔
    (e.toEquiv u ≠ e.toEquiv v ∧ (Parent (e.toEquiv v) (e.toEquiv u) ∨
      Parent (e.toEquiv u) (e.toEquiv v)))
  rw [e.toEquiv.injective.ne_iff, ← e.parent_iff u v, ← e.parent_iff v u]

noncomputable def UnorderedIso.graphIso {S T : Tree V E} (e : UnorderedIso S T) :
    (PlaneTree.graph (shape S)).Iso (PlaneTree.graph (shape T)) := by
  let a := PlaneTree.addressEquiv (shape S)
  let b := PlaneTree.addressEquiv (shape T)
  refine ⟨(a.symm.trans e.toEquiv).trans b, ?_⟩
  intro v w
  have hh := e.adj_iff (a.symm v) (a.symm w)
  change (PlaneTree.graph (shape S)).Adj (a (a.symm v)) (a (a.symm w)) ↔
    (PlaneTree.graph (shape T)).Adj (b (e.toEquiv (a.symm v))) (b (e.toEquiv (a.symm w))) at hh
  rw [a.apply_symm_apply, a.apply_symm_apply] at hh
  exact hh.symm

def unorderedSetoid (V E : Type*) : Setoid (Tree V E) where
  r S T := Nonempty (UnorderedIso S T)
  iseqv := ⟨fun T => ⟨UnorderedIso.refl T⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

end Freezing1.PlaneLabelled
