module

public import Freezing1.RootedPlaneLabelledCoding
public import Freezing1.PlaneLabelledGraphIso
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Fin.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Sibling-permutation equivalence gives an actual labelled graph isomorphism

Vertices are genuine Ulam--Harris addresses. The root-or-child decomposition
retains arbitrary repeated vertex and edge labels; no distinctness,
normalization, or increasing-label hypothesis is imposed.
-/

@[expose] public section

namespace Freezing1.BinaryBijection.Rooted

open scoped Classical

set_option backward.isDefEq.respectTransparency false

abbrev ActualVertex (t : Rooted) := PlaneLabelled.Vertex (PlaneLabelled.shape t.toPlaneLabelled)

abbrev NodeParts (C : List (ℕ × Rooted)) :=
  Unit ⊕ Σ j : Fin C.length, ActualVertex C[j].2

@[simp] theorem present_node_branch (label : Option ℕ) (C : List (ℕ × Rooted))
    (j : Fin C.length) (u : PlaneTree.Address) :
    PlaneTree.Present (PlaneLabelled.shape (Rooted.node label C).toPlaneLabelled) ((j.val + 1) :: u) ↔
      PlaneTree.Present (PlaneLabelled.shape C[j].2.toPlaneLabelled) u := by
  simp only [shape_toPlaneLabelled]
  rw [present_iff_subtree, present_iff_subtree]
  simp [subtree, children]

def nodeVertexMap (label : Option ℕ) (C : List (ℕ × Rooted)) :
    NodeParts C → ActualVertex (.node label C)
  | .inl _ => ⟨[], PlaneTree.present_nil _⟩
  | .inr ⟨j, u⟩ => ⟨(j.val + 1) :: u.val, (present_node_branch label C j u.val).mpr u.property⟩

theorem nodeVertexMap_injective (label : Option ℕ) (C : List (ℕ × Rooted)) :
    Function.Injective (nodeVertexMap label C) := by
  intro a b hab
  have hh := congrArg Subtype.val hab
  rcases a with a | ⟨i, u⟩ <;> rcases b with b | ⟨j, v⟩
  · exact congrArg Sum.inl (Subsingleton.elim a b)
  · simp [nodeVertexMap] at hh
  · simp [nodeVertexMap] at hh
  · change ((i.val + 1) :: u.val) = ((j.val + 1) :: v.val) at hh
    obtain ⟨hij, huv⟩ := List.cons.inj hh
    have hij' : i = j := Fin.ext (by omega)
    subst j
    have huv' : u = v := Subtype.ext huv
    subst v
    rfl

theorem nodeVertexMap_surjective (label : Option ℕ) (C : List (ℕ × Rooted)) :
    Function.Surjective (nodeVertexMap label C) := by
  rintro ⟨u, hu⟩
  cases u with
  | nil => exact ⟨Sum.inl (), rfl⟩
  | cons k u =>
    have hu' : PlaneTree.Present (Rooted.node label C).toPlaneTree (k :: u) := by
      simpa only [shape_toPlaneLabelled] using hu
    have hs := (present_iff_subtree (.node label C) (k :: u)).mp hu'
    have hk : k ≠ 0 := by
      intro he
      subst k
      simp [subtree] at hs
    cases hc : C[k - 1]? with
    | none => simp [subtree, children, hk, hc] at hs
    | some p =>
      obtain ⟨hlen, hp⟩ := List.getElem?_eq_some_iff.mp hc
      let j : Fin C.length := ⟨k - 1, hlen⟩
      have hchild : PlaneTree.Present (PlaneLabelled.shape C[j].2.toPlaneLabelled) u := by
        rw [shape_toPlaneLabelled]
        apply (present_iff_subtree _ _).mpr
        simp only [subtree, children, ite_eq_right hk, hc, Option.bind_some] at hs
        change (C[k - 1].2.subtree u).isSome
        rw [hp]
        exact hs
      refine ⟨Sum.inr ⟨j, ⟨u, hchild⟩⟩, ?_⟩
      apply Subtype.ext
      change ((k - 1 + 1) :: u) = (k :: u)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]

noncomputable def nodeVertexEquiv (label : Option ℕ) (C : List (ℕ × Rooted)) :
    NodeParts C ≃ ActualVertex (.node label C) :=
  Equiv.ofBijective (nodeVertexMap label C)
    ⟨nodeVertexMap_injective label C, nodeVertexMap_surjective label C⟩

@[simp] theorem nodeVertexEquiv_apply (label : Option ℕ) (C : List (ℕ × Rooted)) (a : NodeParts C) :
    nodeVertexEquiv label C a = nodeVertexMap label C a := rfl

@[simp] theorem node_vertexCode_branch (label : Option ℕ) (C : List (ℕ × Rooted))
    (j : Fin C.length) (u : PlaneTree.Address) :
    (Rooted.node label C).vertexCode ((j.val + 1) :: u) = C[j].2.vertexCode u := by
  apply PlaneLabelled.LabelSlot.ext_label
  simp [vertexCode, subtree, children]

theorem node_edgeCode_branch (label : Option ℕ) (C : List (ℕ × Rooted))
    (j : Fin C.length) (u : PlaneTree.Address) :
    (Rooted.node label C).edgeCode ((j.val + 1) :: u) =
      if u = [] then ⟨some C[j].1⟩ else C[j].2.edgeCode u := by
  apply PlaneLabelled.LabelSlot.ext_label
  cases u with
  | nil => simp [edgeCode, incoming, children]
  | cons k u => simp [edgeCode, incoming, children]

@[simp] theorem node_parent_root_branch (label : Option ℕ) (C : List (ℕ × Rooted))
    (j : Fin C.length) (u : ActualVertex C[j].2) :
    PlaneLabelled.Parent (nodeVertexMap label C (Sum.inl ()))
      (nodeVertexMap label C (Sum.inr ⟨j, u⟩)) ↔ u.val = [] := by
  change (((j.val + 1) :: u.val) ≠ [] ∧ ((j.val + 1) :: u.val).dropLast = []) ↔ u.val = []
  cases hu : u.val with
  | nil => simp
  | cons k v => simp

@[simp] theorem node_parent_branch_branch (label : Option ℕ) (C : List (ℕ × Rooted))
    (i j : Fin C.length) (u : ActualVertex C[i].2) (v : ActualVertex C[j].2) :
    PlaneLabelled.Parent (nodeVertexMap label C (Sum.inr ⟨i, u⟩))
      (nodeVertexMap label C (Sum.inr ⟨j, v⟩)) ↔
      i = j ∧ v.val ≠ [] ∧ v.val.dropLast = u.val := by
  change (((j.val + 1) :: v.val) ≠ [] ∧
    ((j.val + 1) :: v.val).dropLast = ((i.val + 1) :: u.val)) ↔ _
  cases hv : v.val with
  | nil => simp
  | cons k w =>
    constructor
    · rintro ⟨_, hd⟩
      have hh : j.val + 1 = i.val + 1 ∧ (k :: w).dropLast = u.val := by
        simpa only [List.dropLast_cons_cons, List.cons.injEq] using hd
      exact ⟨Fin.ext (by omega), by simp, hh.2⟩
    · rintro ⟨rfl, _, htail⟩
      refine ⟨by simp, ?_⟩
      simpa only [List.dropLast_cons_cons, List.cons.injEq] using
        (show i.val + 1 = i.val + 1 ∧ (k :: w).dropLast = u.val from ⟨rfl, htail⟩)

theorem labelledIso_root_address_iff {s t : Rooted}
    (e : PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled) (u : ActualVertex s) :
    u.val = [] ↔ (e.toEquiv u).val = [] := by
  constructor
  · intro hu
    have he : u = PlaneLabelled.rootVertex s.toPlaneLabelled := Subtype.ext hu
    rw [he, e.root_eq]
    rfl
  · intro hu
    have he : e.toEquiv u = PlaneLabelled.rootVertex t.toPlaneLabelled := Subtype.ext hu
    have hr : u = PlaneLabelled.rootVertex s.toPlaneLabelled :=
      e.toEquiv.injective (he.trans e.root_eq.symm)
    exact congrArg Subtype.val hr

noncomputable def gluedVertexEquiv (label : Option ℕ) (L M : List (ℕ × Rooted))
    (φ : Fin L.length ≃ Fin M.length)
    (e : ∀ j, PlaneLabelled.UnorderedIso L[j].2.toPlaneLabelled M[φ j].2.toPlaneLabelled) :
    ActualVertex (.node label L) ≃ ActualVertex (.node label M) :=
  (nodeVertexEquiv label L).symm.trans
    ((Equiv.sumCongr (Equiv.refl Unit) (Equiv.sigmaCongr φ fun j => (e j).toEquiv)).trans
      (nodeVertexEquiv label M))

theorem gluedVertexEquiv_root (label : Option ℕ) (L M : List (ℕ × Rooted))
    (φ : Fin L.length ≃ Fin M.length)
    (e : ∀ j, PlaneLabelled.UnorderedIso L[j].2.toPlaneLabelled M[φ j].2.toPlaneLabelled) :
    gluedVertexEquiv label L M φ e (nodeVertexMap label L (Sum.inl ())) =
      nodeVertexMap label M (Sum.inl ()) := by
  change gluedVertexEquiv label L M φ e ((nodeVertexEquiv label L) (Sum.inl ())) = _
  simp only [gluedVertexEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem gluedVertexEquiv_branch (label : Option ℕ) (L M : List (ℕ × Rooted))
    (φ : Fin L.length ≃ Fin M.length)
    (e : ∀ j, PlaneLabelled.UnorderedIso L[j].2.toPlaneLabelled M[φ j].2.toPlaneLabelled)
    (j : Fin L.length) (u : ActualVertex L[j].2) :
    gluedVertexEquiv label L M φ e (nodeVertexMap label L (Sum.inr ⟨j, u⟩)) =
      nodeVertexMap label M (Sum.inr ⟨φ j, (e j).toEquiv u⟩) := by
  change gluedVertexEquiv label L M φ e ((nodeVertexEquiv label L) (Sum.inr ⟨j, u⟩)) = _
  simp only [gluedVertexEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- A branch bijection and genuine child isomorphisms glue to an isomorphism
of the actual rooted labelled trees. All vertex and incoming-edge slots are
preserved, including the root's absent incoming slot. -/
noncomputable def nodeGluedIso (label : Option ℕ) (L M : List (ℕ × Rooted))
    (φ : Fin L.length ≃ Fin M.length)
    (hedge : ∀ j, L[j].1 = M[φ j].1)
    (e : ∀ j, PlaneLabelled.UnorderedIso L[j].2.toPlaneLabelled M[φ j].2.toPlaneLabelled) :
    PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node label M).toPlaneLabelled where
  toEquiv := gluedVertexEquiv label L M φ e
  root_eq := gluedVertexEquiv_root label L M φ e
  parent_iff a b := by
    obtain ⟨u, rfl⟩ := nodeVertexMap_surjective label L a
    obtain ⟨v, rfl⟩ := nodeVertexMap_surjective label L b
    rcases u with u | ⟨i, u⟩ <;> rcases v with v | ⟨j, v⟩
    · cases u
      cases v
      rw [gluedVertexEquiv_root]
      simp [PlaneLabelled.Parent, nodeVertexMap]
    · cases u
      rw [gluedVertexEquiv_root, gluedVertexEquiv_branch,
        node_parent_root_branch, node_parent_root_branch]
      exact labelledIso_root_address_iff (e j) v
    · cases v
      rw [gluedVertexEquiv_branch, gluedVertexEquiv_root]
      simp [PlaneLabelled.Parent, nodeVertexMap]
    · rw [gluedVertexEquiv_branch, gluedVertexEquiv_branch,
        node_parent_branch_branch, node_parent_branch_branch]
      by_cases hij : i = j
      · subst j
        simpa only [PlaneLabelled.Parent, eq_self_iff_true, true_and] using (e i).parent_iff u v
      · have hφ : φ i ≠ φ j := fun he => hij (φ.injective he)
        simp only [hij, hφ, false_and]
  vertex_labels a := by
    obtain ⟨u, rfl⟩ := nodeVertexMap_surjective label L a
    rcases u with u | ⟨j, u⟩
    · cases u
      rw [gluedVertexEquiv_root]
      rfl
    · rw [gluedVertexEquiv_branch]
      change (Rooted.node label L).vertexCode ((j.val + 1) :: u.val) =
        (Rooted.node label M).vertexCode (((φ j).val + 1) :: ((e j).toEquiv u).val)
      rw [node_vertexCode_branch, node_vertexCode_branch]
      exact (e j).vertex_labels u
  edge_labels a := by
    obtain ⟨u, rfl⟩ := nodeVertexMap_surjective label L a
    rcases u with u | ⟨j, u⟩
    · cases u
      rw [gluedVertexEquiv_root]
      rfl
    · rw [gluedVertexEquiv_branch]
      change (Rooted.node label L).edgeCode ((j.val + 1) :: u.val) =
        (Rooted.node label M).edgeCode (((φ j).val + 1) :: ((e j).toEquiv u).val)
      rw [node_edgeCode_branch, node_edgeCode_branch]
      by_cases hu : u.val = []
      · rw [ite_eq_left hu, ite_eq_left ((labelledIso_root_address_iff (e j) u).mp hu)]
        apply PlaneLabelled.LabelSlot.ext_label
        exact congrArg some (hedge j)
      · have he : ((e j).toEquiv u).val ≠ [] :=
          fun he => hu ((labelledIso_root_address_iff (e j) u).mpr he)
        rw [ite_eq_right hu, ite_eq_right he]
        exact (e j).edge_labels u

theorem position_fiber_card (C : List (ℕ × Rooted)) (p : ℕ × Rooted) :
    Fintype.card {j : Fin C.length // C[j] = p} = C.count p := by
  rw [Fintype.card_subtype]
  simpa only [List.Vector.get_eq_get_toList, List.Vector.toList_mk, Fin.cast_mk,
    List.get_eq_getElem, Fin.val_cast, Fin.getElem_fin] using Fin.card_filter_univ_eq_vector_get_eq_count p
    (⟨C, rfl⟩ : List.Vector (ℕ × Rooted) C.length)

noncomputable def permPositionFiberEquiv {L M : List (ℕ × Rooted)} (hp : L.Perm M)
    (p : ℕ × Rooted) :
    {j : Fin L.length // L[j] = p} ≃ {j : Fin M.length // M[j] = p} :=
  Fintype.equivOfCardEq ((position_fiber_card L p).trans
    ((hp.count_eq p).trans (position_fiber_card M p).symm))

/-- Permuting list entries bijects their occurrences, even when labelled
child pairs repeat. Fibres are counted with multiplicity. -/
noncomputable def permPositionEquiv {L M : List (ℕ × Rooted)} (hp : L.Perm M) :
    Fin L.length ≃ Fin M.length :=
  Equiv.ofFiberEquiv (permPositionFiberEquiv hp)

theorem permPositionEquiv_get {L M : List (ℕ × Rooted)} (hp : L.Perm M) (j : Fin L.length) :
    M[permPositionEquiv hp j] = L[j] :=
  Equiv.ofFiberEquiv_map (permPositionFiberEquiv hp) j

def labelledIsoOfEq {s t : Rooted} (h : s = t) :
    PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled := by
  subst t
  exact PlaneLabelled.UnorderedIso.refl _

noncomputable def nodePermIso (label : Option ℕ) {L M : List (ℕ × Rooted)} (hp : L.Perm M) :
    PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node label M).toPlaneLabelled :=
  nodeGluedIso label L M (permPositionEquiv hp)
    (fun j => congrArg Prod.fst (permPositionEquiv_get hp j).symm)
    (fun j => labelledIsoOfEq (congrArg Prod.snd (permPositionEquiv_get hp j).symm))

def ChildIsoRel (p q : ℕ × Rooted) : Prop :=
  p.1 = q.1 ∧ Nonempty (PlaneLabelled.UnorderedIso p.2.toPlaneLabelled q.2.toPlaneLabelled)

theorem childIsoRel_refl (p : ℕ × Rooted) : ChildIsoRel p p :=
  ⟨rfl, ⟨PlaneLabelled.UnorderedIso.refl _⟩⟩

theorem forall₂_childIsoRel_refl (C : List (ℕ × Rooted)) : List.Forall₂ ChildIsoRel C C := by
  induction C with
  | nil => exact .nil
  | cons p C ih => exact .cons (childIsoRel_refl p) ih

theorem nodeIso_of_forall₂ (label : Option ℕ) {L M : List (ℕ × Rooted)}
    (h : List.Forall₂ ChildIsoRel L M) :
    Nonempty (PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node label M).toPlaneLabelled) := by
  let φ : Fin L.length ≃ Fin M.length := (Fin.castOrderIso h.length_eq).toEquiv
  have hr : ∀ j, ChildIsoRel L[j] M[φ j] := by
    intro j
    exact h.get j.isLt (by rw [← h.length_eq]; exact j.isLt)
  exact ⟨nodeGluedIso label L M φ (fun j => (hr j).1) (fun j => (hr j).2.some)⟩

/-- The finite sibling-permutation quotient forgets exactly auxiliary plane
order in this direction: it supplies a genuine rooted labelled graph
isomorphism on actual vertices, with arbitrary repeated source labels. -/
theorem UnorderedEq.nonempty_unorderedIso {s t : Rooted} (h : s.UnorderedEq t) :
    Nonempty (PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled) := by
  induction h with
  | refl t => exact ⟨PlaneLabelled.UnorderedIso.refl _⟩
  | symm h ih => exact ⟨ih.some.symm⟩
  | trans h₁ h₂ ih₁ ih₂ => exact ⟨ih₁.some.trans ih₂.some⟩
  | perm label hp => exact ⟨nodePermIso label hp⟩
  | child label edge before after he ih =>
    apply nodeIso_of_forall₂ label
    exact List.rel_append (forall₂_childIsoRel_refl before)
      (.cons ⟨rfl, ih⟩ (forall₂_childIsoRel_refl after))

end Freezing1.BinaryBijection.Rooted
