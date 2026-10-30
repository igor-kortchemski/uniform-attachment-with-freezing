module

public import Freezing1.RootedUnorderedGraphIso
public import Mathlib.Data.List.FinRange

/-!
# Actual finite rooted labelled isomorphisms respect the sibling quotient

The converse does not require distinct labels. Root children are recovered
from the actual parent relation, and the isomorphism is restricted to their
actual descendant components before structural induction is applied.
-/

@[expose] public section

namespace Freezing1.BinaryBijection.Rooted

open scoped Classical

set_option backward.isDefEq.respectTransparency false

def branchVertex (label : Option ℕ) (C : List (ℕ × Rooted)) (j : Fin C.length)
    (u : ActualVertex C[j].2) : ActualVertex (.node label C) :=
  nodeVertexMap label C (Sum.inr ⟨j, u⟩)

theorem branchVertex_injective (label : Option ℕ) (C : List (ℕ × Rooted)) (j : Fin C.length) :
    Function.Injective (branchVertex label C j) := by
  intro u v h
  have hh := congrArg Subtype.val h
  change ((j.val + 1) :: u.val) = ((j.val + 1) :: v.val) at hh
  exact Subtype.ext (List.cons.inj hh).2

def RootChildren (s : Rooted) :=
  {u : ActualVertex s // PlaneLabelled.Parent (PlaneLabelled.rootVertex s.toPlaneLabelled) u}

def rootChildMap (label : Option ℕ) (C : List (ℕ × Rooted)) (j : Fin C.length) :
    RootChildren (.node label C) :=
  ⟨branchVertex label C j (PlaneLabelled.rootVertex C[j].2.toPlaneLabelled),
    (node_parent_root_branch label C j _).mpr rfl⟩

theorem rootChildMap_injective (label : Option ℕ) (C : List (ℕ × Rooted)) :
    Function.Injective (rootChildMap label C) := by
  intro i j h
  have hh := congrArg (fun v : RootChildren (.node label C) => v.val.val) h
  change ((i.val + 1) :: []) = ((j.val + 1) :: []) at hh
  have := (List.cons.inj hh).1
  exact Fin.ext (by omega)

theorem rootChildMap_surjective (label : Option ℕ) (C : List (ℕ × Rooted)) :
    Function.Surjective (rootChildMap label C) := by
  intro v
  obtain ⟨a, ha⟩ := nodeVertexMap_surjective label C v.val
  have hv := v.property
  rw [← ha] at hv
  rcases a with a | ⟨j, u⟩
  · cases a
    simp [PlaneLabelled.Parent, PlaneLabelled.rootVertex, nodeVertexMap] at hv
  · have hu : u.val = [] := (node_parent_root_branch label C j u).mp hv
    have hue : u = PlaneLabelled.rootVertex C[j].2.toPlaneLabelled := Subtype.ext hu
    refine ⟨j, ?_⟩
    apply Subtype.ext
    rw [← ha, hue]
    rfl

noncomputable def rootChildEquiv (label : Option ℕ) (C : List (ℕ × Rooted)) :
    Fin C.length ≃ RootChildren (.node label C) :=
  Equiv.ofBijective (rootChildMap label C)
    ⟨rootChildMap_injective label C, rootChildMap_surjective label C⟩

noncomputable def rootChildrenIsoEquiv {s t : Rooted}
    (e : PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled) :
    RootChildren s ≃ RootChildren t where
  toFun u := ⟨e.toEquiv u.val, by
    have h := (e.parent_iff (PlaneLabelled.rootVertex s.toPlaneLabelled) u.val).mp u.property
    simpa only [e.root_eq] using h⟩
  invFun v := ⟨e.toEquiv.symm v.val, by
    have h := (e.symm.parent_iff (PlaneLabelled.rootVertex t.toPlaneLabelled) v.val).mp v.property
    rw [e.symm.root_eq] at h
    simpa only [PlaneLabelled.UnorderedIso.symm] using h⟩
  left_inv u := by
    apply Subtype.ext
    exact e.toEquiv.symm_apply_apply u.val
  right_inv v := by
    apply Subtype.ext
    exact e.toEquiv.apply_symm_apply v.val

noncomputable def rootChildIndexEquiv {label other : Option ℕ} {L M : List (ℕ × Rooted)}
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) : Fin L.length ≃ Fin M.length :=
  ((rootChildEquiv label L).trans (rootChildrenIsoEquiv e)).trans (rootChildEquiv other M).symm

theorem rootChildIndexEquiv_vertex {label other : Option ℕ} {L M : List (ℕ × Rooted)}
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) (j : Fin L.length) :
    e.toEquiv (branchVertex label L j (PlaneLabelled.rootVertex L[j].2.toPlaneLabelled)) =
      branchVertex other M (rootChildIndexEquiv e j)
        (PlaneLabelled.rootVertex M[rootChildIndexEquiv e j].2.toPlaneLabelled) := by
  have he : rootChildEquiv other M (rootChildIndexEquiv e j) =
      rootChildrenIsoEquiv e (rootChildEquiv label L j) := by
    change rootChildEquiv other M ((rootChildEquiv other M).symm _) = _
    exact (rootChildEquiv other M).apply_symm_apply _
  have hh := congrArg (fun v : RootChildren (.node other M) => v.val) he
  dsimp only [rootChildEquiv, rootChildrenIsoEquiv, rootChildMap] at hh
  exact hh.symm

theorem labelledIso_rootLabel_eq {s t : Rooted}
    (e : PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled) : s.rootLabel = t.rootLabel := by
  have h := e.vertex_labels (PlaneLabelled.rootVertex s.toPlaneLabelled)
  rw [e.root_eq] at h
  have hh := congrArg (fun v : PlaneLabelled.LabelSlot (Option ℕ) => v.label) h
  change some s.rootLabel = some t.rootLabel at hh
  exact Option.some.inj hh

theorem rootChildIndexEquiv_edge {label other : Option ℕ} {L M : List (ℕ × Rooted)}
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) (j : Fin L.length) :
    L[j].1 = M[rootChildIndexEquiv e j].1 := by
  have h := e.edge_labels (branchVertex label L j (PlaneLabelled.rootVertex L[j].2.toPlaneLabelled))
  rw [rootChildIndexEquiv_vertex] at h
  change (Rooted.node label L).edgeCode ((j.val + 1) :: []) =
    (Rooted.node other M).edgeCode (((rootChildIndexEquiv e j).val + 1) :: []) at h
  rw [node_edgeCode_branch, node_edgeCode_branch] at h
  simp only [ite_true] at h
  exact Option.some.inj (congrArg PlaneLabelled.LabelSlot.label h)

theorem image_branch_exists {label other : Option ℕ} {L M : List (ℕ × Rooted)}
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) (j : Fin L.length) (u : ActualVertex L[j].2) :
    ∃ v : ActualVertex M[rootChildIndexEquiv e j].2,
      e.toEquiv (branchVertex label L j u) = branchVertex other M (rootChildIndexEquiv e j) v := by
  suffices ∀ n, ∀ u : ActualVertex L[j].2, u.val.length = n →
      ∃ v : ActualVertex M[rootChildIndexEquiv e j].2,
        e.toEquiv (branchVertex label L j u) = branchVertex other M (rootChildIndexEquiv e j) v from
    this u.val.length u rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hlen
    by_cases hu : u.val = []
    · have hue : u = PlaneLabelled.rootVertex L[j].2.toPlaneLabelled := Subtype.ext hu
      exact ⟨_, by simpa only [hue] using rootChildIndexEquiv_vertex e j⟩
    · let up : ActualVertex L[j].2 :=
        ⟨u.val.dropLast, PlaneTree.present_of_prefix u.val.dropLast_prefix u.property⟩
      have hshort : up.val.length < n := by
        change u.val.dropLast.length < n
        rw [List.length_dropLast, hlen]
        have hn : n ≠ 0 := by
          intro hn
          apply hu
          exact List.length_eq_zero_iff.mp (hlen.trans hn)
        omega
      obtain ⟨vp, hvp⟩ := ih _ hshort up rfl
      have hp : PlaneLabelled.Parent (branchVertex label L j up) (branchVertex label L j u) := by
        change ((j.val + 1) :: u.val) ≠ [] ∧
          ((j.val + 1) :: u.val).dropLast = ((j.val + 1) :: up.val)
        refine ⟨by simp, ?_⟩
        rw [List.dropLast_cons_of_ne_nil hu]
      have ht := (e.parent_iff _ _).mp hp
      rw [hvp] at ht
      obtain ⟨a, ha⟩ := nodeVertexMap_surjective other M (e.toEquiv (branchVertex label L j u))
      rw [← ha] at ht
      rcases a with a | ⟨k, v⟩
      · cases a
        simp [PlaneLabelled.Parent, nodeVertexMap] at ht
      · have hk : rootChildIndexEquiv e j = k :=
          (node_parent_branch_branch other M _ _ vp v).mp ht |>.1
        subst k
        exact ⟨v, ha.symm⟩

noncomputable def branchForwardMap {label other : Option ℕ} {L M : List (ℕ × Rooted)}
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) (j : Fin L.length) (u : ActualVertex L[j].2) :
    ActualVertex M[rootChildIndexEquiv e j].2 :=
  (image_branch_exists e j u).choose

theorem branchForwardMap_spec {label other : Option ℕ} {L M : List (ℕ × Rooted)}
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) (j : Fin L.length) (u : ActualVertex L[j].2) :
    e.toEquiv (branchVertex label L j u) =
      branchVertex other M (rootChildIndexEquiv e j) (branchForwardMap e j u) :=
  (image_branch_exists e j u).choose_spec

theorem branchForwardMap_injective {label other : Option ℕ} {L M : List (ℕ × Rooted)}
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) (j : Fin L.length) :
    Function.Injective (branchForwardMap e j) := by
  intro u v huv
  apply branchVertex_injective label L j
  apply e.toEquiv.injective
  rw [branchForwardMap_spec, branchForwardMap_spec, huv]

theorem branchForwardMap_surjective {label other : Option ℕ} {L M : List (ℕ × Rooted)}
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) (j : Fin L.length) :
    Function.Surjective (branchForwardMap e j) := by
  intro v
  let target := branchVertex other M (rootChildIndexEquiv e j) v
  let z := e.toEquiv.symm target
  obtain ⟨a, ha⟩ := nodeVertexMap_surjective label L z
  have he : e.toEquiv (nodeVertexMap label L a) = target := by
    rw [ha]
    exact e.toEquiv.apply_symm_apply target
  rcases a with a | ⟨k, u⟩
  · cases a
    have hr : e.toEquiv (nodeVertexMap label L (Sum.inl ())) =
        PlaneLabelled.rootVertex (Rooted.node other M).toPlaneLabelled := e.root_eq
    rw [hr] at he
    have hh := congrArg Subtype.val he
    simp [PlaneLabelled.rootVertex, target, branchVertex, nodeVertexMap] at hh
  · obtain ⟨w, hw⟩ := image_branch_exists e k u
    have hh := congrArg Subtype.val (hw.symm.trans he)
    change (((rootChildIndexEquiv e k).val + 1) :: w.val) =
      (((rootChildIndexEquiv e j).val + 1) :: v.val) at hh
    have hk : rootChildIndexEquiv e k = rootChildIndexEquiv e j :=
      Fin.ext (by have := (List.cons.inj hh).1; omega)
    have hk' : k = j := (rootChildIndexEquiv e).injective hk
    subst k
    refine ⟨u, ?_⟩
    apply branchVertex_injective other M (rootChildIndexEquiv e j)
    exact (branchForwardMap_spec e j u).symm.trans he

noncomputable def childVertexEquiv {label other : Option ℕ} {L M : List (ℕ × Rooted)}
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) (j : Fin L.length) :
    ActualVertex L[j].2 ≃ ActualVertex M[rootChildIndexEquiv e j].2 :=
  Equiv.ofBijective (branchForwardMap e j)
    ⟨branchForwardMap_injective e j, branchForwardMap_surjective e j⟩

theorem childVertexEquiv_spec {label other : Option ℕ} {L M : List (ℕ × Rooted)}
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) (j : Fin L.length) (u : ActualVertex L[j].2) :
    e.toEquiv (branchVertex label L j u) =
      branchVertex other M (rootChildIndexEquiv e j) (childVertexEquiv e j u) :=
  branchForwardMap_spec e j u

theorem childVertexEquiv_root {label other : Option ℕ} {L M : List (ℕ × Rooted)}
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) (j : Fin L.length) :
    childVertexEquiv e j (PlaneLabelled.rootVertex L[j].2.toPlaneLabelled) =
      PlaneLabelled.rootVertex M[rootChildIndexEquiv e j].2.toPlaneLabelled := by
  apply branchVertex_injective other M (rootChildIndexEquiv e j)
  exact (childVertexEquiv_spec e j _).symm.trans (rootChildIndexEquiv_vertex e j)

/-- Restrict the actual isomorphism to the descendant component of one
root child. The root's relative incoming slot is absent on both sides. -/
noncomputable def childIso {label other : Option ℕ} {L M : List (ℕ × Rooted)}
    (e : PlaneLabelled.UnorderedIso (Rooted.node label L).toPlaneLabelled
      (Rooted.node other M).toPlaneLabelled) (j : Fin L.length) :
    PlaneLabelled.UnorderedIso L[j].2.toPlaneLabelled M[rootChildIndexEquiv e j].2.toPlaneLabelled where
  toEquiv := childVertexEquiv e j
  root_eq := childVertexEquiv_root e j
  parent_iff u v := by
    have h := e.parent_iff (branchVertex label L j u) (branchVertex label L j v)
    rw [childVertexEquiv_spec, childVertexEquiv_spec] at h
    simp only [branchVertex] at h
    rw [node_parent_branch_branch, node_parent_branch_branch] at h
    simpa only [eq_self_iff_true, true_and, PlaneLabelled.Parent] using h
  vertex_labels u := by
    have h := e.vertex_labels (branchVertex label L j u)
    rw [childVertexEquiv_spec] at h
    change (Rooted.node label L).vertexCode ((j.val + 1) :: u.val) =
      (Rooted.node other M).vertexCode
        (((rootChildIndexEquiv e j).val + 1) :: (childVertexEquiv e j u).val) at h
    rw [node_vertexCode_branch, node_vertexCode_branch] at h
    exact h
  edge_labels u := by
    by_cases hu : u.val = []
    · have hue : u = PlaneLabelled.rootVertex L[j].2.toPlaneLabelled := Subtype.ext hu
      rw [hue, childVertexEquiv_root]
      rfl
    · have hv : (childVertexEquiv e j u).val ≠ [] := by
        intro hv
        have heq : childVertexEquiv e j u =
            PlaneLabelled.rootVertex M[rootChildIndexEquiv e j].2.toPlaneLabelled := Subtype.ext hv
        have hue : u = PlaneLabelled.rootVertex L[j].2.toPlaneLabelled :=
          (childVertexEquiv e j).injective (heq.trans (childVertexEquiv_root e j).symm)
        exact hu (congrArg Subtype.val hue)
      have h := e.edge_labels (branchVertex label L j u)
      rw [childVertexEquiv_spec] at h
      change (Rooted.node label L).edgeCode ((j.val + 1) :: u.val) =
        (Rooted.node other M).edgeCode
          (((rootChildIndexEquiv e j).val + 1) :: (childVertexEquiv e j u).val) at h
      rw [node_edgeCode_branch, node_edgeCode_branch, ite_eq_right hu, ite_eq_right hv] at h
      exact h

def ChildUnorderedRel (p q : ℕ × Rooted) : Prop := p.1 = q.1 ∧ p.2.UnorderedEq q.2

theorem node_unorderedEq_of_forall₂_aux (label : Option ℕ)
    {L M : List (ℕ × Rooted)} (h : List.Forall₂ ChildUnorderedRel L M)
    (before : List (ℕ × Rooted)) :
    (Rooted.node label (before ++ L)).UnorderedEq (Rooted.node label (before ++ M)) := by
  induction h generalizing before with
  | nil => exact .refl _
  | @cons p q L M hpq htail ih =>
    rcases p with ⟨edge, s⟩
    rcases q with ⟨other, t⟩
    change edge = other ∧ s.UnorderedEq t at hpq
    obtain ⟨hedge, hchild⟩ := hpq
    subst other
    have hfirst := UnorderedEq.child label edge before L hchild
    have hrest : (Rooted.node label (before ++ (edge, t) :: L)).UnorderedEq
        (Rooted.node label (before ++ (edge, t) :: M)) := by
      simpa only [List.append_assoc, List.singleton_append] using ih (before ++ [(edge, t)])
    exact hfirst.trans hrest

theorem node_unorderedEq_of_forall₂ (label : Option ℕ)
    {L M : List (ℕ × Rooted)} (h : List.Forall₂ ChildUnorderedRel L M) :
    (Rooted.node label L).UnorderedEq (Rooted.node label M) := by
  simpa only [List.nil_append] using node_unorderedEq_of_forall₂_aux label h []

theorem ofFn_equiv_perm {α : Type*} {a b : ℕ} (f : Fin a → α) (g : Fin b → α)
    (φ : Fin a ≃ Fin b) (hfg : ∀ j, f j = g (φ j)) : (List.ofFn f).Perm (List.ofFn g) := by
  have hab : a = b := by simpa only [Fintype.card_fin] using Fintype.card_congr φ
  subst b
  have hf : f = g ∘ φ := funext hfg
  rw [hf]
  exact Equiv.Perm.ofFn_comp_perm φ g

theorem unorderedEq_node_of_indexEquiv (label : Option ℕ) {L M : List (ℕ × Rooted)}
    (φ : Fin L.length ≃ Fin M.length) (hedge : ∀ j : Fin L.length, L[j].1 = M[φ j].1)
    (hchild : ∀ j : Fin L.length, L[j].2.UnorderedEq M[φ j].2) :
    (Rooted.node label L).UnorderedEq (Rooted.node label M) := by
  let N := List.ofFn (fun j : Fin L.length => M[φ j])
  have hrel : List.Forall₂ ChildUnorderedRel L N := by
    apply List.forall₂_iff_get.mpr
    refine ⟨by simp [N], fun i hi hn => ?_⟩
    have hright : N.get ⟨i, hn⟩ = M[φ ⟨i, hi⟩] := by
      simp only [N, List.get_eq_getElem, List.getElem_ofFn]
    rw [hright]
    exact ⟨hedge ⟨i, hi⟩, hchild ⟨i, hi⟩⟩
  have hperm : N.Perm M := by
    have hh := ofFn_equiv_perm (fun j : Fin L.length => M[φ j])
      (fun j : Fin M.length => M[j]) φ (fun _ => rfl)
    simpa only [N, Fin.getElem_fin, List.ofFn_getElem] using hh
  exact (node_unorderedEq_of_forall₂ label hrel).trans (.perm label hperm)

/-- Reflection for every finite rooted labelled tree, with repeated labels
allowed: the actual graph isomorphism cannot identify different sibling
permutation classes. -/
theorem unorderedEq_of_nonempty_unorderedIso {s t : Rooted}
    (h : Nonempty (PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled)) :
    s.UnorderedEq t := by
  suffices ∀ n (s t : Rooted), sizeOf s = n →
      Nonempty (PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled) → s.UnorderedEq t from
    this (sizeOf s) s t rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s t hs h
    cases s with
    | node label L =>
      cases t with
      | node other M =>
        obtain ⟨e⟩ := h
        have hlabel : label = other := labelledIso_rootLabel_eq e
        subst other
        apply unorderedEq_node_of_indexEquiv label (rootChildIndexEquiv e) (rootChildIndexEquiv_edge e)
        intro j
        have hmem : L[j] ∈ L := by
          simpa only [List.get_eq_getElem, Fin.getElem_fin] using List.get_mem L j
        have hsmall : sizeOf L[j].2 < n := by
          simpa only [hs] using child_size_lt label L L[j] hmem
        exact ih _ hsmall L[j].2 M[rootChildIndexEquiv e j].2 rfl ⟨childIso e j⟩

theorem unorderedEq_iff_nonempty_unorderedIso (s t : Rooted) :
    s.UnorderedEq t ↔ Nonempty (PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled) :=
  ⟨fun h => h.nonempty_unorderedIso, unorderedEq_of_nonempty_unorderedIso⟩

end Freezing1.BinaryBijection.Rooted
