module

public import Freezing1.ChronologicalPlaneTree
public import Freezing1.PlaneTreeLabellings

/-!
# Actual vertices behind chronological Ulam--Harris addresses

A successful birth-ordered traversal always identifies a genuine source
vertex, with height equal to the traversal length. No extra degree or
freezing assumption is made on a valid chronological tree.
-/

@[expose] public section

namespace Freezing1.LocalTree

open scoped Classical

theorem exists_vertex_of_mem_childIDs (T : Tree) (v : Vertex T) (b : ℕ)
    (hb : b ∈ childIDs T v.val.birth) :
    ∃ w : Vertex T, w.val.birth = b ∧ w.val.birth ≠ 0 ∧ w.val.parent = v.val.birth := by
  rw [childIDs, recordAt_vertex] at hb
  obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hb
  obtain ⟨hr, hn, hp⟩ := Finset.mem_filter.mp hr
  exact ⟨⟨r, v.val.height + 1, hr⟩, he, hn, hp⟩

theorem exists_vertex_of_follow (T : Tree) (v : Vertex T) (u : PlaneTree.Address) (b : ℕ)
    (hf : follow T v.val.birth u = some b) :
    ∃ w : Vertex T, w.val.birth = b ∧ w.val.height = v.val.height + u.length := by
  induction u generalizing v b with
  | nil =>
    have hb := Option.some.inj hf
    exact ⟨v, hb, by simp⟩
  | cons j u ih =>
    by_cases hj : j = 0
    · simp [follow, hj] at hf
    · rw [follow, ite_eq_right hj] at hf
      cases hc : (childList T v.val.birth)[j - 1]? with
      | none => simp only [hc, Option.bind_none] at hf; contradiction
      | some c =>
        rw [hc, Option.bind_some] at hf
        have hmem : c ∈ childIDs T v.val.birth := by
          simpa only [childList, Finset.mem_sort] using List.mem_of_getElem? hc
        obtain ⟨w, hw, hne, hp⟩ := exists_vertex_of_mem_childIDs T v c hmem
        have hd := (parent_data_of_birth_eq T hne hp).1
        obtain ⟨z, hz, hheight⟩ := ih w b (by simpa only [hw] using hf)
        refine ⟨z, hz, ?_⟩
        simp only [List.length_cons]
        omega

theorem present_toPlaneTree_iff_follow (T : Tree) (u : PlaneTree.Address) :
    PlaneTree.Present (toPlaneTree T) u ↔ (follow T 0 u).isSome := by
  induction u using List.reverseRecOn with
  | nil => simp [follow]
  | append_singleton u j ih =>
    rw [PlaneTree.present_append_singleton, ih, follow_append]
    cases hs : follow T 0 u with
    | none => simp
    | some b =>
      change ((some b).isSome ∧ 1 ≤ j ∧ j ≤ planeOffspring T u) ↔ _
      simp only [planeOffspring, hs, Option.isSome_some, true_and, Option.bind_some]
      by_cases hj : j = 0
      · simp [follow, hj]
      · cases hc : (childList T b)[j - 1]? with
        | none =>
          have hlen := List.getElem?_eq_none_iff.mp hc
          rw [length_childList] at hlen
          simp [follow, hj, hc]
          omega
        | some c =>
          obtain ⟨hlen, _⟩ := List.getElem?_eq_some_iff.mp hc
          rw [length_childList] at hlen
          simp [follow, hj, hc]
          omega

theorem exists_vertex_of_present (T : Tree) (u : PlaneTree.Address)
    (hu : PlaneTree.Present (toPlaneTree T) u) :
    ∃ v : Vertex T, follow T 0 u = some v.val.birth ∧ v.val.height = u.length := by
  have hh := (present_toPlaneTree_iff_follow T u).mp hu
  cases hf : follow T 0 u with
  | none => simp only [hf, Option.isSome_none, Bool.false_eq_true] at hh
  | some b =>
    obtain ⟨v, hb, hv⟩ := exists_vertex_of_follow T (root T) u b (by simpa only [root_birth] using hf)
    exact ⟨v, by simp only [hb], by simpa only [root_height, zero_add] using hv⟩

noncomputable def addressVertex (T : Tree) (u : PlaneLabelled.Vertex (toPlaneTree T)) : Vertex T :=
  (exists_vertex_of_present T u.val u.property).choose

theorem follow_addressVertex (T : Tree) (u : PlaneLabelled.Vertex (toPlaneTree T)) :
    follow T 0 u.val = some (addressVertex T u).val.birth :=
  (exists_vertex_of_present T u.val u.property).choose_spec.1

theorem addressVertex_height (T : Tree) (u : PlaneLabelled.Vertex (toPlaneTree T)) :
    (addressVertex T u).val.height = u.val.length :=
  (exists_vertex_of_present T u.val u.property).choose_spec.2

theorem addressVertex_eq_of_follow (T : Tree) (u : PlaneLabelled.Vertex (toPlaneTree T))
    (v : Vertex T) (hv : follow T 0 u.val = some v.val.birth) : addressVertex T u = v := by
  apply vertex_birth_injective T
  exact Option.some.inj ((follow_addressVertex T u).symm.trans hv)

end Freezing1.LocalTree
