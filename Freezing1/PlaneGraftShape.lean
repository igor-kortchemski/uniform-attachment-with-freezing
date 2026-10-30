module

public import Freezing1.PlaneStateGraftRight

/-!
# The finite first-child decomposition agrees with the plane-tree graft
-/

@[expose] public section

namespace Freezing1.PlaneForward

open PlaneTree
open scoped Classical

theorem mem_graft_vertices_left (s t : State) (u : Address) :
    1 :: u ∈ (graft s t).vertices ↔ u ∈ s.vertices := by
  simp only [graft, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨v, hv, he⟩ | ⟨v, _, he⟩)
    · exact List.cons.inj he |>.2 ▸ hv
    · exact (shiftRoot_ne_first v u he).elim
  · intro hu
    exact Or.inl ⟨u, hu, rfl⟩

theorem mem_graft_vertices_right (s t : State) (u : Address) :
    shiftRoot u ∈ (graft s t).vertices ↔ u ∈ t.vertices := by
  simp only [graft, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨v, _, he⟩ | ⟨v, hv, he⟩)
    · exact (shiftRoot_ne_first u v he.symm).elim
    · exact shiftRoot_injective he ▸ hv
  · intro hu
    exact Or.inr ⟨u, hu, rfl⟩

theorem graft_vertices_iff_present {s t : State} (hs : Valid s) (ht : Valid t)
    (u : Address) :
    u ∈ (graft s t).vertices ↔ Present (PlaneTree.graft (shape s) (shape t)) u := by
  cases u with
  | nil =>
    have hm : [] ∈ (graft s t).vertices :=
      (mem_graft_vertices_right s t []).mpr ht.root_mem
    simp only [present_nil, iff_true]
    exact hm
  | cons j u =>
    cases j with
    | zero =>
      rw [show (0 :: u : Address) = shiftRoot (0 :: u) from rfl,
        mem_graft_vertices_right, ht.mem_vertices_iff_present]
      norm_num [shiftRoot, present_cons]
    | succ j =>
      cases j with
      | zero =>
        rw [mem_graft_vertices_left, hs.mem_vertices_iff_present]
        simp [present_cons]
      | succ j =>
        rw [show ((j + 2) :: u : Address) = shiftRoot ((j + 1) :: u) from rfl,
          mem_graft_vertices_right, ht.mem_vertices_iff_present]
        simp only [shiftRoot, present_cons, degree_graft]
        rw [child_succ_graft _ _ (show 1 ≤ j + 1 by omega)]
        have hb : j + 2 ≤ degree (shape t) + 1 ↔ j + 1 ≤ degree (shape t) := by omega
        simp only [show 1 ≤ j + 1 by omega, show 1 ≤ j + 2 by omega,
          true_and, hb]

theorem graft_childCount_eq_graftRaw {s t : State} (hs : Valid s) (ht : Valid t)
    (u : Address) :
    childCount (graft s t) u = (PlaneTree.graft (shape s) (shape t)).val u := by
  cases u with
  | nil =>
    change childCount (graft s t) [] = (shape t).val [] + 1
    rw [graft_childCount_root hs.root_mem, ht.shape_offspring]
  | cons j u =>
    cases j with
    | zero =>
      change childCount (graft s t) (0 :: u) = 0
      have he := graft_childCount_right_nonroot s t (u := 0 :: u) (by simp)
      simp only [shiftRoot] at he
      rw [he]
      exact ht.childCount_canonical.zero_of_absent_child [] 0 (by omega) u
    | succ j =>
      cases j with
      | zero =>
        change childCount (graft s t) (1 :: u) = (shape s).val u
        rw [graft_childCount_left, hs.shape_offspring]
      | succ j =>
        change childCount (graft s t) ((j + 2) :: u) = (shape t).val ((j + 1) :: u)
        rw [ht.shape_offspring]
        exact graft_childCount_right_nonroot s t (u := (j + 1) :: u) (by simp)

theorem Valid.graft {s t : State} (hs : Valid s) (ht : Valid t) : Valid (PlaneForward.graft s t) := by
  constructor
  · exact (mem_graft_vertices_right s t []).mpr ht.root_mem
  · intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      exact (mem_graft_vertices_left s t u).mpr (hs.active_subset hu)
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      exact (mem_graft_vertices_right s t u).mpr (ht.active_subset hu)
  · intro u v huv
    apply (graft_vertices_iff_present hs ht u).mpr
    exact present_of_prefix ⟨v, rfl⟩ ((graft_vertices_iff_present hs ht (u ++ v)).mp huv)
  · intro u hu j
    rw [graft_vertices_iff_present hs ht, present_append_singleton,
      ← graft_childCount_eq_graftRaw hs ht]
    exact and_iff_right ((graft_vertices_iff_present hs ht u).mp hu)

theorem shape_graft_of_valid {s t : State} (hs : Valid s) (ht : Valid t)
    (hg : Valid (graft s t)) :
    shape (graft s t) = PlaneTree.graft (shape s) (shape t) := by
  apply Subtype.ext
  funext u
  rw [hg.shape_offspring]
  cases u with
  | nil =>
    change childCount (graft s t) [] = (shape t).val [] + 1
    rw [graft_childCount_root hs.root_mem, ht.shape_offspring]
  | cons j u =>
    cases j with
    | zero =>
      change childCount (graft s t) (0 :: u) = 0
      exact hg.childCount_canonical.zero_of_absent_child [] 0 (by omega) u
    | succ j =>
      cases j with
      | zero =>
        change childCount (graft s t) (1 :: u) = (shape s).val u
        rw [graft_childCount_left, hs.shape_offspring]
      | succ j =>
        change childCount (graft s t) ((j + 2) :: u) = (shape t).val ((j + 1) :: u)
        rw [ht.shape_offspring]
        exact graft_childCount_right_nonroot s t (u := (j + 1) :: u) (by simp)

theorem shape_graft {s t : State} (hs : Valid s) (ht : Valid t) :
    shape (graft s t) = PlaneTree.graft (shape s) (shape t) :=
  shape_graft_of_valid hs ht (hs.graft ht)

end Freezing1.PlaneForward
