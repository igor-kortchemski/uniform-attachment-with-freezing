module

public import Freezing1.PlaneStateGraft

/-!
# Updates in the remainder component of a first-child graft
-/

@[expose] public section

namespace Freezing1.PlaneForward

open PlaneTree
open scoped Classical

theorem shiftRoot_length (u : Address) : (shiftRoot u).length = u.length := by
  cases u with
  | nil => rfl
  | cons j u => cases j <;> rfl

theorem singleton_child_iff_length (u : Address) :
    (∃ j : ℕ, u = [j]) ↔ u.length = 1 := by
  constructor
  · rintro ⟨j, rfl⟩
    rfl
  · intro h
    cases u with
    | nil => simp at h
    | cons j u =>
      have hu : u = [] := List.length_eq_zero_iff.mp (by simpa using h)
      exact ⟨j, by rw [hu]⟩

theorem graft_children_root {s : State} (hs : [] ∈ s.vertices) (t : State) :
    children (graft s t) [] = insert [1] ((children t []).image shiftRoot) := by
  ext a
  simp only [children, graft, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    Finset.mem_insert, List.nil_append]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩, j, he⟩
    · have hv0 : v = [] := by
        have hh := congrArg List.length he
        simp only [List.length_cons, List.length_nil] at hh
        exact List.length_eq_zero_iff.mp (by omega)
      exact Or.inl (by rw [hv0])
    · refine Or.inr ⟨v, ⟨hv, ?_⟩, rfl⟩
      apply (singleton_child_iff_length v).mpr
      rw [← shiftRoot_length, he]
      rfl
  · rintro (rfl | ⟨v, ⟨hv, j, he⟩, rfl⟩)
    · exact ⟨Or.inl ⟨[], hs, rfl⟩, 1, rfl⟩
    · refine ⟨Or.inr ⟨v, hv, rfl⟩, ?_⟩
      apply (singleton_child_iff_length _).mpr
      rw [shiftRoot_length, he]
      rfl

theorem graft_childCount_root {s : State} (hs : [] ∈ s.vertices) (t : State) :
    childCount (graft s t) [] = childCount t [] + 1 := by
  rw [childCount, graft_children_root hs, Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _ shiftRoot_injective]
    rfl
  · intro hm
    obtain ⟨u, _, he⟩ := Finset.mem_image.mp hm
    exact shiftRoot_ne_first u [] he

theorem graft_children_right_nonroot (s t : State) {u : Address} (hu : u ≠ []) :
    children (graft s t) (shiftRoot u) = (children t u).image shiftRoot := by
  ext a
  simp only [children, graft, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨⟨v, _, rfl⟩ | ⟨v, hv, rfl⟩, j, he⟩
    · have hshift : shiftRoot (u ++ [j]) = 1 :: v := by
        rw [shiftRoot_append hu]
        exact he.symm
      exact (shiftRoot_ne_first (u ++ [j]) v hshift).elim
    · have he' : v = u ++ [j] := shiftRoot_injective (by
        rw [shiftRoot_append hu]
        exact he)
      exact ⟨v, ⟨hv, j, he'⟩, rfl⟩
  · rintro ⟨v, ⟨hv, j, he⟩, rfl⟩
    exact ⟨Or.inr ⟨v, hv, rfl⟩, j, by rw [he, shiftRoot_append hu]⟩

theorem graft_childCount_right_nonroot (s t : State) {u : Address} (hu : u ≠ []) :
    childCount (graft s t) (shiftRoot u) = childCount t u := by
  rw [childCount, graft_children_right_nonroot s t hu,
    Finset.card_image_of_injective _ shiftRoot_injective]
  rfl

theorem graft_newChild_right {s : State} (hs : [] ∈ s.vertices) (t : State) (u : Address) :
    newChild (graft s t) (shiftRoot u) = shiftRoot (newChild t u) := by
  by_cases hu : u = []
  · subst u
    simp only [shiftRoot, newChild, List.nil_append, graft_childCount_root hs]
  · simp only [newChild, graft_childCount_right_nonroot s t hu,
      shiftRoot_append hu]

theorem graft_attach_right {s : State} (hs : [] ∈ s.vertices) (t : State) (u : Address) :
    attach (graft s t) (shiftRoot u) = graft s (attach t u) := by
  change ({ vertices := insert (newChild (graft s t) (shiftRoot u)) (graft s t).vertices
            active := insert (newChild (graft s t) (shiftRoot u)) (graft s t).active } : State) = _
  rw [graft_newChild_right hs]
  cases s
  cases t
  simp only [attach, graft, Finset.image_insert, Finset.union_insert]

theorem graft_freeze_right (s t : State) (u : Address) :
    freeze (graft s t) (shiftRoot u) = graft s (freeze t u) := by
  cases s with
  | mk S A =>
    cases t with
    | mk T B =>
      simp only [freeze, graft, State.mk.injEq, true_and]
      rw [Finset.erase_union_distrib, ← Finset.image_erase shiftRoot_injective]
      congr 1
      apply Finset.erase_eq_of_notMem
      intro hm
      obtain ⟨v, _, he⟩ := Finset.mem_image.mp hm
      exact shiftRoot_ne_first u v he.symm

theorem graft_step_right {s : State} (hs : [] ∈ s.vertices) (t : State)
    (sign : Bool) (u : Address) :
    step (graft s t) sign (shiftRoot u) = graft s (step t sign u) := by
  by_cases hu : u ∈ t.active
  · rw [step, ite_eq_left ((mem_graft_active_right s t u).mpr hu), step, ite_eq_left hu]
    cases sign
    · exact graft_freeze_right s t u
    · exact graft_attach_right hs t u
  · rw [step, ite_eq_right ((mem_graft_active_right s t u).not.mpr hu),
      step, ite_eq_right hu]

end Freezing1.PlaneForward
