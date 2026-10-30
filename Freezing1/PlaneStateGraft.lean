module

public import Freezing1.PlaneStateUpdates

/-!
# First-child and remainder grafting on genuine finite plane states

The first component is placed below child 1. The other component keeps its
root and shifts positive root-child indices by one. The zero-index convention
keeps the two address ranges disjoint even on raw states.
-/

@[expose] public section

namespace Freezing1.PlaneForward

open PlaneTree
open scoped Classical

def shiftRoot : Address → Address
  | [] => []
  | 0 :: u => 0 :: u
  | (j + 1) :: u => (j + 2) :: u

theorem shiftRoot_injective : Function.Injective shiftRoot := by
  intro u v he
  cases u with
  | nil =>
    cases v with
    | nil => rfl
    | cons j v => cases j <;> simp [shiftRoot] at he
  | cons i u =>
    cases v with
    | nil => cases i <;> simp [shiftRoot] at he
    | cons j v =>
      cases i <;> cases j <;> simp_all [shiftRoot]

theorem shiftRoot_ne_first (u v : Address) : shiftRoot u ≠ 1 :: v := by
  cases u with
  | nil => simp [shiftRoot]
  | cons j u => cases j <;> simp [shiftRoot]

theorem shiftRoot_append {u : Address} (hu : u ≠ []) (w : Address) :
    shiftRoot (u ++ w) = shiftRoot u ++ w := by
  cases u with
  | nil => exact (hu rfl).elim
  | cons j u => cases j <;> rfl

def graft (s t : State) : State where
  vertices := s.vertices.image (List.cons 1) ∪ t.vertices.image shiftRoot
  active := s.active.image (List.cons 1) ∪ t.active.image shiftRoot

theorem graft_images_disjoint (S T : Finset Address) :
    Disjoint (S.image (List.cons 1)) (T.image shiftRoot) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, _, he⟩ := Finset.mem_image.mp hb
  exact shiftRoot_ne_first v u he

theorem graft_active_card (s t : State) :
    (graft s t).active.card = s.active.card + t.active.card := by
  rw [graft, Finset.card_union_of_disjoint (graft_images_disjoint _ _),
    Finset.card_image_of_injective _ (fun _ _ he => (List.cons.inj he).2),
    Finset.card_image_of_injective _ shiftRoot_injective]

theorem mem_graft_active_left (s t : State) (u : Address) :
    1 :: u ∈ (graft s t).active ↔ u ∈ s.active := by
  simp only [graft, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨v, hv, he⟩ | ⟨v, _, he⟩)
    · exact List.cons.inj he |>.2 ▸ hv
    · exact (shiftRoot_ne_first v u he).elim
  · intro hu
    exact Or.inl ⟨u, hu, rfl⟩

theorem mem_graft_active_right (s t : State) (u : Address) :
    shiftRoot u ∈ (graft s t).active ↔ u ∈ t.active := by
  simp only [graft, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨v, _, he⟩ | ⟨v, hv, he⟩)
    · exact (shiftRoot_ne_first u v he.symm).elim
    · exact shiftRoot_injective he ▸ hv
  · intro hu
    exact Or.inr ⟨u, hu, rfl⟩

theorem graft_children_left (s t : State) (u : Address) :
    children (graft s t) (1 :: u) = (children s u).image (List.cons 1) := by
  ext a
  simp only [children, graft, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩ | ⟨v, _, rfl⟩, j, he⟩
    · exact ⟨v, ⟨hv, j, List.cons.inj he |>.2⟩, rfl⟩
    · exact (shiftRoot_ne_first v (u ++ [j]) he).elim
  · rintro ⟨v, ⟨hv, j, he⟩, rfl⟩
    exact ⟨Or.inl ⟨v, hv, rfl⟩, j, congrArg (List.cons 1) he⟩

theorem graft_childCount_left (s t : State) (u : Address) :
    childCount (graft s t) (1 :: u) = childCount s u := by
  rw [childCount, graft_children_left,
    Finset.card_image_of_injective _ (fun _ _ he => (List.cons.inj he).2)]
  rfl

theorem graft_newChild_left (s t : State) (u : Address) :
    newChild (graft s t) (1 :: u) = 1 :: newChild s u := by
  simp only [newChild, graft_childCount_left, List.cons_append]

theorem graft_attach_left (s t : State) (u : Address) :
    attach (graft s t) (1 :: u) = graft (attach s u) t := by
  change ({ vertices := insert (newChild (graft s t) (1 :: u)) (graft s t).vertices
            active := insert (newChild (graft s t) (1 :: u)) (graft s t).active } : State) = _
  rw [graft_newChild_left]
  cases s
  cases t
  simp only [attach, graft, Finset.image_insert, Finset.insert_union]

theorem graft_freeze_left (s t : State) (u : Address) :
    freeze (graft s t) (1 :: u) = graft (freeze s u) t := by
  cases s with
  | mk S A =>
    cases t with
    | mk T B =>
      simp only [freeze, graft, State.mk.injEq, true_and]
      rw [Finset.erase_union_distrib, ← Finset.image_erase (fun _ _ he => (List.cons.inj he).2)]
      congr 1
      apply Finset.erase_eq_of_notMem
      intro hm
      obtain ⟨v, _, he⟩ := Finset.mem_image.mp hm
      exact shiftRoot_ne_first v u he

theorem graft_step_left (s t : State) (sign : Bool) (u : Address) :
    step (graft s t) sign (1 :: u) = graft (step s sign u) t := by
  by_cases hu : u ∈ s.active
  · rw [step, ite_eq_left ((mem_graft_active_left s t u).mpr hu), step, ite_eq_left hu]
    cases sign
    · exact graft_freeze_left s t u
    · exact graft_attach_left s t u
  · rw [step, ite_eq_right ((mem_graft_active_left s t u).not.mpr hu),
      step, ite_eq_right hu]

end Freezing1.PlaneForward
