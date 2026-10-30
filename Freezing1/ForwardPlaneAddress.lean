module

public import Freezing1.ForwardTree
public import Freezing1.PlaneStateUpdates

/-!
# Chronological addresses for the actual finite forward tree

The index of a child is its rank among siblings in increasing birth order.
The guarded recursion is total on raw states, and its characterizations are
proved on the actual valid states. No tree or branching property is assumed
for the resulting stochastic process.
-/

@[expose] public section

@[ext] theorem Freezing1.PlaneForward.State.ext {s t : Freezing1.PlaneForward.State}
    (hv : s.vertices = t.vertices) (ha : s.active = t.active) : s = t := by
  cases s
  cases t
  simp_all

namespace Freezing1.Forward

open scoped Classical

noncomputable def childRank (s : State) (v : ℕ) : ℕ :=
  (s.vertices.filter (fun w => w ≠ 0 ∧ s.parent w = s.parent v ∧ w ≤ v)).card

theorem childRank_pos {s : State} {v : ℕ} (hv : v ∈ s.vertices) (hv0 : v ≠ 0) :
    0 < childRank s v := by
  apply Finset.card_pos.mpr
  exact ⟨v, Finset.mem_filter.mpr ⟨hv, hv0, rfl, le_rfl⟩⟩

theorem childRank_lt {s : State} {u v : ℕ} (hv : v ∈ s.vertices) (hv0 : v ≠ 0)
    (hpar : s.parent u = s.parent v) (huv : u < v) :
    childRank s u < childRank s v := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro w hw
    obtain ⟨hw, hw0, hp, hwu⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hw, hw0, hp.trans hpar, hwu.trans huv.le⟩
  · intro he
    have hm : v ∈ s.vertices.filter
        (fun w => w ≠ 0 ∧ s.parent w = s.parent v ∧ w ≤ v) :=
      Finset.mem_filter.mpr ⟨hv, hv0, rfl, le_rfl⟩
    rw [← he] at hm
    have := (Finset.mem_filter.mp hm).2.2.2
    omega

theorem eq_of_childRank_eq {s : State} {u v : ℕ}
    (hu : u ∈ s.vertices) (hv : v ∈ s.vertices) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hp : s.parent u = s.parent v) (hr : childRank s u = childRank s v) : u = v := by
  rcases lt_trichotomy u v with huv | he | hvu
  · have := childRank_lt hv hv0 hp huv
    omega
  · exact he
  · have := childRank_lt hu hu0 hp.symm hvu
    omega

noncomputable def planeAddress (s : State) (v : ℕ) : PlaneTree.Address :=
  if v = 0 then [] else
    if h : s.parent v < v then planeAddress s (s.parent v) ++ [childRank s v] else []
termination_by v

@[simp] theorem planeAddress_zero (s : State) : planeAddress s 0 = [] := by
  rw [planeAddress, if_pos rfl]

theorem ValidAt.planeAddress_nonroot {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) (hv0 : v ≠ 0) :
    planeAddress s v = planeAddress s (s.parent v) ++ [childRank s v] := by
  rw [planeAddress, if_neg hv0, dif_pos (hs.parent_lt v hv hv0)]

theorem ValidAt.planeAddress_eq_nil_iff {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) : planeAddress s v = [] ↔ v = 0 := by
  constructor
  · intro he
    by_contra hv0
    rw [hs.planeAddress_nonroot hv hv0] at he
    have := congrArg List.length he
    simp only [List.length_append, List.length_singleton, List.length_nil] at this
    omega
  · rintro rfl
    exact planeAddress_zero s

theorem ValidAt.planeAddress_injective {n : ℕ} {s : State} (hs : ValidAt n s) :
    Set.InjOn (planeAddress s) (s.vertices : Set ℕ) := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro hu v hv he
    by_cases hu0 : u = 0
    · subst u
      exact ((hs.planeAddress_eq_nil_iff hv).mp (he.symm.trans (planeAddress_zero s))).symm
    · have hv0 : v ≠ 0 := by
        intro hv0
        subst v
        exact hu0 ((hs.planeAddress_eq_nil_iff hu).mp (he.trans (planeAddress_zero s)))
      rw [hs.planeAddress_nonroot hu hu0, hs.planeAddress_nonroot hv hv0] at he
      obtain ⟨hp, hr⟩ := List.append_singleton_inj.mp he
      have hpar := ih (s.parent u) (hs.parent_lt u hu hu0)
        (hs.parent_mem u hu) (hs.parent_mem v hv) hp
      exact eq_of_childRank_eq hu hv hu0 hv0 hpar hr

theorem ValidAt.planeAddress_length {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) : (planeAddress s v).length = s.height v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases hv0 : v = 0
    · subst v
      rw [planeAddress_zero, List.length_nil, hs.height_root]
    · rw [hs.planeAddress_nonroot hv hv0, List.length_append, List.length_singleton,
        ih (s.parent v) (hs.parent_lt v hv hv0) (hs.parent_mem v hv),
        hs.height_parent v hv hv0]

theorem childRank_freeze (s : State) (t u v : ℕ) :
    childRank (freeze s t u) v = childRank s v := rfl

theorem planeAddress_freeze (s : State) (t u v : ℕ) :
    planeAddress (freeze s t u) v = planeAddress s v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases hv : v = 0
    · subst v
      rw [planeAddress_zero, planeAddress_zero]
    · conv_lhs => rw [planeAddress]
      conv_rhs => rw [planeAddress]
      simp only [ite_eq_right hv]
      by_cases hp : s.parent v < v
      · have hp' : (freeze s t u).parent v < v := hp
        rw [dif_pos hp', dif_pos hp, childRank_freeze]
        exact congrArg (fun a => a ++ [childRank s v]) (ih (s.parent v) hp)
      · have hp' : ¬(freeze s t u).parent v < v := hp
        rw [dif_neg hp', dif_neg hp]

noncomputable def State.toPlaneState (s : State) : PlaneForward.State where
  vertices := s.vertices.image (planeAddress s)
  active := s.active.image (planeAddress s)

theorem toPlaneState_initial : initial.toPlaneState = PlaneForward.initial := by
  apply PlaneForward.State.ext <;> simp [State.toPlaneState, initial,
    PlaneForward.initial, planeAddress_zero]

theorem toPlaneState_freeze {n : ℕ} {s : State} (hs : ValidAt n s)
    (t : ℕ) {u : ℕ} (hu : u ∈ s.active) :
    (freeze s t u).toPlaneState = PlaneForward.freeze s.toPlaneState (planeAddress s u) := by
  apply PlaneForward.State.ext
  · simp only [State.toPlaneState, freeze, PlaneForward.freeze]
    congr 1
    funext v
    exact planeAddress_freeze s t u v
  · change (s.active.erase u).image (planeAddress (freeze s t u)) =
      (s.active.image (planeAddress s)).erase (planeAddress s u)
    have he : planeAddress (freeze s t u) = planeAddress s := funext (planeAddress_freeze s t u)
    rw [he]
    ext a
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨v, ⟨hvu, hv⟩, rfl⟩
      refine ⟨?_, v, hv, rfl⟩
      intro heq
      exact hvu (hs.planeAddress_injective (hs.active_subset hv) (hs.active_subset hu) heq)
    · rintro ⟨ha, v, hv, rfl⟩
      exact ⟨v, ⟨fun heq => ha (heq ▸ rfl), hv⟩, rfl⟩

end Freezing1.Forward
