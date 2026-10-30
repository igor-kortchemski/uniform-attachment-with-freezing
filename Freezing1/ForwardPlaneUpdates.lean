module

public import Freezing1.ForwardPlaneAddress

/-!
# The actual forward transitions commute with chronological projection
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

theorem childRank_attach_old {n : ℕ} {s : State} (hs : ValidAt n s)
    (v : ℕ) {w : ℕ} (hw : w ∈ s.vertices) :
    childRank (attach s (n + 1) v) w = childRank s w := by
  unfold childRank
  congr 1
  ext a
  have hwn : w ≠ n + 1 := by have := hs.vertices_le w hw; omega
  by_cases han : a = n + 1
  · subst a
    have hnot : ¬n + 1 ≤ w := by have := hs.vertices_le w hw; omega
    have hnotmem : n + 1 ∉ s.vertices := by
      intro hm
      have := hs.vertices_le _ hm
      omega
    simp [attach, hwn, hnot, hnotmem]
  · simp [attach, hwn, han]

theorem planeAddress_attach_old {n : ℕ} {s : State} (hs : ValidAt n s)
    (v : ℕ) {w : ℕ} (hw : w ∈ s.vertices) :
    planeAddress (attach s (n + 1) v) w = planeAddress s w := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
    by_cases hw0 : w = 0
    · subst w
      rw [planeAddress_zero, planeAddress_zero]
    · have hwn : w ≠ n + 1 := by have := hs.vertices_le w hw; omega
      have hp : (attach s (n + 1) v).parent w = s.parent w := by simp [attach, hwn]
      have hlt : (attach s (n + 1) v).parent w < w := hp ▸ hs.parent_lt w hw hw0
      conv_lhs => rw [planeAddress]
      rw [ite_eq_right hw0, dite_eq_left hlt, childRank_attach_old hs v hw]
      rw [hp, ih (s.parent w) (hs.parent_lt w hw hw0) (hs.parent_mem w hw),
        hs.planeAddress_nonroot hw hw0]

noncomputable def birthChildren (s : State) (v : ℕ) : Finset ℕ :=
  s.vertices.filter (fun w => w ≠ 0 ∧ s.parent w = v)

theorem planeAddress_child_iff {n : ℕ} {s : State} (hs : ValidAt n s)
    {v w : ℕ} (hv : v ∈ s.vertices) (hw : w ∈ s.vertices) (j : ℕ) :
    planeAddress s w = planeAddress s v ++ [j] ↔
      w ≠ 0 ∧ s.parent w = v ∧ childRank s w = j := by
  constructor
  · intro he
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, planeAddress_zero] at he
      have := congrArg List.length he
      simp only [List.length_nil, List.length_append, List.length_singleton] at this
      omega
    rw [hs.planeAddress_nonroot hw hw0] at he
    obtain ⟨hp, hr⟩ := List.append_singleton_inj.mp he
    exact ⟨hw0, hs.planeAddress_injective (hs.parent_mem w hw) hv hp, hr⟩
  · rintro ⟨hw0, hp, hr⟩
    rw [hs.planeAddress_nonroot hw hw0, hp, hr]

theorem toPlaneState_children {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) :
    PlaneForward.children s.toPlaneState (planeAddress s v) =
      (birthChildren s v).image (planeAddress s) := by
  ext a
  simp only [PlaneForward.children, State.toPlaneState, Finset.mem_filter,
    Finset.mem_image, birthChildren]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, j, hj⟩
    obtain ⟨hw0, hp, _⟩ := (planeAddress_child_iff hs hv hw j).mp hj
    exact ⟨w, ⟨hw, hw0, hp⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hw, hw0, hp⟩ := hw
    exact ⟨⟨w, hw, rfl⟩, childRank s w,
      (planeAddress_child_iff hs hv hw _).mpr ⟨hw0, hp, rfl⟩⟩

theorem toPlaneState_childCount {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) :
    PlaneForward.childCount s.toPlaneState (planeAddress s v) = (birthChildren s v).card := by
  rw [PlaneForward.childCount, toPlaneState_children hs hv]
  apply Finset.card_image_iff.mpr
  intro u hu w hw he
  exact hs.planeAddress_injective (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hw).1 he

theorem childRank_attach_new {n : ℕ} {s : State} (hs : ValidAt n s) (v : ℕ) :
    childRank (attach s (n + 1) v) (n + 1) = (birthChildren s v).card + 1 := by
  have hfresh : n + 1 ∉ s.vertices := by
    intro hm
    have := hs.vertices_le _ hm
    omega
  have he : (attach s (n + 1) v).vertices.filter
      (fun w => w ≠ 0 ∧ (attach s (n + 1) v).parent w =
        (attach s (n + 1) v).parent (n + 1) ∧ w ≤ n + 1) =
      insert (n + 1) (birthChildren s v) := by
    ext w
    by_cases hwn : w = n + 1
    · subst w
      simp [attach]
    · by_cases hw : w ∈ s.vertices
      · have hle := (hs.vertices_le w hw).trans (Nat.le_succ n)
        simp [attach, birthChildren, hwn, hw, hle]
      · simp [attach, birthChildren, hwn, hw]
  unfold childRank
  rw [he, Finset.card_insert_of_notMem]
  intro hm
  exact hfresh (Finset.mem_filter.mp hm).1

theorem planeAddress_attach_new {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.active) :
    planeAddress (attach s (n + 1) v) (n + 1) =
      PlaneForward.newChild s.toPlaneState (planeAddress s v) := by
  rw [(hs.attach hv).planeAddress_nonroot (Finset.mem_insert_self _ _) (by omega)]
  have hp : (attach s (n + 1) v).parent (n + 1) = v := by simp [attach]
  rw [hp, planeAddress_attach_old hs v (hs.active_subset hv), childRank_attach_new hs]
  rw [PlaneForward.newChild, toPlaneState_childCount hs (hs.active_subset hv)]

theorem toPlaneState_attach {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.active) :
    (attach s (n + 1) v).toPlaneState =
      PlaneForward.attach s.toPlaneState (planeAddress s v) := by
  apply PlaneForward.State.ext
  · change (insert (n + 1) s.vertices).image (planeAddress (attach s (n + 1) v)) = _
    rw [Finset.image_insert, planeAddress_attach_new hs hv]
    congr 1
    apply Finset.image_congr
    intro w hw
    exact planeAddress_attach_old hs v hw
  · change (insert (n + 1) s.active).image (planeAddress (attach s (n + 1) v)) = _
    rw [Finset.image_insert, planeAddress_attach_new hs hv]
    congr 1
    apply Finset.image_congr
    intro w hw
    exact planeAddress_attach_old hs v (hs.active_subset hw)

theorem mem_toPlaneState_active {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) :
    planeAddress s v ∈ s.toPlaneState.active ↔ v ∈ s.active := by
  constructor
  · rintro h
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
    exact (hs.planeAddress_injective (hs.active_subset hw) hv he) ▸ hw
  · exact fun h => Finset.mem_image_of_mem _ h

theorem toPlaneState_step {n : ℕ} {s : State} (hs : ValidAt n s)
    (sign : Bool) {v : ℕ} (hv : v ∈ s.vertices) :
    (step s (n + 1) sign v).toPlaneState =
      PlaneForward.step s.toPlaneState sign (planeAddress s v) := by
  by_cases ha : v ∈ s.active
  · have ha' := (mem_toPlaneState_active hs hv).mpr ha
    rw [step, ite_eq_left ha, PlaneForward.step, ite_eq_left ha']
    cases sign
    · exact toPlaneState_freeze hs _ ha
    · exact toPlaneState_attach hs ha
  · have ha' := (mem_toPlaneState_active hs hv).not.mpr ha
    simp only [step, ite_eq_right ha, PlaneForward.step, ite_eq_right ha']

end Freezing1.Forward
