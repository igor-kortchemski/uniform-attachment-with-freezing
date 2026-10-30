module

public import Freezing1.ForwardPlaneLaw
public import Freezing1.ChronologicalPlaneTree
public import Mathlib.Order.Interval.Finset.Fin

/-!
# The finite chronological projection agrees with ordering the labelled tree

Sibling ranks are the indices in the increasing list of actual child birth
IDs. Thus the finite address representation and the continuous operation of
ordering and erasing labels produce the same plane tree.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical

theorem recordAt_localTreeOfState {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) :
    LocalTree.recordAt (localTreeOfState s) v = some (localRecord s v) := by
  apply (LocalTree.recordAt_eq_some_iff _ _ _).mpr
  refine ⟨⟨s.height v, ?_⟩, rfl⟩
  rw [hs.localTreeOfState_balls]
  exact (localRecord_mem_ball_iff _ _ _).mpr ⟨hv, le_rfl⟩

theorem childIDs_localTreeOfState {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) :
    LocalTree.childIDs (localTreeOfState s) v = birthChildren s v := by
  rw [LocalTree.childIDs, recordAt_localTreeOfState hs hv]
  simp only [hs.localTreeOfState_balls]
  ext w
  constructor
  · intro hw
    obtain ⟨r, hr, hb⟩ := Finset.mem_image.mp hw
    obtain ⟨hr, hr0, hp⟩ := Finset.mem_filter.mp hr
    obtain ⟨u, hu, rfl, _⟩ := (mem_localBall_iff _ _ _).mp hr
    change u = w at hb
    subst u
    change w ≠ 0 at hr0
    exact Finset.mem_filter.mpr ⟨hu, hr0, by simpa [localRecord, hr0] using hp⟩
  · intro hw
    obtain ⟨hw, hw0, hp⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_image.mpr ⟨localRecord s w, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · apply (localRecord_mem_ball_iff _ _ _).mpr
      refine ⟨hw, ?_⟩
      change s.height w ≤ s.height v + 1
      have hh := hs.height_parent w hw hw0
      simpa only [hp] using hh.le
    · exact ⟨hw0, by simpa [localRecord, hw0] using hp⟩

theorem childList_localTreeOfState {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) :
    LocalTree.childList (localTreeOfState s) v = (birthChildren s v).sort (· ≤ ·) := by
  rw [LocalTree.childList, childIDs_localTreeOfState hs hv]

theorem card_filter_le_orderEmb (V : Finset ℕ) (i : Fin V.card) :
    (V.filter (fun w => w ≤ V.orderEmbOfFin rfl i)).card = i.val + 1 := by
  let e := V.orderIsoOfFin rfl
  have he : (Finset.Iic i).image (fun j => (e j).val) =
      V.filter (fun w => w ≤ V.orderEmbOfFin rfl i) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_Iic, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(e j).property, e.monotone hj⟩
    · rintro ⟨hw, hle⟩
      refine ⟨e.symm ⟨w, hw⟩, ?_, ?_⟩
      · apply e.le_iff_le.mp
        rw [e.apply_symm_apply]
        change w ≤ V.orderEmbOfFin rfl i
        exact hle
      · exact congrArg Subtype.val (e.apply_symm_apply ⟨w, hw⟩)
  rw [← he, Finset.card_image_iff.mpr]
  · exact Fin.card_Iic i
  · intro a _ b _ hab
    exact e.injective (Subtype.ext hab)

theorem sorted_getElem?_card_filter_le (V : Finset ℕ) {v : ℕ} (hv : v ∈ V) :
    (V.sort (· ≤ ·))[(V.filter (fun w => w ≤ v)).card - 1]? = some v := by
  let e := V.orderIsoOfFin rfl
  let i : Fin V.card := e.symm ⟨v, hv⟩
  have hi : V.orderEmbOfFin rfl i = v :=
    congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)
  have hc := card_filter_le_orderEmb V i
  rw [hi] at hc
  rw [hc, Nat.add_sub_cancel_right]
  rw [List.getElem?_eq_getElem (by simp)]
  exact congrArg some ((Finset.orderEmbOfFin_apply V rfl i).symm.trans hi)

theorem sorted_getElem?_iff_card_filter_le (V : Finset ℕ) (j w : ℕ) (hj : 0 < j) :
    (V.sort (· ≤ ·))[j - 1]? = some w ↔
      w ∈ V ∧ (V.filter (fun v => v ≤ w)).card = j := by
  constructor
  · intro h
    have hw : w ∈ V := (Finset.mem_sort _).mp (List.mem_of_getElem? h)
    have hr := sorted_getElem?_card_filter_le V hw
    have hidx : j - 1 < (V.sort (· ≤ ·)).length := by
      exact (List.getElem?_eq_some_iff.mp h).choose
    have he : j - 1 = (V.filter (fun v => v ≤ w)).card - 1 :=
      ((Finset.sort_nodup V (· ≤ ·)).getElem?_inj hidx).mp (h.trans hr.symm)
    have hp : 0 < (V.filter (fun v => v ≤ w)).card :=
      Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, le_rfl⟩⟩
    exact ⟨hw, by omega⟩
  · rintro ⟨hw, hr⟩
    simpa only [hr] using sorted_getElem?_card_filter_le V hw

theorem childRank_eq_filter_children {s : State} {v w : ℕ} (hp : s.parent w = v) :
    childRank s w = ((birthChildren s v).filter (fun u => u ≤ w)).card := by
  unfold childRank birthChildren
  congr 1
  ext u
  simp only [Finset.mem_filter, hp, and_assoc]

theorem childList_getElem?_iff {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) (j w : ℕ) (hj : 0 < j) :
    (LocalTree.childList (localTreeOfState s) v)[j - 1]? = some w ↔
      w ∈ s.vertices ∧ w ≠ 0 ∧ s.parent w = v ∧ childRank s w = j := by
  rw [childList_localTreeOfState hs hv, sorted_getElem?_iff_card_filter_le _ j w hj]
  constructor
  · rintro ⟨hw, hr⟩
    obtain ⟨hw, hw0, hp⟩ := Finset.mem_filter.mp hw
    exact ⟨hw, hw0, hp, (childRank_eq_filter_children hp).trans hr⟩
  · rintro ⟨hw, hw0, hp, hr⟩
    exact ⟨Finset.mem_filter.mpr ⟨hw, hw0, hp⟩, (childRank_eq_filter_children hp).symm.trans hr⟩

theorem follow_planeAddress {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) :
    LocalTree.follow (localTreeOfState s) 0 (planeAddress s v) = some v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases hv0 : v = 0
    · subst v
      simp [planeAddress_zero, LocalTree.follow]
    · rw [hs.planeAddress_nonroot hv hv0, LocalTree.follow_append,
        ih (s.parent v) (hs.parent_lt v hv hv0) (hs.parent_mem v hv)]
      have hp := childRank_pos hv hv0
      have hg := (childList_getElem?_iff hs (hs.parent_mem v hv) (childRank s v) v hp).mpr
        ⟨hv, hv0, rfl, rfl⟩
      simp [LocalTree.follow, Nat.ne_of_gt hp, hg]

theorem follow_eq_some_data {n : ℕ} {s : State} (hs : ValidAt n s)
    {a : ℕ} (ha : a ∈ s.vertices) {u : PlaneTree.Address} {v : ℕ}
    (h : LocalTree.follow (localTreeOfState s) a u = some v) :
    v ∈ s.vertices ∧ planeAddress s v = planeAddress s a ++ u := by
  induction u generalizing a with
  | nil =>
    have he : a = v := Option.some.inj h
    subst v
    exact ⟨ha, by simp⟩
  | cons j u ih =>
    by_cases hj : j = 0
    · simp [LocalTree.follow, hj] at h
    · cases hg : (LocalTree.childList (localTreeOfState s) a)[j - 1]? with
      | none => simp [LocalTree.follow, hj, hg] at h
      | some w =>
        have hd := (childList_getElem?_iff hs ha j w (by omega)).mp hg
        have hf : LocalTree.follow (localTreeOfState s) w u = some v := by
          simpa [LocalTree.follow, hj, hg] using h
        obtain ⟨hv, hvaddr⟩ := ih hd.1 hf
        refine ⟨hv, ?_⟩
        rw [hvaddr, (planeAddress_child_iff hs ha hd.1 j).mpr hd.2,
          List.append_assoc, List.singleton_append]

theorem shape_toPlaneState_eq_toPlaneTree {n : ℕ} {s : State} (hs : ValidAt n s)
    (hp : PlaneForward.Valid s.toPlaneState) :
    PlaneForward.shape s.toPlaneState = LocalTree.toPlaneTree (localTreeOfState s) := by
  apply Subtype.ext
  funext u
  rw [hp.shape_offspring]
  change PlaneForward.childCount s.toPlaneState u =
    LocalTree.planeOffspring (localTreeOfState s) u
  unfold LocalTree.planeOffspring
  cases hf : LocalTree.follow (localTreeOfState s) 0 u with
  | none =>
    apply hp.childCount_zero_of_not_mem
    intro hu
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hu
    have hh := follow_planeAddress hs hv
    rw [he, hf] at hh
    contradiction
  | some v =>
    change PlaneForward.childCount s.toPlaneState u =
      (LocalTree.childIDs (localTreeOfState s) v).card
    obtain ⟨hv, he⟩ := follow_eq_some_data hs hs.root_mem hf
    simp only [planeAddress_zero, List.nil_append] at he
    rw [← he, toPlaneState_childCount hs hv, childIDs_localTreeOfState hs hv]

end Freezing1.Forward

namespace Freezing1.ForwardAnnealed

open Forward MeasureTheory

theorem fullLaw_shape_eq_toPlaneTree (p : unitInterval) :
    ∀ᵐ H ∂fullLaw p, ∀ n,
      PlaneForward.shape (H n).toPlaneState =
        LocalTree.toPlaneTree (localTreeOfState (H n)) := by
  filter_upwards [fullLaw_valid p, fullLaw_toPlaneState_valid p] with H hv hp
  exact fun n => shape_toPlaneState_eq_toPlaneTree (hv n) (hp n)

theorem treeLaw_shape_eq_toPlaneTree (p : unitInterval) (n : ℕ) :
    ∀ᵐ s ∂treeLaw p n,
      PlaneForward.shape s.toPlaneState = LocalTree.toPlaneTree (localTreeOfState s) := by
  filter_upwards [treeLaw_valid p n, treeLaw_toPlaneState_valid p n] with s hv hp
  exact shape_toPlaneState_eq_toPlaneTree hv hp

theorem map_treeLaw_toPlaneTree (p : unitInterval) (n : ℕ) :
    (treeLaw p n).map (fun s => LocalTree.toPlaneTree (localTreeOfState s)) =
      (PlaneForward.fullLaw p PlaneForward.initial).map (fun H => PlaneForward.shape (H n)) := by
  have hm : Measurable PlaneForward.shape := measurable_of_countable _
  calc
    _ = ((treeLaw p n).map State.toPlaneState).map PlaneForward.shape := by
      rw [Measure.map_map hm measurable_toPlaneState]
      apply Measure.map_congr
      filter_upwards [treeLaw_shape_eq_toPlaneTree p n] with s hs
      exact hs.symm
    _ = _ := by
      rw [map_treeLaw_toPlaneState, Measure.map_map hm (measurable_pi_apply n)]
      rfl

end Freezing1.ForwardAnnealed
