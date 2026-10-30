module

public import Freezing1.InterleavedChainExtraction
public import Mathlib.Data.List.OfFn
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Selection ranks and the finite observed words

These deterministic lemmas identify the source's successive minimum times
with the entries of the actual finite observation list. Repeated fallback
times are retained when a side stops being selected.
-/

@[expose] public section

namespace Freezing1.InterleavedChain

open scoped Classical

noncomputable def selectionCount (marks : ℕ → Bool) (side : Bool) (n : ℕ) : ℕ :=
  ((Finset.Ioc 0 n).filter (fun i => marks i = side)).card

@[simp] theorem selectionCount_zero (marks : ℕ → Bool) (side : Bool) :
    selectionCount marks side 0 = 0 := by simp [selectionCount]

theorem selectionCount_split (marks : ℕ → Bool) (side : Bool) {a b : ℕ} (hab : a ≤ b) :
    selectionCount marks side b = selectionCount marks side a +
      ((Finset.Ioc a b).filter (fun i => marks i = side)).card := by
  unfold selectionCount
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hab, Finset.filter_union,
    Finset.card_union_of_disjoint]
  exact (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (d := b) le_rfl).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem selectionCount_mono (marks : ℕ → Bool) (side : Bool) :
    Monotone (selectionCount marks side) := by
  intro a b hab
  rw [selectionCount_split marks side hab]
  omega

theorem selectionCount_succ (marks : ℕ → Bool) (side : Bool) (n : ℕ) :
    selectionCount marks side (n + 1) = selectionCount marks side n +
      if marks (n + 1) = side then 1 else 0 := by
  rw [selectionCount_split marks side n.le_succ, Nat.Ioc_succ_singleton]
  by_cases h : marks (n + 1) = side <;> simp [Finset.filter_singleton, h]

theorem exists_selection_of_count_lt (marks : ℕ → Bool) (side : Bool)
    {a b : ℕ} (hab : a ≤ b)
    (h : selectionCount marks side a < selectionCount marks side b) :
    ∃ m, a < m ∧ m ≤ b ∧ marks m = side := by
  rw [selectionCount_split marks side hab] at h
  have hn : ((Finset.Ioc a b).filter (fun i => marks i = side)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨m, hm⟩ := hn
  exact ⟨m, (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1,
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).2, (Finset.mem_filter.mp hm).2⟩

theorem selectionCount_strict_of_marked (marks : ℕ → Bool) (side : Bool)
    {a b : ℕ} (hab : a < b) (hb : marks b = side) :
    selectionCount marks side a < selectionCount marks side b := by
  rw [selectionCount_split marks side hab.le]
  have hn : 0 < ((Finset.Ioc a b).filter (fun i => marks i = side)).card :=
    Finset.card_pos.mpr ⟨b, by simp [hab, hb]⟩
  omega

theorem selectionCount_nextTime (marks : ℕ → Bool) (side : Bool) (a : ℕ)
    (h : ∃ n, a < n ∧ marks n = side) :
    selectionCount marks side (nextTime marks side a) = selectionCount marks side a + 1 := by
  obtain ⟨ha, hm, hmin⟩ := nextTime_of_exists marks side a h
  rw [selectionCount_split marks side ha.le]
  have he : (Finset.Ioc a (nextTime marks side a)).filter (fun i => marks i = side) =
      {nextTime marks side a} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨ham, hmn⟩, hmark⟩
      exact le_antisymm hmn (le_of_not_gt (fun hh => hmin m ham hh hmark))
    · rintro rfl
      exact ⟨⟨ha, le_rfl⟩, hm⟩
  simp [he]

/-- Every rank already observed at horizon N has its correct count and a
selection time at most N. This excludes fallback for those positive ranks. -/
theorem selectedTime_rank (marks : ℕ → Bool) (side : Bool) {k N : ℕ}
    (hk : k ≤ selectionCount marks side N) :
    selectedTime marks side k ≤ N ∧
      selectionCount marks side (selectedTime marks side k) = k := by
  induction k with
  | zero => simp [selectedTime]
  | succ k ih =>
    obtain ⟨ht, hc⟩ := ih (by omega)
    obtain ⟨m, hm, hmN, hmark⟩ := exists_selection_of_count_lt marks side ht (by omega)
    have hex : ∃ m, selectedTime marks side k < m ∧ marks m = side := ⟨m, hm, hmark⟩
    refine ⟨?_, ?_⟩
    · exact (Nat.find_min' (nextCandidate_exists marks side _) (Or.inl ⟨hm, hmark⟩)).trans hmN
    · change selectionCount marks side (nextTime marks side _) = k + 1
      rw [selectionCount_nextTime marks side _ hex, hc]

theorem selectedTime_count_eq (marks : ℕ → Bool) (side : Bool) {n : ℕ}
    (_hn : 0 < n) (hm : marks n = side) :
    selectedTime marks side (selectionCount marks side n) = n := by
  obtain ⟨ht, hc⟩ := selectedTime_rank marks side (k := selectionCount marks side n)
    (N := n) le_rfl
  apply le_antisymm ht
  by_contra hnot
  have hh := selectionCount_strict_of_marked marks side (Nat.lt_of_not_ge hnot) hm
  omega

/-- The literal finite list of states seen when a side is selected. -/
def collect {D : Type*} (marks : ℕ → Bool) (values : ℕ → D) (side : Bool) : ℕ → List D
  | 0 => []
  | n + 1 => if marks (n + 1) = side then collect marks values side n ++ [values (n + 1)]
      else collect marks values side n

theorem collect_eq_ofFn {D : Type*} (marks : ℕ → Bool) (values : ℕ → D)
    (side : Bool) (n : ℕ) :
    collect marks values side n = List.ofFn (fun i : Fin (selectionCount marks side n) =>
      values (selectedTime marks side (i.val + 1))) := by
  induction n with
  | zero => simp [collect]
  | succ n ih =>
    by_cases hm : marks (n + 1) = side
    · have ht := selectedTime_count_eq marks side (Nat.zero_lt_succ n) hm
      rw [selectionCount_succ, ite_eq_left hm] at ht
      simp only [collect, ih, selectionCount_succ, ite_eq_left hm,
        List.ofFn_succ', Fin.val_cast, Fin.val_castSucc, Fin.val_last, ht, List.concat_eq_append]
    · simp only [collect, ih, selectionCount_succ, ite_eq_right hm, Nat.add_zero, Fin.val_cast]

theorem nextTime_of_count_bounded (marks : ℕ → Bool) (side : Bool) (a : ℕ)
    (h : ∀ n, selectionCount marks side n ≤ selectionCount marks side a) :
    nextTime marks side a = a := by
  apply nextTime_of_none
  intro m ham hm
  have hh := selectionCount_strict_of_marked marks side ham hm
  exact (not_lt_of_ge (h m)) hh

theorem selectedTime_stable (marks : ℕ → Bool) (side : Bool) {k a : ℕ}
    (hk : selectedTime marks side k = a) (ha : nextTime marks side a = a)
    {j : ℕ} (hkj : k ≤ j) : selectedTime marks side j = a := by
  induction j, hkj using Nat.le_induction with
  | base => exact hk
  | succ j hj ih => simpa only [selectedTime, ih] using ha

/-- Once the requested rank lies within the current horizon, either it has
actually been observed or there can be no further selections at all. -/
theorem count_ge_or_globally_bounded (marks : ℕ → Bool) (side : Bool) {r N : ℕ}
    (h : selectedTime marks side r ≤ N) :
    r ≤ selectionCount marks side N ∨
      ∀ m, selectionCount marks side m ≤ selectionCount marks side N := by
  by_cases hr : r ≤ selectionCount marks side N
  · exact Or.inl hr
  · right
    intro m
    by_contra hm
    let k := min r (selectionCount marks side m)
    have hk : selectionCount marks side N < k := by omega
    obtain ⟨_, hcount⟩ := selectedTime_rank marks side (k := k) (N := m) (min_le_right _ _)
    have htime : selectedTime marks side k ≤ N :=
      ((selectedTime_mono marks side) (min_le_left _ _)).trans h
    have hmono := selectionCount_mono marks side htime
    omega


@[simp] theorem length_collect {D : Type*} (marks : ℕ → Bool) (values : ℕ → D)
    (side : Bool) (n : ℕ) :
    (collect marks values side n).length = selectionCount marks side n := by
  rw [collect_eq_ofFn, List.length_ofFn]

/-- The last observation is the state at the last actual selection, and at
time zero when no selection has occurred. -/
theorem getLastD_collect {D : Type*} (marks : ℕ → Bool) (values : ℕ → D)
    (side : Bool) (n : ℕ) :
    (collect marks values side n).getLastD (values 0) =
      values (selectedTime marks side (selectionCount marks side n)) := by
  rw [collect_eq_ofFn]
  cases hc : selectionCount marks side n with
  | zero => simp [selectedTime]
  | succ k =>
    rw [List.ofFn_succ', List.concat_eq_append, List.getLastD_concat]
    rfl


end Freezing1.InterleavedChain
