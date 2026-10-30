module

public import Freezing1.ForwardBlockHeightAncestor
public import Freezing1.ForwardTruncationLaw

/-! Actual parent paths and graph distances between time-cut ancestors. -/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

set_option backward.isDefEq.respectTransparency false

/-- The computed cut ancestor is reached by exactly the recorded cut height
many actual parent edges. -/
theorem ValidAt.cutAncestor_path_data {n : ℕ} {s : State} (hs : ValidAt n s)
    (a : ℕ) {v : ℕ} (hv : v ∈ s.vertices) :
    cutAncestor s a v ∈ s.vertices ∧ cutAncestor s a v ≤ a ∧
      (s.parent^[cutHeight s a v]) v = cutAncestor s a v ∧
      s.height v = s.height (cutAncestor s a v) + cutHeight s a v ∧
      ∃ p : s.graph.Walk (cutAncestor s a v) v, p.length = cutHeight s a v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases hva : v ≤ a
    · rw [cutAncestor_of_le s a v hva,
        show cutHeight s a v = 0 from cutHeightAux_eq_zero_of_le s a _ v hva]
      exact ⟨hv, hva, rfl, by omega, .nil, rfl⟩
    · have hav : a < v := Nat.lt_of_not_ge hva
      have hv0 : v ≠ 0 := by omega
      obtain ⟨hr, hra, hiter, hheight, p, hp⟩ :=
        ih (s.parent v) (hs.parent_lt v hv hv0) (hs.parent_mem v hv)
      rw [cutAncestor_eq_parent hs hv hav, cutHeight_eq_parent_add hs hv hav]
      refine ⟨hr, hra, ?_, ?_, p.concat (hs.parent_adj v hv hv0), ?_⟩
      · simpa only [Function.iterate_succ_apply] using hiter
      · have hh := hs.height_parent v hv hv0
        omega
      · simp only [SimpleGraph.Walk.length_concat, hp]

theorem ValidAt.dist_cutAncestor_eq_cutHeight {n : ℕ} {s : State} (hs : ValidAt n s)
    (a : ℕ) {v : ℕ} (hv : v ∈ s.vertices) :
    s.graph.dist (cutAncestor s a v) v = cutHeight s a v := by
  obtain ⟨_, _, _, hh, p, hp⟩ := hs.cutAncestor_path_data a hv
  apply le_antisymm
  · simpa only [hp] using s.graph.dist_le p
  · obtain ⟨q, hq⟩ := (show s.graph.Reachable (cutAncestor s a v) v from ⟨p⟩).exists_walk_length_eq_dist
    have hlength := hs.height_le_walk_length q
    omega

theorem ValidAt.cutAncestor_comp {n : ℕ} {s : State} (hs : ValidAt n s)
    {a b : ℕ} (hab : a ≤ b) {v : ℕ} (hv : v ∈ s.vertices) :
    cutAncestor s a (cutAncestor s b v) = cutAncestor s a v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases hvb : v ≤ b
    · rw [cutAncestor_of_le s b v hvb]
    · have hbv : b < v := Nat.lt_of_not_ge hvb
      have hv0 : v ≠ 0 := by omega
      rw [cutAncestor_eq_parent hs hv hbv,
        cutAncestor_eq_parent hs hv (hab.trans_lt hbv)]
      exact ih _ (hs.parent_lt v hv hv0) (hs.parent_mem v hv)

/-- A vertex alive at a later cut has an ancestor alive at each earlier cut.
This includes ancestors which freeze later and so are absent from the final
active set. -/
theorem HistoryShape.cutAncestor_historically_active {x : SignSequence} {n : ℕ} {s : State}
    (hs : HistoryShape x n s) {a b v : ℕ} (hab : a ≤ b)
    (hv : v ∈ (truncateAt s b).active) :
    cutAncestor s a v ∈ (truncateAt s a).active := by
  have hvalid := (hs.prefix_phaseData (Nat.le_refl n)).valid
  have hvV : v ∈ s.vertices := (Finset.mem_filter.mp hv).1
  have hvFrozen : ∀ t, s.frozenAt v = some t → b < t := (Finset.mem_filter.mp hv).2.2
  have hrec : ∀ w ∈ s.vertices,
      (∀ t, s.frozenAt w = some t → a < t) →
      cutAncestor s a w ∈ (truncateAt s a).active := by
    intro w
    induction w using Nat.strong_induction_on with
    | h w ih =>
      intro hw hfr
      by_cases hwa : w ≤ a
      · rw [cutAncestor_of_le s a w hwa]
        exact Finset.mem_filter.mpr ⟨hw, hwa, hfr⟩
      · have haw : a < w := Nat.lt_of_not_ge hwa
        have hw0 : w ≠ 0 := by omega
        have hp := hs.parent_lt w hw hw0
        have hpFrozen : ∀ t, s.frozenAt (s.parent w) = some t → a < t := by
          intro t ht
          exact haw.trans (hs.parent_frozen_after_child w hw hw0 t ht)
        have hparent := ih _ hp (hs.parent_mem w hw) hpFrozen
        have hcurrent : ValidAt n s := by
          simpa only [hs.prefix_self] using hvalid
        rwa [cutAncestor_eq_parent hcurrent hw haw]
  exact hrec v hvV (fun t ht => hab.trans_lt (hvFrozen t ht))

end Freezing1.Forward
