module

public import Freezing1.ForwardCutUpdates
public import Freezing1.ForwardTree

/-!
# Cut-forest statistics are unchanged by truncation at their endpoint

Parent chains of an old vertex stay within its birth-time prefix. Its cut
heights, and hence every block height, therefore agree in the terminal tree
and its prefix. Active vertices at an earlier cut are preserved exactly.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

theorem cutHeightAux_truncateAt {n : ℕ} {s : State} (hs : ValidAt n s)
    (a b m : ℕ) {v : ℕ} (hv : v ∈ s.vertices) (hvb : v ≤ b) :
    cutHeightAux (truncateAt s b) a m v = cutHeightAux s a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    by_cases hva : v ≤ a
    · simp only [cutHeightAux, ite_eq_left hva]
    · have hv0 : v ≠ 0 := by omega
      have hpv : s.parent v ≤ b := (hs.parent_lt v hv hv0).le.trans hvb
      change (if v ≤ a then 0 else cutHeightAux (truncateAt s b) a m
        ((truncateAt s b).parent v) + 1) = _
      rw [show (truncateAt s b).parent v = s.parent v by simp [truncateAt, hvb]]
      simp only [cutHeightAux, ite_eq_right hva, ih (hs.parent_mem v hv) hpv]

theorem cutHeight_truncateAt {n : ℕ} {s : State} (hs : ValidAt n s)
    (a b : ℕ) {v : ℕ} (hv : v ∈ s.vertices) (hvb : v ≤ b) :
    cutHeight (truncateAt s b) a v = cutHeight s a v := by
  unfold cutHeight
  rw [show (truncateAt s b).height v = s.height v by simp [truncateAt, hvb]]
  exact cutHeightAux_truncateAt hs a b _ hv hvb

theorem blockHeight_truncateAt {n : ℕ} {s : State} (hs : ValidAt n s)
    (a b c : ℕ) {v : ℕ} (hv : v ∈ s.vertices) (hvc : v ≤ c) :
    blockHeight (truncateAt s c) a b v = blockHeight s a b v := by
  simp only [blockHeight, cutHeight_truncateAt hs a c hv hvc,
    cutHeight_truncateAt hs b c hv hvc]

theorem cutRoots_truncateAt (s : State) {a b : ℕ} (hab : a ≤ b) :
    cutRoots (truncateAt s b) a = cutRoots s a := by
  ext v
  have hchar (t : State) : v ∈ cutRoots t a ↔
      v ∈ t.vertices ∧ v ≤ a ∧ ∀ j, t.frozenAt v = some j → a < j :=
    Finset.mem_filter
  rw [hchar, hchar]
  have hverts : v ∈ (truncateAt s b).vertices ↔ v ∈ s.vertices ∧ v ≤ b :=
    Finset.mem_filter
  rw [hverts]
  have hfreeze : (truncateAt s b).frozenAt v =
      match s.frozenAt v with
      | none => none
      | some t => if v ≤ b ∧ t ≤ b then some t else none := rfl
  constructor
  · rintro ⟨⟨hv, hvb⟩, hva, hf⟩
    refine ⟨hv, hva, ?_⟩
    intro j hj
    by_cases hjb : j ≤ b
    · exact hf j (by simp [hfreeze, hj, hvb, hjb])
    · omega
  · rintro ⟨hv, hva, hf⟩
    have hvb := hva.trans hab
    refine ⟨⟨hv, hvb⟩, hva, ?_⟩
    intro j hj
    cases hfs : s.frozenAt v with
    | none => simp [hfreeze, hfs] at hj
    | some t =>
      by_cases htb : t ≤ b
      · have he : t = j := by simpa [hfreeze, hfs, hvb, htb] using hj
        subst j
        exact hf t hfs
      · simp [hfreeze, hfs, htb] at hj

theorem blockTallCount_truncateAt {n : ℕ} {s : State} (hs : ValidAt n s)
    (a b : ℕ) (threshold : ℝ) :
    blockTallCount (truncateAt s b) a b threshold = blockTallCount s a b threshold := by
  unfold blockTallCount
  rw [cutRoots_truncateAt s le_rfl]
  congr 1
  apply Finset.filter_congr
  intro v hv
  have hm := (mem_cutRoots s b v).mp hv
  rw [blockHeight_truncateAt hs a b b (Finset.mem_filter.mp hm.1).1 hm.2]

end Freezing1.Forward
