module

public import Freezing1.HeightScale

/-! The actual adjacent transposition in the manuscript's harmonic bound. -/

@[expose] public section

namespace Freezing1

open scoped BigOperators Classical

/-- Move an attachment immediately before the preceding freezing step. -/
def attachmentSwap (x : SignSequence) (i : ℕ) : SignSequence :=
  Function.update (Function.update x i true) (i + 1) false

theorem attachmentSwap_apply (x : SignSequence) (i k : ℕ) :
    attachmentSwap x i k = if k = i then true else if k = i + 1 then false else x k := by
  by_cases hki : k = i <;> by_cases hki' : k = i + 1 <;>
    simp [attachmentSwap, hki, hki']

theorem attachmentSwap_plusCount {x : SignSequence} {i : ℕ}
    (hi : 1 ≤ i) (hminus : x i = false) (hplus : x (i + 1) = true) (k : ℕ) :
    plusCount (attachmentSwap x i) k = plusCount x k + if k = i then 1 else 0 := by
  induction k with
  | zero => simp [show 0 ≠ i by omega]
  | succ k ih =>
    rw [plusCount_succ, plusCount_succ, ih, attachmentSwap_apply]
    by_cases hk : k + 1 = i
    · have hk' : k ≠ i := by omega
      simp [hk, hk', hminus]
    · by_cases hk' : k + 1 = i + 1
      · have hki : k = i := by omega
        simp [hki, hplus]
      · have hki : k ≠ i := by omega
        simp [hk, hki]

theorem attachmentSwap_activeCount {x : SignSequence} {i : ℕ}
    (hi : 1 ≤ i) (hminus : x i = false) (hplus : x (i + 1) = true) (k : ℕ) :
    activeCount (attachmentSwap x i) k = activeCount x k + if k = i then 2 else 0 := by
  rw [activeCount_eq, activeCount_eq, attachmentSwap_plusCount hi hminus hplus]
  split_ifs <;> push_cast <;> ring

theorem PositiveThrough.attachmentSwap {x : SignSequence} {n i : ℕ}
    (h : PositiveThrough x n) (hi : 1 ≤ i)
    (hminus : x i = false) (hplus : x (i + 1) = true) :
    PositiveThrough (Freezing1.attachmentSwap x i) n := by
  intro k hk
  rw [attachmentSwap_activeCount hi hminus hplus]
  have := h k hk
  split_ifs <;> omega

/-- The sole changed height contribution replaces `1 / S_(i+1)` by
`1 / (S_(i+1)+1)`; all later populations and terms agree exactly. -/
theorem attachmentSwap_heightScale {x : SignSequence} {i n : ℕ}
    (hi : 1 ≤ i) (hin : i + 1 ≤ n)
    (hminus : x i = false) (hplus : x (i + 1) = true) :
    heightScale (attachmentSwap x i) n + 1 / (activeCount x (i + 1) : ℝ) =
      heightScale x n + 1 / ((activeCount x (i + 1) : ℝ) + 1) := by
  have hlocal : ∀ k, (if attachmentSwap x i (k + 1) then
      1 / (activeCount (attachmentSwap x i) (k + 1) : ℝ) else 0) =
      (if x (k + 1) then 1 / (activeCount x (k + 1) : ℝ) else 0) +
      (if k + 1 = i then 1 / ((activeCount x (i + 1) : ℝ) + 1) else 0) -
      (if k + 1 = i + 1 then 1 / (activeCount x (i + 1) : ℝ) else 0) := by
    intro k
    rw [attachmentSwap_apply, attachmentSwap_activeCount hi hminus hplus]
    by_cases hk : k + 1 = i
    · have hk' : k + 1 ≠ i + 1 := by omega
      have hc : (activeCount x i : ℝ) + 2 = (activeCount x (i + 1) : ℝ) + 1 := by
        rw [activeCount_succ, hplus]
        simp only [ite_true, Int.cast_add, Int.cast_one]
        ring
      simp [hk, hminus, hc]
    · by_cases hk' : k + 1 = i + 1
      · simp [hk', hplus]
      · have hki : k ≠ i := by omega
        simp [hk, hki]
  have hi' : i - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hi'' : i ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hp : (∑ k ∈ Finset.range n, if k + 1 = i then
      1 / ((activeCount x (i + 1) : ℝ) + 1) else 0) =
      1 / ((activeCount x (i + 1) : ℝ) + 1) := by
    rw [Finset.sum_eq_single (i - 1)]
    · simp [show i - 1 + 1 = i by omega]
    · intro b _ hbi
      simp [show b + 1 ≠ i by omega]
    · exact fun hh => (hh hi').elim
  have hm : (∑ k ∈ Finset.range n, if k + 1 = i + 1 then
      1 / (activeCount x (i + 1) : ℝ) else 0) =
      1 / (activeCount x (i + 1) : ℝ) := by
    simp only [Nat.add_right_cancel_iff, Finset.sum_ite_eq', hi'', ↓reduceIte]
  unfold heightScale
  simp_rw [hlocal, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hp, hm]
  ring

theorem attachmentSwap_heightScale_le {x : SignSequence} {i n : ℕ}
    (h : PositiveThrough x n) (hi : 1 ≤ i) (hin : i + 1 ≤ n)
    (hminus : x i = false) (hplus : x (i + 1) = true) :
    heightScale (attachmentSwap x i) n ≤ heightScale x n := by
  have hc : 0 < (activeCount x (i + 1) : ℝ) := by exact_mod_cast h (i + 1) hin
  have he := attachmentSwap_heightScale hi hin hminus hplus
  have hr : 1 / ((activeCount x (i + 1) : ℝ) + 1) ≤
      1 / (activeCount x (i + 1) : ℝ) :=
    one_div_le_one_div_of_le hc (by linarith)
  linarith

end Freezing1
