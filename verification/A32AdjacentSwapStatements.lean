module

import Freezing1.HeightScaleSorting

/-! Independent expanded source statements and axiom probe for A32. -/

open scoped BigOperators Classical
open Freezing1

set_option backward.isDefEq.respectTransparency false

example (x : SignSequence) (n i : ℕ) (hx : PositiveThrough x n)
    (hi : 1 ≤ i) (hin : i + 1 ≤ n) (hm : x i = false) (hp : x (i + 1) = true) :
    heightScale (Function.update (Function.update x i true) (i + 1) false) n ≤
      heightScale x n :=
  attachmentSwap_heightScale_le hx hi hin hm hp

example (x : SignSequence) (i : ℕ) (hi : 1 ≤ i)
    (hm : x i = false) (hp : x (i + 1) = true) (k : ℕ) :
    activeCount (Function.update (Function.update x i true) (i + 1) false) k =
      activeCount x k + if k = i then 2 else 0 :=
  attachmentSwap_activeCount hi hm hp k

example (x : SignSequence) (n : ℕ) (hx : PositiveThrough x n) :
    ∃ y, AttachmentSwapChain n x y ∧ PositiveThrough y n ∧
      (∀ k, 1 ≤ k → k ≤ n → y k = if k ≤ plusCount x n then true else false) ∧
      (∀ k, k = 0 ∨ n < k → y k = x k) ∧
      plusCount y n = plusCount x n ∧
      heightScale y n = shiftedHarmonic (plusCount x n) ∧
      heightScale y n ≤ heightScale x n := by
  obtain ⟨y, hy, hs, hpos, hout, hc, hh, hle⟩ := heightScale_sorted_by_adjacent_swaps x n hx
  refine ⟨y, hy, hpos, ?_, hout, hc, hh, hle⟩
  intro k hk hkn
  rw [hs.apply_eq hk hkn, hc]
  by_cases h : k ≤ plusCount x n <;> simp [h]

example (x : SignSequence) (n : ℕ) :
    ∃ y, AttachmentSwapChain n x y ∧ PrefixSorted y n :=
  exists_sorted_attachmentSwapChain x n

example (x y : SignSequence) (n : ℕ) (h : AttachmentSwapChain n x y) :
    plusCount y n = plusCount x n ∧ minusCount y n = minusCount x n := by
  exact ⟨h.plusCount_eq, by simp only [minusCount, h.plusCount_eq]⟩

example (x : SignSequence) (n i : ℕ) (hi : 1 ≤ i) (hin : i + 1 ≤ n)
    (hm : x i = false) (hp : x (i + 1) = true) :
    attachmentArea (attachmentSwap x i) n = attachmentArea x n + 1 ∧
      attachmentArea (attachmentSwap x i) n ≤ n * n :=
  ⟨attachmentArea_swap hi hin hm hp, attachmentArea_le _ _⟩

example (x : SignSequence) (n : ℕ) (hs : PrefixSorted x n) :
    heightScale x n =
      ∑ i ∈ Finset.Icc 1 (plusCount x n), 1 / ((i : ℝ) + 1) := by
  rw [hs.heightScale_eq]
  have he : Finset.Icc 1 (plusCount x n) = Finset.Ico 1 (plusCount x n + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [he, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, shiftedHarmonic, Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

example (x : SignSequence) (n : ℕ) (hn : 1 ≤ n) (hx : PositiveThrough x n) :
    Real.log ((n : ℝ) / 4) ≤ Real.log (((plusCount x n : ℝ) + 1) / 2) ∧
      Real.log (((plusCount x n : ℝ) + 1) / 2) ≤ shiftedHarmonic (plusCount x n) ∧
      shiftedHarmonic (plusCount x n) ≤ heightScale x n :=
  heightScale_lower_bound_by_adjacent_swaps hn hx

example (x : SignSequence) (n : ℕ) (hn : 1 ≤ n) (hx : PositiveThrough x n) :
    Real.log ((n : ℝ) / 4) ≤ heightScale x n := by
  obtain ⟨h₁, h₂, h₃⟩ := heightScale_lower_bound_by_adjacent_swaps hn hx
  exact h₁.trans (h₂.trans h₃)

#print axioms attachmentSwap_activeCount
#print axioms attachmentSwap_heightScale
#print axioms attachmentSwap_heightScale_le
#print axioms attachmentArea_swap
#print axioms exists_sorted_attachmentSwapChain
#print axioms PrefixSorted.apply_eq
#print axioms PrefixSorted.heightScale_eq
#print axioms heightScale_sorted_by_adjacent_swaps
#print axioms exists_sorted_schedule_by_adjacent_swaps
#print axioms heightScale_lower_bound_by_adjacent_swaps
