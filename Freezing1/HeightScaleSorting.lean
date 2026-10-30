module

public import Freezing1.HeightScaleAdjacentSwap

/-! Finite iteration of the manuscript's actual adjacent swaps. -/

@[expose] public section

namespace Freezing1

open scoped BigOperators Classical

inductive AttachmentSwapChain (n : ℕ) (x : SignSequence) : SignSequence → Prop
  | refl : AttachmentSwapChain n x x
  | step {y : SignSequence} (h : AttachmentSwapChain n x y) (i : ℕ)
      (hi : 1 ≤ i) (hin : i + 1 ≤ n) (hm : y i = false) (hp : y (i + 1) = true) :
      AttachmentSwapChain n x (attachmentSwap y i)

def PrefixSorted (x : SignSequence) (n : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i + 1 ≤ n → x i = false → x (i + 1) = false

def attachmentArea (x : SignSequence) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, plusCount x k

theorem attachmentArea_le (x : SignSequence) (n : ℕ) : attachmentArea x n ≤ n * n := by
  calc
    _ ≤ ∑ _k ∈ Finset.range n, n := by
      apply Finset.sum_le_sum
      intro k hk
      exact (plusCount_le x k).trans (Nat.le_of_lt (Finset.mem_range.mp hk))
    _ = _ := by simp

theorem attachmentArea_swap {x : SignSequence} {i n : ℕ}
    (hi : 1 ≤ i) (hin : i + 1 ≤ n) (hm : x i = false) (hp : x (i + 1) = true) :
    attachmentArea (attachmentSwap x i) n = attachmentArea x n + 1 := by
  unfold attachmentArea
  simp_rw [attachmentSwap_plusCount hi hm hp, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', show i < n by omega]

theorem AttachmentSwapChain.plusCount_eq {n : ℕ} {x y : SignSequence}
    (h : AttachmentSwapChain n x y) : plusCount y n = plusCount x n := by
  induction h with
  | refl => rfl
  | step h i hi hin hm hp ih =>
    rw [attachmentSwap_plusCount hi hm hp]
    simpa only [ite_eq_right (show n ≠ i by omega), add_zero] using ih

theorem AttachmentSwapChain.positive {n : ℕ} {x y : SignSequence}
    (h : AttachmentSwapChain n x y) (hx : PositiveThrough x n) : PositiveThrough y n := by
  induction h with
  | refl => exact hx
  | step h i hi hin hm hp ih => exact ih.attachmentSwap hi hm hp

theorem AttachmentSwapChain.heightScale_le {n : ℕ} {x y : SignSequence}
    (h : AttachmentSwapChain n x y) (hx : PositiveThrough x n) :
    heightScale y n ≤ heightScale x n := by
  induction h with
  | refl => exact le_rfl
  | step h i hi hin hm hp ih =>
    exact (attachmentSwap_heightScale_le (h.positive hx) hi hin hm hp).trans ih

theorem AttachmentSwapChain.outside {n : ℕ} {x y : SignSequence}
    (h : AttachmentSwapChain n x y) (k : ℕ) (hk : k = 0 ∨ n < k) : y k = x k := by
  induction h with
  | refl => rfl
  | step h i hi hin hm hp ih =>
    rw [attachmentSwap_apply]
    have hki : k ≠ i := by rcases hk with rfl | hk <;> omega
    have hki' : k ≠ i + 1 := by rcases hk with rfl | hk <;> omega
    simpa only [ite_eq_right hki, ite_eq_right hki'] using ih

/-- Bounded integer area supplies termination of genuine adjacent swaps,
without assuming that a sorted permutation is reachable. -/
theorem exists_sorted_attachmentSwapChain (x : SignSequence) (n : ℕ) :
    ∃ y, AttachmentSwapChain n x y ∧ PrefixSorted y n := by
  let A : Set ℕ := {a | ∃ y, AttachmentSwapChain n x y ∧ attachmentArea y n = a}
  have hfin : A.Finite := (Set.finite_Iic (n * n)).subset (by
    rintro a ⟨y, _, rfl⟩
    exact attachmentArea_le y n)
  have hne : A.Nonempty := ⟨attachmentArea x n, x, .refl, rfl⟩
  obtain ⟨y, hy, harea⟩ := hne.csSup_mem hfin
  refine ⟨y, hy, fun i hi hin hm => ?_⟩
  by_contra hh
  have hp : y (i + 1) = true := by cases he : y (i + 1) <;> simp_all
  have hz : AttachmentSwapChain n x (attachmentSwap y i) := .step hy i hi hin hm hp
  have hmem : attachmentArea (attachmentSwap y i) n ∈ A := ⟨_, hz, rfl⟩
  have hle := le_csSup hfin.bddAbove hmem
  rw [attachmentArea_swap hi hin hm hp, harea] at hle
  omega

theorem PrefixSorted.false_later {x : SignSequence} {n : ℕ} (hs : PrefixSorted x n)
    {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (hkn : k ≤ n) (hm : x i = false) :
    x k = false := by
  induction k, hik using Nat.le_induction with
  | base => exact hm
  | succ k hik ih => exact hs k (by omega) hkn (ih (by omega))

theorem PrefixSorted.true_before {x : SignSequence} {n : ℕ} (hs : PrefixSorted x n)
    {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (hkn : k ≤ n) (hp : x k = true) :
    x i = true := by
  cases hm : x i
  · have := hs.false_later hi hik hkn hm
    simp [hp] at this
  · rfl

theorem PrefixSorted.plusCount_eq_of_true_last {x : SignSequence} {n : ℕ}
    (hs : PrefixSorted x (n + 1)) (hp : x (n + 1) = true) : plusCount x n = n := by
  unfold plusCount
  calc
    _ = ∑ _i ∈ Finset.range n, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      have ht := hs.true_before (by omega : 1 ≤ i + 1)
        (by have := Finset.mem_range.mp hi; omega : i + 1 ≤ n + 1) le_rfl hp
      simp [ht]
    _ = n := by simp

/-- The sorted-prefix predicate means literally all attachments first. -/
theorem PrefixSorted.apply_eq {x : SignSequence} {n : ℕ} (hs : PrefixSorted x n)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : x k = decide (k ≤ plusCount x n) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    have hs' : PrefixSorted x n := fun i hi hin => hs i hi (by omega)
    rw [plusCount_succ]
    cases hp : x (n + 1)
    · by_cases hkn' : k ≤ n
      · exact ih hs' hk hkn'
      · have he : k = n + 1 := by omega
        subst k
        simp [hp, show ¬n + 1 ≤ plusCount x n from by have := plusCount_le x n; omega]
    · have hc := hs.plusCount_eq_of_true_last hp
      rw [hc]
      have ht := hs.true_before hk hkn le_rfl hp
      simp [ht, hkn]

theorem PrefixSorted.heightScale_eq {x : SignSequence} {n : ℕ} (hs : PrefixSorted x n) :
    heightScale x n = shiftedHarmonic (plusCount x n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs' : PrefixSorted x n := fun i hi hin => hs i hi (by omega)
    rw [heightScale_succ, plusCount_succ, ih hs']
    cases hp : x (n + 1)
    · simp
    · have hc := hs.plusCount_eq_of_true_last hp
      have ha : (activeCount x (n + 1) : ℝ) = (n : ℝ) + 2 := by
        rw [activeCount_eq, plusCount_succ, hp, hc]
        simp only [ite_true]
        push_cast
        ring
      simp only [↓reduceIte, shiftedHarmonic_succ, hc, ha]

/-- The source's sorted schedule is reached by finitely many of its
specified swaps, retains the tail, and has the exact harmonic height. -/
theorem heightScale_sorted_by_adjacent_swaps (x : SignSequence) (n : ℕ)
    (hx : PositiveThrough x n) :
    ∃ y, AttachmentSwapChain n x y ∧ PrefixSorted y n ∧ PositiveThrough y n ∧
      (∀ k, k = 0 ∨ n < k → y k = x k) ∧
      plusCount y n = plusCount x n ∧
      heightScale y n = shiftedHarmonic (plusCount x n) ∧
      heightScale y n ≤ heightScale x n := by
  obtain ⟨y, hy, hs⟩ := exists_sorted_attachmentSwapChain x n
  refine ⟨y, hy, hs, hy.positive hx, hy.outside, hy.plusCount_eq, ?_, hy.heightScale_le hx⟩
  rw [hs.heightScale_eq, hy.plusCount_eq]

theorem exists_sorted_schedule_by_adjacent_swaps (x : SignSequence) (n : ℕ) :
    ∃ y, AttachmentSwapChain n x y ∧
      (∀ k, 1 ≤ k → k ≤ n → y k = decide (k ≤ plusCount x n)) ∧
      (∀ k, k = 0 ∨ n < k → y k = x k) := by
  obtain ⟨y, hy, hs⟩ := exists_sorted_attachmentSwapChain x n
  refine ⟨y, hy, ?_, hy.outside⟩
  intro k hk hkn
  rw [hs.apply_eq hk hkn, hy.plusCount_eq]

/-- All inequalities displayed in the manuscript's adjacent-swap proof,
with its original weaker logarithmic intermediate bound. -/
theorem heightScale_lower_bound_by_adjacent_swaps {x : SignSequence} {n : ℕ}
    (hn : 1 ≤ n) (hx : PositiveThrough x n) :
    Real.log ((n : ℝ) / 4) ≤ Real.log (((plusCount x n : ℝ) + 1) / 2) ∧
      Real.log (((plusCount x n : ℝ) + 1) / 2) ≤ shiftedHarmonic (plusCount x n) ∧
      shiftedHarmonic (plusCount x n) ≤ heightScale x n := by
  obtain ⟨y, hy, hs, _, _, hc, hh, hle⟩ := heightScale_sorted_by_adjacent_swaps x n hx
  have hcount : (n : ℝ) ≤ 2 * (plusCount x n : ℝ) := by
    exact_mod_cast le_two_mul_plusCount hx
  refine ⟨Real.log_le_log (by positivity) (by linarith), ?_, ?_⟩
  · exact (Real.log_le_log (by positivity) (by linarith)).trans (log_le_shiftedHarmonic _)
  · rw [← hh]
    exact hle

end Freezing1
