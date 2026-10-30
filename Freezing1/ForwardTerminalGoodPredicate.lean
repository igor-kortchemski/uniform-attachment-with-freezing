module

public import Freezing1.GeometricChainSourceIndices
public import Freezing1.ForwardTruncationLaw
public import Freezing1.ForwardBlockStatistics
public import Freezing1.ForwardCutTruncation

/-! Source A48: all good-chain tests can be read in the one terminal tree. -/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

theorem cutAncestorAux_truncate_of_mem {n : ℕ} {s : State} (hs : ValidAt n s)
    (a b m : ℕ) {v : ℕ} (hv : v ∈ s.vertices) (hvb : v ≤ b) :
    cutAncestorAux (truncateAt s b) a m v = cutAncestorAux s a m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    by_cases hva : v ≤ a
    · simp only [cutAncestorAux, ite_eq_left hva]
    · have hv0 : v ≠ 0 := by omega
      have hp : s.parent v ≤ b := (hs.parent_lt v hv hv0).le.trans hvb
      change (if v ≤ a then v else cutAncestorAux (truncateAt s b) a m
        ((truncateAt s b).parent v)) = _
      rw [show (truncateAt s b).parent v = s.parent v by simp [truncateAt, hvb]]
      simp only [cutAncestorAux, ite_eq_right hva, ih (hs.parent_mem v hv) hp]

theorem cutAncestor_truncate_of_mem {n : ℕ} {s : State} (hs : ValidAt n s)
    (a b : ℕ) {v : ℕ} (hv : v ∈ s.vertices) (hvb : v ≤ b) :
    cutAncestor (truncateAt s b) a v = cutAncestor s a v := by
  unfold cutAncestor
  change cutAncestorAux (truncateAt s b) a (if v ≤ b then s.height v else 0) v = _
  rw [ite_eq_left hvb]
  exact cutAncestorAux_truncate_of_mem hs a b _ hv hvb

/-- The source's active set at a past time is recovered from the terminal
birth identifiers and freezing timestamps, including the initial root. -/
theorem mem_historical_active (s : State) (b v : ℕ) :
    v ∈ (truncateAt s b).active ↔
      v ∈ s.vertices ∧ v ≤ b ∧ ∀ t, s.frozenAt v = some t → b < t := by
  simp only [truncateAt, Finset.mem_filter]

theorem goodSet_truncate_eq_terminal_filter {n : ℕ} {s : State} (hs : ValidAt n s)
    (C k₀ k : ℕ) (t : ℝ) :
    goodSet (truncateAt s (C ^ k)) C k₀ k t =
      (truncateAt s (C ^ k)).active.filter fun v => ∀ ell ∈ Finset.Ico k₀ k,
        t < (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ) := by
  unfold goodSet
  apply Finset.filter_congr
  intro v hv
  obtain ⟨hvV, hvb, _⟩ := (mem_historical_active s (C ^ k) v).mp hv
  simp only [blockHeight_truncateAt hs _ _ _ hvV hvb]

/-- Exact cumulative-good predicate of the paper, with every height increment
evaluated in the same terminal tree and every source index retained. -/
theorem goodSet_truncate_eq_source_filter {n : ℕ} {s : State} (hs : ValidAt n s)
    (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ) (N k : ℕ) (t : ℝ)
    (hA : 0 < A N) (hk₀ : 1 ≤ chainLowerIndex C A N) :
    goodSet (truncateAt s (C ^ k)) C (chainLowerIndex C A N) k t =
      (truncateAt s (C ^ k)).active.filter fun v =>
        ∀ ell : ℕ, 1 ≤ ell → ell < k → A N ≤ ((C ^ ell : ℕ) : ℝ) →
          t < (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ) := by
  rw [goodSet_eq_source_filter _ C hC A N k t hA hk₀]
  apply Finset.filter_congr
  intro v hv
  obtain ⟨hvV, hvb, _⟩ := (mem_historical_active s (C ^ k) v).mp hv
  simp only [blockHeight_truncateAt hs _ _ _ hvV hvb]

/-- The tall count at two prefixes is exactly the source's terminal-tree
count over vertices that were active at the upper cut. -/
theorem blockTallCount_truncate_eq_terminal_filter {n : ℕ} {s : State}
    (hs : ValidAt n s) (a b : ℕ) (t : ℝ) :
    blockTallCount (truncateAt s b) a b t =
      ((truncateAt s b).active.filter fun v => t < (blockHeight s a b v : ℝ)).card := by
  rw [blockTallCount_truncateAt hs a b t]
  rfl

theorem treeLaw_goodSet_truncate_eq_source_filter (x : SignSequence) (n : ℕ)
    (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ) (k : ℕ) (t : ℝ)
    (hA : 0 < A n) (hk₀ : 1 ≤ chainLowerIndex C A n) :
    ∀ᵐ s ∂treeLaw x n,
      goodSet (truncateAt s (C ^ k)) C (chainLowerIndex C A n) k t =
        (truncateAt s (C ^ k)).active.filter fun v =>
          ∀ ell : ℕ, 1 ≤ ell → ell < k → A n ≤ ((C ^ ell : ℕ) : ℝ) →
            t < (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ) :=
  (treeLaw_valid x n).mono fun _ hs =>
    goodSet_truncate_eq_source_filter hs C hC A n k t hA hk₀

end Freezing1.Forward
