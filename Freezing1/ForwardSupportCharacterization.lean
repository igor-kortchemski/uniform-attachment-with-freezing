module

public import Freezing1.ConstructionEquivalence
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The corrected forward support and point-mass statement

The schedule-compatible increasing terminal shape is equivalent to an actual
legal history, including the extinction endpoint. Its mass is the forward
probability product. The larger shape class printed in L04 lacks schedule
compatibility and remains a false literal assertion.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal
open scoped BigOperators

theorem treeLaw_historyShape (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂treeLaw x n, HistoryShape x n s := by
  rw [← CanonicalTree.reverseStateLaw_eq_forward_treeLaw x n hn]
  exact (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
    (CanonicalTree.treeLaw_reverseState_historyShape x n hn)

theorem HasHistory.historyShape {x : SignSequence} {n : ℕ} {s : State}
    (h : HasHistory x n s) (hn : (n : ℕ∞) ≤ extinctionTime x) :
    HistoryShape x n s := by
  have hp := (treeLaw_singleton_ne_zero_iff_hasHistory x n hn s).mpr h
  by_contra hnot
  apply hp
  apply measure_mono_null (t := {r : State | ¬HistoryShape x n r}) _
    (ae_iff.mp (treeLaw_historyShape x n hn))
  intro r hr
  change ¬HistoryShape x n r
  simpa only [Set.mem_singleton_iff.mp hr] using hnot

/-- Necessary and sufficient finite support, with the fixed schedule retained. -/
theorem historyShape_iff_hasHistory (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (s : State) :
    HistoryShape x n s ↔ HasHistory x n s :=
  ⟨HistoryShape.hasHistory, fun h => h.historyShape hn⟩

theorem treeLaw_singleton_ne_zero_iff_historyShape (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (s : State) :
    (treeLaw x n) {s} ≠ 0 ↔ HistoryShape x n s := by
  rw [treeLaw_singleton_ne_zero_iff_hasHistory x n hn s,
    historyShape_iff_hasHistory x n hn s]

/-- Corrected L04: every schedule-compatible increasing shape has the exact
product mass, with no extra probabilistic premise. -/
theorem treeLaw_real_singleton_of_historyShape (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {s : State}
    (hs : HistoryShape x n s) :
    (treeLaw x n).real {s} = forwardHistoryWeight x n :=
  treeLaw_real_singleton_of_hasHistory x n hn hs.hasHistory

theorem forwardHistoryWeight_eq_source_product (x : SignSequence) (n : ℕ) :
    forwardHistoryWeight x n =
      ∏ i ∈ Finset.Icc 1 n, 1 / (activeCount x (i - 1) : ℝ) := by
  induction n with
  | zero => simp [forwardHistoryWeight]
  | succ n ih =>
    rw [forwardHistoryWeight_succ, Finset.prod_Icc_succ_top (by omega), ih]
    simp

/-- The corrected fixed-schedule statement in the paper's exact indexing. -/
theorem corrected_forward_tree_probability (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {s : State} (hs : HistoryShape x n s) :
    (treeLaw x n).real {s} =
      ∏ i ∈ Finset.Icc 1 n, 1 / (activeCount x (i - 1) : ℝ) := by
  rw [treeLaw_real_singleton_of_historyShape x n hn hs,
    forwardHistoryWeight_eq_source_product]

end Freezing1.Forward
