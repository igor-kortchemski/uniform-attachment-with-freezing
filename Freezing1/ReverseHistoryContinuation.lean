module

public import Freezing1.ReverseHistory

/-!
# Markov continuation of the actual reverse history

The complete history is retained while the original transition kernels are
iterated from phase `a+k` down to phase `a`. The decomposition theorem is an
equality of measures, with no independence or conditional-law hypothesis.
-/

@[expose] public section

namespace Freezing1.ReverseHistory

open MeasureTheory

noncomputable def blockHistoryLaw (x : SignSequence) (a : ℕ) :
    ℕ → History → Measure History
  | 0, H => Measure.dirac H
  | k + 1, H => (transitionLaw x (a + k) H).bind (blockHistoryLaw x a k)

instance blockHistoryLaw_probability (x : SignSequence) (a k : ℕ) (H : History) :
    IsProbabilityMeasure (blockHistoryLaw x a k H) := by
  induction k generalizing H with
  | zero => change IsProbabilityMeasure (Measure.dirac H); infer_instance
  | succ k ih =>
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Filter.Eventually.of_forall ih)

/-- Every forest preceding the block is preserved in the full recorded history. -/
theorem map_blockHistoryLaw_stage (x : SignSequence) (a k : ℕ) (H : History) (j : ℕ) :
    (blockHistoryLaw x a k H).map (fun H' => stage H' (k + j)) =
      Measure.dirac (stage H j) := by
  induction k generalizing H j with
  | zero =>
    simpa only [blockHistoryLaw, Nat.zero_add] using
      (Measure.map_dirac' (f := fun H' : History => stage H' j) measurable_from_top H)
  | succ k ih =>
    rw [blockHistoryLaw,
      Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    have ht : k + 1 + j = k + (j + 1) := by omega
    simp_rw [ht, ih]
    rw [Measure.bind_dirac_eq_map _ measurable_from_top]
    exact map_transitionLaw_stage_succ x (a + k) H j

/-- Split the genuine joint law at the top of any finite block. -/
theorem lawAfter_eq_bind_blockHistoryLaw (x : SignSequence) (n a k : ℕ)
    (hak : a + k ≤ n) :
    lawAfter x n (n - a) =
      (lawAfter x n (n - (a + k))).bind (blockHistoryLaw x a k) := by
  induction k with
  | zero => simpa only [Nat.add_zero, blockHistoryLaw] using
      (Measure.bind_dirac (m := lawAfter x n (n - a))).symm
  | succ k ih =>
    rw [ih (by omega)]
    have he : n - (a + k) = (n - (a + (k + 1))) + 1 := by omega
    have hlt : n - (a + (k + 1)) < n := by omega
    have hi : n - ((n - (a + (k + 1))) + 1) = a + k := by omega
    rw [he, lawAfter, ite_eq_left hlt, hi,
      Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    rfl

/-- The same split in the paper's two endpoint notation. -/
theorem lawAfter_eq_bind_continuation (x : SignSequence) (n a b : ℕ)
    (hab : a ≤ b) (hbn : b ≤ n) :
    lawAfter x n (n - a) =
      (lawAfter x n (n - b)).bind (blockHistoryLaw x a (b - a)) := by
  simpa only [Nat.add_sub_of_le hab] using
    lawAfter_eq_bind_blockHistoryLaw x n a (b - a) (by omega)

end Freezing1.ReverseHistory
