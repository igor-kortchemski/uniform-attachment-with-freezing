module

public import Freezing1.ReversePairHeightHistory

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

/- The pair consists of two random phase-b roots, expressed using fixed labels.
   The bound retains the probability of that past event. It does not replace
   it by one and does not assert independence of different vertex heights. -/
example (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    (a b : ℕ) (hab : a ≤ b) (hbn : b ≤ n)
    (u v : ℕ ⊕ ℕ) (huv : u ≠ v) (t : ℝ) :
    (Freezing1.ReverseHistory.fullLaw x n).real
      {H | u ∈ (Freezing1.ReverseHistory.stage H b).roots ∧
        v ∈ (Freezing1.ReverseHistory.stage H b).roots ∧
        t < ((Freezing1.ReverseHistory.stage H a).depth u : ℝ) ∧
        t < ((Freezing1.ReverseHistory.stage H a).depth v : ℝ)} ≤
      (Freezing1.ReverseHistory.fullLaw x n).real
        {H | u ∈ (Freezing1.ReverseHistory.stage H b).roots ∧
          v ∈ (Freezing1.ReverseHistory.stage H b).roots} *
      ((Freezing1.bernoulliPartialSumLaw
          (Freezing1.Reverse.attachmentParameter x n hn)
          (Finset.univ.filter fun i : Fin n => a ≤ i.val ∧ i.val < b)).real
          {j : ℕ | t < (j : ℝ)} ^ 2 +
        ∑ i ∈ Finset.Ioc a b,
          if x i then 1 / ((Freezing1.activeCount x i).toNat.choose 2 : ℝ) else 0) := by
  simpa only [Freezing1.Reverse.blockTailProbability, Freezing1.Reverse.blockIndices,
    Freezing1.Reverse.blockCoalescenceRisk, Freezing1.Reverse.coalescenceHazard,
    Nat.add_sub_of_le hab] using
    Freezing1.ReverseHistory.fullLaw_root_pair_tail_le x n hn hab hbn huv t

#print axioms Freezing1.Reverse.transitionLaw_exclusive_depth_increments
#print axioms Freezing1.Reverse.transitionLaw_killed_product_le
#print axioms Freezing1.Reverse.blockLaw_killed_product_le
#print axioms Freezing1.Reverse.blockAverage_eq_integral_partialSum
#print axioms Freezing1.Reverse.blockLaw_pair_tail_le
#print axioms Freezing1.ReverseHistory.map_blockHistoryLaw_current
#print axioms Freezing1.ReverseHistory.fullLaw_root_pair_tail_le
