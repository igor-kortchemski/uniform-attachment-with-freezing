module

public import Freezing1.ReversePairHeightVariance

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

/- The random variable is literally the number of actual phase-b roots whose
   phase-a height exceeds t, on the same genuine reverse-history law. -/
example (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    (a b : ℕ) (hab : a ≤ b) (hbn : b ≤ n) (t : ℝ) :
    variance
      (fun H => (((Freezing1.ReverseHistory.stage H b).roots.filter
        fun v => t < ((Freezing1.ReverseHistory.stage H a).depth v : ℝ)).card : ℝ))
      (Freezing1.ReverseHistory.fullLaw x n) ≤
      (Freezing1.activeCount x b : ℝ) + (Freezing1.activeCount x b : ℝ) ^ 2 *
        (∑ i ∈ Finset.Ioc a b,
          if x i then 1 / ((Freezing1.activeCount x i).toNat.choose 2 : ℝ) else 0) := by
  simpa only [Freezing1.ReverseHistory.blockTallRootCount,
    Freezing1.Reverse.blockCoalescenceRisk, Freezing1.Reverse.coalescenceHazard,
    Nat.add_sub_of_le hab] using
    Freezing1.ReverseHistory.variance_blockTallRootCount_le x n hn hab hbn t

#print axioms Freezing1.ReverseHistory.blockTallRootCount_memLp
#print axioms Freezing1.ReverseHistory.integral_blockTallRootCount_sq_le
#print axioms Freezing1.ReverseHistory.integral_blockTallRootCount_eq_blockTail
#print axioms Freezing1.ReverseHistory.variance_blockTallRootCount_le
