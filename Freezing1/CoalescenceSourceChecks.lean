module

public import Freezing1.ReverseCoalescenceTime
public import Freezing1.TreeSourceChecks

/-!
# A genuine counterexample to the printed diagonal coalescence law

At one attachment step, an active vertex coalesces with itself at phase one.
The printed formula without a distinctness premise assigns probability one
to phase zero. Both probabilities are checked for the actual history law.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped ENNReal BigOperators

theorem printed_coalescence_law_counterexample (x : SignSequence) (hx : x 1 = true) :
    (ReverseHistory.fullLaw x 1).real
        {H | ReverseHistory.coalescenceTime 1 H (Sum.inl 0) (Sum.inl 0) = 0} ≠
      (1 / ((activeCount x 1).toNat.choose 2 : ℝ)) *
        ∏ t ∈ (Finset.Ioc 1 1).filter (fun t => x t = true),
          (1 - 1 / ((activeCount x t).toNat.choose 2 : ℝ)) := by
  have hτ := one_lt_extinctionTime_of_attachment x hx
  have hS : activeCount x 1 = 2 := by
    simpa only [activeCount_succ, activeCount_zero, hx, ↓reduceIte] using (show (1 : ℤ) + 1 = 2 by norm_num)
  have hv : Sum.inl 0 ∈ vertexLabels x 1 := by
    simp [vertexLabels, hS]
  have hself := ReverseHistory.fullLaw_coalescenceTime_self x 1 hτ.le hv
  have he : (ReverseHistory.fullLaw x 1).real
      {H | ReverseHistory.coalescenceTime 1 H (Sum.inl 0) (Sum.inl 0) = 0} = 0 := by
    have hset : {H | ReverseHistory.coalescenceTime 1 H (Sum.inl 0) (Sum.inl 0) = 0}
        =ᵐ[ReverseHistory.fullLaw x 1] (∅ : Set ReverseHistory.History) := by
      filter_upwards [hself] with H hH
      simp only [birthTime] at hH
      simp [hH]
    rw [measureReal_congr hset]
    simp
  rw [he, hS]
  norm_num

end Freezing1
