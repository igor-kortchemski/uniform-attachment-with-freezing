module

import Freezing1.ReverseHistoryHeight
import Freezing1.ReverseHeightBounds

/-!
Independent statement probe for source L01 and P03, using the manuscript's
paper step i, rather than the implementation's reverse transition count k.
The conditional sigma-algebra contains the entire predecessor history.
The upper P03 claim below is deliberately the corrected |V_n| version.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Freezing1

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) (i : ℕ)
    (hi : 1 ≤ i) (hib : i ≤ birthTime n v) :
    (ReverseHistory.lawAfter x n (n - i + 1))[
      (fun H => if ReverseHistory.heightIncrement v H = 1 then (1 : ℝ) else 0) |
      MeasurableSpace.comap ReverseHistory.previous (⊤ : MeasurableSpace ReverseHistory.History)]
      =ᵐ[ReverseHistory.lawAfter x n (n - i + 1)]
        fun _ => if x i then 1 / (activeCount x i : ℝ) else 0 := by
  have hin : i ≤ n := by
    cases v with
    | inl j => simpa only [birthTime] using hib
    | inr j =>
      have hj : j < n ∧ x (j + 1) = false := by
        simpa [vertexLabels, frozenIndices] using hv
      simp only [birthTime] at hib
      omega
  have he : n - (n - i) = i := Nat.sub_sub_self hin
  simpa only [he] using
    ReverseHistory.height_increment_conditional_probability x n (n - i) hn
      (by omega) hv (by omega)

example (x : SignSequence) (n : ℕ) (hn : 1 ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x) {t : ℝ} (ht : 0 < t) :
    (Reverse.treeLaw x n).real
      {F | (reverseMaximum F : ℝ) - heightScale x n < -t} ≤
      Real.exp (-heightScale x n * bennettRate (t / heightScale x n)) :=
  reverseMaximum_lower_tail_source x n hn hτ ht

example (x : SignSequence) (n : ℕ) (hn : 1 ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x) {t : ℝ} (ht : 0 < t) :
    (Reverse.treeLaw x n).real
      {F | t < (reverseMaximum F : ℝ) - heightScale x n} ≤
      Real.exp (-heightScale x n * bennettRate (t / heightScale x n) +
        Real.log ((vertexLabels x n).card : ℝ)) :=
  reverseMaximum_corrected_upper_tail_source x n hn hτ ht

#print axioms Freezing1.ReverseHistory.forest_heightIncrement_hasLaw
#print axioms Freezing1.ReverseHistory.transitionLaw_previous_increment
#print axioms Freezing1.ReverseHistory.lawAfter_previous_increment_joint
#print axioms Freezing1.ReverseHistory.lawAfter_heightIncrement_hasLaw
#print axioms Freezing1.ReverseHistory.lawAfter_heightIncrement_indep_previous
#print axioms Freezing1.ReverseHistory.height_increment_conditional_probability
#print axioms Freezing1.Reverse.transitionLaw_trackedDepth_hasLaw
#print axioms Freezing1.Reverse.lawAfter_trackedDepth_hasLaw
#print axioms Freezing1.Reverse.treeLaw_depth_hasLaw
#print axioms Freezing1.Reverse.treeLaw_height_identDistrib_bernoulli
#print axioms Freezing1.Reverse.heightBernoulli_independent
#print axioms Freezing1.Reverse.heightBernoulli_hasLaw
#print axioms Freezing1.Reverse.sum_attachmentParameter
#print axioms Freezing1.reverseMaximum_eq_finiteHeightMax
#print axioms Freezing1.reverseMaximum_eq_finiteHeightMax_ae
#print axioms Freezing1.reverseMaximum_corrected_upper_tail
#print axioms Freezing1.reverseMaximum_upper_tail_nat_succ
#print axioms Freezing1.reverseMaximum_lower_tail
#print axioms Freezing1.reverseMaximum_corrected_upper_tail_source
#print axioms Freezing1.reverseMaximum_lower_tail_source
