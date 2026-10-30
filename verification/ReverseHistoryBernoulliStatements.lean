module

import Freezing1.ReverseHistoryBernoulli

/-!
Exact actual-history probes for A13. The index j below denotes paper step
j+1: its increment is H_j(v)-H_(j+1)(v). Every statement concerns a single
fixed vertex, and the common probability space is the actual full history.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Freezing1 Freezing1.ReverseHistory

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    iIndepFun (fun j : Fin (birthTime n v) => fun H : History =>
      (stage H j.val).depth v - (stage H (j.val + 1)).depth v) (fullLaw x n) := by
  apply (phaseIncrements_independent x n hn hv).congr
  intro j
  exact Filter.Eventually.of_forall fun H => phaseIncrement_eq_stage v j.val H

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    ∀ᵐ H ∂fullLaw x n, (stage H 0).depth v =
      ∑ j : Fin (birthTime n v),
        ((stage H j.val).depth v - (stage H (j.val + 1)).depth v) := by
  simpa only [phaseIncrement_eq_stage, stage_zero] using
    fullLaw_depth_eq_sum_phaseIncrements x n hn hv

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ birthTime n v) :
    HasLaw (fun H : History => (stage H a).depth v - (stage H b).depth v)
      (bernoulliPartialSumLaw
        (fun j : Fin b => Reverse.attachmentParameter x n hn
          ⟨j.val, j.isLt.trans_le (hb.trans (Reverse.birthTime_le_of_mem hv))⟩)
        (Finset.univ.filter fun j : Fin b => a ≤ j.val)) (fullLaw x n) :=
  fullLaw_depth_difference_hasLaw x n hn hv hab hb

#print axioms Freezing1.ReverseHistory.phaseIncrement_hasLaw
#print axioms Freezing1.ReverseHistory.phaseIncrements_independent
#print axioms Freezing1.ReverseHistory.phaseIncrements_hasLaw_product
#print axioms Freezing1.ReverseHistory.fullLaw_depth_eq_sum_phaseIncrements
#print axioms Freezing1.ReverseHistory.fullLaw_depth_difference_hasLaw
