module

import Freezing1.ReverseHistoryBlockCount

/-!
Independent literal-type probes for the reverse-history block count.
The displayed count uses the actual random root set, not a deterministic
label subset or an assumed probability. Transfer to the source's forward
cut-forest count is a separate obligation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
open Freezing1 Freezing1.ReverseHistory

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ birthTime n v) :
    IndepFun (fun H : History => (stage H a).depth v - (stage H b).depth v)
      (previous^[b]) (fullLaw x n) :=
  depth_difference_indep_past x n hn hv hab hb

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) (r : ℝ) :
    (∫ H, ((((stage H b).roots.filter fun v => r < ((stage H a).depth v : ℝ)).card : ℕ) : ℝ)
      ∂fullLaw x n) =
      (activeCount x b : ℝ) *
      (bernoulliPartialSumLaw
        (fun i : Fin b => Reverse.attachmentParameter x n hn ⟨i.val, i.isLt.trans_le hb⟩)
        (Finset.univ.filter fun i : Fin b => a ≤ i.val)).real
        {k : ℕ | r < (k : ℝ)} :=
  integral_blockTallRootCount x n hn hab hb r

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (a : ℕ) {b : ℕ} (hb : b ≤ n) (r : ℝ) :
    Integrable (fun H : History =>
      ((((stage H b).roots.filter fun v => r < ((stage H a).depth v : ℝ)).card : ℕ) : ℝ))
      (fullLaw x n) :=
  blockTallRootCount_integrable x n hn a hb r

#print axioms Freezing1.ReverseHistory.blockSum_indep_past
#print axioms Freezing1.ReverseHistory.depth_difference_indep_past
#print axioms Freezing1.ReverseHistory.depth_difference_event_and_root
#print axioms Freezing1.ReverseHistory.blockTallRootCount_integrable
#print axioms Freezing1.ReverseHistory.integral_blockTallRootCount
