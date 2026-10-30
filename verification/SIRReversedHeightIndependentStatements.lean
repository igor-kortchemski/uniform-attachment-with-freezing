module

import Freezing1.SIRReversedHeightIdentity

open scoped BigOperators

namespace Freezing1.SIR.ReversedHeightIndependentAudit

example (x : SignSequence) (I : ℕ → ℝ) (n τ : ℕ) :
    (∑ i ∈ Finset.Ico n τ, if x (i + 1) then 1 / I i else 0) =
      ∑ j ∈ Finset.Icc 1 (τ - n),
        if x (τ - j + 1) then 1 / I (τ - j) else 0 :=
  reverse_preStep_attachment_sum x I n τ

example (x : SignSequence) (τ i : ℕ) (hτ : activeCount x τ = 0) (hi : i ≤ τ) :
    (∑ j ∈ Finset.range i, -(if x (τ - j) then (1 : ℤ) else -1)) =
      activeCount x (τ - i) :=
  reverse_activeCount_partialSum x hτ i hi

example : SignWordFeasible 1 (![true, false, false] : Fin 3 → Bool) ∧
    ForwardAnnealed.wordSchedule (![true, false, false] : Fin 3 → Bool) =
      (fun i => decide (i = 1)) :=
  ⟨reverseIdentityExample_feasible, reverseIdentityExample_wordSchedule⟩

example :
    let x := ForwardAnnealed.wordSchedule (![true, false, false] : Fin 3 → Bool)
    let I : ℕ → ℝ := fun i => (activeCount x i : ℝ)
    (∑ i ∈ Finset.Ico 1 3, if x i then 1 / I i else 0) = 1 / 2 ∧
    (∑ j ∈ Finset.Icc 1 (3 - 1 : ℕ), if x (3 - j + 1) then 1 / I (3 - j) else 0) = 0 := by
  dsimp only
  rw [reverseIdentityExample_wordSchedule]
  exact printed_reverse_attachment_identity_counterexample

#print axioms reverse_preStep_attachment_sum
#print axioms reverse_activeCount_partialSum
#print axioms reverseIdentityExample_feasible
#print axioms reverseIdentityExample_wordSchedule
#print axioms printed_reverse_attachment_identity_counterexample

end Freezing1.SIR.ReversedHeightIndependentAudit
