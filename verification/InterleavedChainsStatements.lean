module

import Freezing1.InterleavedChainsIndependent

open Freezing1 MeasureTheory ProbabilityTheory
open Freezing1.InterleavedChain
open scoped Classical

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- The literal source hypotheses use probability one from every starting
triple whenever the relevant coordinate is not absorbing. -/
example (α : Kernel E E) [IsMarkovKernel α] (κ : E × E → unitInterval)
    (hl : ∀ x y i, α x {x} ≠ 1 →
      fullLaw α κ (x, y, i) {H | ∃ n : ℕ, 1 ≤ n ∧ (H n).2.2 = true} = 1)
    (hr : ∀ x y i, α y {y} ≠ 1 →
      fullLaw α κ (x, y, i) {H | ∃ n : ℕ, 1 ≤ n ∧ (H n).2.2 = false} = 1)
    (x y : E) :
    (fullLaw α κ (x, y, true)).map
        (fun H => (extracted H true, extracted H false)) =
      (CountableMarkovChain.fullLaw α x).prod (CountableMarkovChain.fullLaw α y) := by
  apply extracted_pair_map_eq_prod
  constructor
  · intro x y i hx
    have hm : Measurable (fun H : ℕ → State E => ∃ n : ℕ, 0 < n ∧ (H n).2.2 = true) := by
      apply Measurable.exists
      intro n
      exact measurable_const.and ((measurable_pi_apply n).snd.snd.eq measurable_const)
    apply (ae_iff_prob_eq_one hm).mpr
    simpa only [Nat.lt_iff_add_one_le, zero_add] using hl x y i hx
  · intro x y i hy
    have hm : Measurable (fun H : ℕ → State E => ∃ n : ℕ, 0 < n ∧ (H n).2.2 = false) := by
      apply Measurable.exists
      intro n
      exact measurable_const.and ((measurable_pi_apply n).snd.snd.eq measurable_const)
    apply (ae_iff_prob_eq_one hm).mpr
    simpa only [Nat.lt_iff_add_one_le, zero_add] using hr x y i hy

example (marks : ℕ → Bool) (side : Bool) (k : ℕ)
    (h : ∀ n, selectedTime marks side k < n → marks n ≠ side) :
    selectedTime marks side (k + 1) = selectedTime marks side k :=
  nextTime_of_none marks side _ h

#print axioms Freezing1.InterleavedChain.transition_left_singleton
#print axioms Freezing1.InterleavedChain.transition_right_singleton
#print axioms Freezing1.InterleavedChain.measurable_extracted
#print axioms Freezing1.InterleavedChain.lintegral_pairCompletion_observations
#print axioms Freezing1.InterleavedChain.completion_observed_eventually
#print axioms Freezing1.InterleavedChain.fullLaw_pathFair
#print axioms Freezing1.InterleavedChain.extractedWord_pair_probability
#print axioms Freezing1.CountableMarkovChain.futureWord_probability
#print axioms Freezing1.CountablePathLaw.pair_eq_of_word_probabilities
#print axioms Freezing1.InterleavedChain.extracted_pair_map_eq_prod
#print axioms Freezing1.InterleavedChain.extracted_pair_hasLaw
