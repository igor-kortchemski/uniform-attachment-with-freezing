module

import Freezing1.InterleavedSourceFactorization

/-! Independent reconstruction of the literal source first-selection
event, scalar restart factorization and absorbing two-term identity. -/

open MeasureTheory ProbabilityTheory
open Freezing1 Freezing1.InterleavedChain Freezing1.CountableMarkovChain
open scoped Classical

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

example (α : Kernel E E) [IsMarkovKernel α] (κ : E × E → unitInterval) (x y z : E) :
    (InterleavedChain.fullLaw α κ (x, y, true)) {H |
      ∃ n : ℕ, 0 < n ∧ (∀ m, 0 < m → m < n → (H m).2.2 = true) ∧
        (H n).2.2 = false ∧ (H n).2.1 = z} =
      (InterleavedChain.fullLaw α κ (x, y, true))
        {H | ∃ n : ℕ, 0 < n ∧ (H n).2.2 = false} * α y {z} := by
  have he : {H : ℕ → State E |
      ∃ n : ℕ, 0 < n ∧ (∀ m, 0 < m → m < n → (H m).2.2 = true) ∧
        (H n).2.2 = false ∧ (H n).2.1 = z} = firstSelectionValue false z := by
    ext H
    exact (first_right_value_literal H z).symm
  rw [he]
  exact firstSelectionValue_probability α κ x y z true false

example (α : Kernel E E) [IsMarkovKernel α] (κ : E × E → unitInterval)
    (hf : Fair α κ) (x y : E) (u v : List E) (z : E)
    (hv : ¬Absorbing α (v.getLastD y)) :
    (InterleavedChain.fullLaw α κ (x, y, true))
      {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v ∧
        extracted H false (v.length + 1) = z} =
      (InterleavedChain.fullLaw α κ (x, y, true))
        {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v} *
      (InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true))
        (firstSelectionValue false z) :=
  source_right_factorization_nonabsorbing α κ hf x y u v z hv

example (α : Kernel E E) [IsMarkovKernel α] (κ : E × E → unitInterval)
    (hf : Fair α κ) (x y : E) (u v : List E) (z : E)
    (hv : Absorbing α (v.getLastD y)) :
    let μ := InterleavedChain.fullLaw α κ (x, y, true)
    let ρ := InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true)
    let B := {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v}
    μ {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v ∧
      extracted H false (v.length + 1) = z} =
      μ B * ρ (everSelected false)ᶜ * (if v.getLastD y = z then 1 else 0) +
      μ B * ρ (everSelected false) * α (v.getLastD y) {z} :=
  source_right_factorization_absorbing α κ hf x y u v z hv

#print axioms firstSelectionValue_probability
#print axioms firstSelectionValue_probability_of_nonabsorbing
#print axioms source_right_factorization_nonabsorbing
#print axioms source_left_factorization_nonabsorbing
#print axioms source_right_factorization_absorbing
#print axioms source_left_factorization_absorbing
#print axioms fullLaw_selectedTime_strict_of_nonabsorbing
