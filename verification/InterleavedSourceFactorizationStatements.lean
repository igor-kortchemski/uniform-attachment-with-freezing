module

import Freezing1.InterleavedSourceFactorization

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Classical

noncomputable section

namespace Freezing1.InterleavedChain.SourceFactorizationStatementCheck

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

example (α : Kernel E E) [IsMarkovKernel α] (κ : E × E → unitInterval)
    (x y z : E) (i side : Bool) :
    (InterleavedChain.fullLaw α κ (x, y, i)) (firstSelectionValue side z) =
      (InterleavedChain.fullLaw α κ (x, y, i)) (everSelected side) *
        α (coordinate (x, y, i) side) {z} :=
  firstSelectionValue_probability α κ x y z i side

example (α : Kernel E E) [IsMarkovKernel α] (κ : E × E → unitInterval)
    (hf : Fair α κ) (x y : E) (u v : List E) (z : E)
    (hv : ¬CountableMarkovChain.Absorbing α (v.getLastD y)) :
    (InterleavedChain.fullLaw α κ (x, y, true))
      {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v ∧
        extracted H false (v.length + 1) = z} =
      (InterleavedChain.fullLaw α κ (x, y, true))
        {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v} *
      (InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true))
        {H | ∃ n : ℕ, 0 < n ∧ (∀ m, 0 < m → m < n → (H m).2.2 = true) ∧
          (H n).2.2 = false ∧ (H n).2.1 = z} := by
  have he : firstSelectionValue false z =
      {H : ℕ → State E | ∃ n : ℕ, 0 < n ∧
        (∀ m, 0 < m → m < n → (H m).2.2 = true) ∧ (H n).2.2 = false ∧ (H n).2.1 = z} := by
    ext H
    exact first_right_value_literal H z
  rw [← he]
  exact source_right_factorization_nonabsorbing α κ hf x y u v z hv

example (α : Kernel E E) [IsMarkovKernel α] (κ : E × E → unitInterval)
    (hf : Fair α κ) (x y : E) (u v : List E) (z : E)
    (hv : CountableMarkovChain.Absorbing α (v.getLastD y)) :
    let μ := InterleavedChain.fullLaw α κ (x, y, true)
    let ρ := InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true)
    let B := {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v}
    μ {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v ∧
      extracted H false (v.length + 1) = z} =
      μ B * ρ {H | ∀ n : ℕ, 0 < n → (H n).2.2 = true} *
        (if v.getLastD y = z then 1 else 0) +
      μ B * ρ {H | ∃ n : ℕ, 0 < n ∧ (H n).2.2 = false} * α (v.getLastD y) {z} := by
  have he : (everSelected (E := E) false)ᶜ =
      {H : ℕ → State E | ∀ n : ℕ, 0 < n → (H n).2.2 = true} := by
    ext H
    exact never_right_selected_literal H
  have hh := source_right_factorization_absorbing α κ hf x y u v z hv
  simp only [he] at hh
  unfold everSelected at hh
  exact hh

example (α : Kernel E E) [IsMarkovKernel α] (κ : E × E → unitInterval)
    (hf : Fair α κ) (x y z : E) (i : Bool) :
    (InterleavedChain.fullLaw α κ (x, y, i)) {H | extracted H false 1 = z} = α y {z} := by
  simpa [extractedWord] using source_right_prefix_transition α κ hf x y i [] [] z

example (α : Kernel E E) [IsMarkovKernel α] (κ : E × E → unitInterval)
    (hf : Fair α κ) (x y : E) (u v : List E) (z : E)
    (hu : ¬CountableMarkovChain.Absorbing α (u.getLastD x)) :
    (InterleavedChain.fullLaw α κ (x, y, true))
      {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v ∧
        extracted H true (u.length + 1) = z} =
      (InterleavedChain.fullLaw α κ (x, y, true))
        {H | extractedWord H true u.length = u ∧ extractedWord H false v.length = v} *
      (InterleavedChain.fullLaw α κ (u.getLastD x, v.getLastD y, true))
        (firstSelectionValue true z) :=
  source_left_factorization_nonabsorbing α κ hf x y u v z hu

example (α : Kernel E E) [IsMarkovKernel α] (κ : E × E → unitInterval)
    (hf : Fair α κ) (s : State E) (side : Bool) :
    ∀ᵐ H ∂InterleavedChain.fullLaw α κ s, ∀ k,
      ¬CountableMarkovChain.Absorbing α (extracted H side k) →
        selectedTime (fun n => (H n).2.2) side k <
          selectedTime (fun n => (H n).2.2) side (k + 1) :=
  fullLaw_selectedTime_strict_of_nonabsorbing α κ hf s side

#print axioms firstSelectionValue_iff
#print axioms completion_observed_singleton_eventually
#print axioms firstSelectionValue_probability
#print axioms everSelected_probability_eq_one
#print axioms source_right_prefix_transition
#print axioms source_left_prefix_transition
#print axioms source_right_factorization_nonabsorbing
#print axioms source_left_factorization_nonabsorbing
#print axioms source_right_factorization_absorbing
#print axioms source_left_factorization_absorbing
#print axioms first_right_value_literal
#print axioms never_right_selected_literal
#print axioms fullLaw_selectedTime_strict_of_nonabsorbing

end Freezing1.InterleavedChain.SourceFactorizationStatementCheck
