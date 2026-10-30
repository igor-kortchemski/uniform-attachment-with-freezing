module

public import Freezing1.SIRCountLaw
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! A total measurable bounded hitting index. On the actual SIR history
law it is exactly the first infectious-population zero, because extinction
by `2*n+1` is a proved property of that law. -/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory
open scoped Classical NNReal

noncomputable def boundedExtinctionIndex (n : ℕ) (H : ℕ → Counts) : ℕ :=
  Nat.find (show ∃ i : ℕ, i = 2 * n + 1 ∨ (H i).infectious = 0 from
    ⟨2 * n + 1, Or.inl rfl⟩)

theorem boundedExtinctionIndex_le (n : ℕ) (H : ℕ → Counts) :
    boundedExtinctionIndex n H ≤ 2 * n + 1 :=
  Nat.find_min' _ (Or.inl rfl)

theorem measurable_boundedExtinctionIndex (n : ℕ) : Measurable (boundedExtinctionIndex n) := by
  unfold boundedExtinctionIndex
  apply measurable_find
  intro i
  by_cases hi : i = 2 * n + 1
  · simp only [hi, true_or, Set.ofPred_true]
    exact MeasurableSet.univ
  · simp only [hi, false_or]
    exact (measurableSet_singleton (0 : ℕ)).preimage
      ((measurable_of_countable (fun c : Counts => c.infectious)).comp (measurable_pi_apply i))

theorem boundedExtinctionIndex_zero (n : ℕ) (H : ℕ → Counts)
    (hterminal : (H (2 * n + 1)).infectious = 0) :
    (H (boundedExtinctionIndex n H)).infectious = 0 := by
  have hspec := Nat.find_spec (show ∃ i : ℕ, i = 2 * n + 1 ∨ (H i).infectious = 0 from
    ⟨2 * n + 1, Or.inl rfl⟩)
  change boundedExtinctionIndex n H = 2 * n + 1 ∨
    (H (boundedExtinctionIndex n H)).infectious = 0 at hspec
  rcases hspec with ht | hz
  · rw [ht]
    exact hterminal
  · exact hz

theorem boundedExtinctionIndex_pos_before (n : ℕ) (H : ℕ → Counts) {i : ℕ}
    (hi : i < boundedExtinctionIndex n H) : 0 < (H i).infectious := by
  have hn : ¬(i = 2 * n + 1 ∨ (H i).infectious = 0) := Nat.find_min _ hi
  exact Nat.pos_of_ne_zero (fun h => hn (Or.inr h))

theorem countsFullLaw_boundedExtinctionIndex_firstZero (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂countsFullLaw rate n,
      boundedExtinctionIndex n H ≤ 2 * n + 1 ∧
      (H (boundedExtinctionIndex n H)).infectious = 0 ∧
      ∀ i < boundedExtinctionIndex n H, 0 < (H i).infectious := by
  filter_upwards [countsFullLaw_absorbed_by rate n] with H hH
  exact ⟨boundedExtinctionIndex_le n H, boundedExtinctionIndex_zero n H hH.1,
    fun _ hi => boundedExtinctionIndex_pos_before n H hi⟩

end Freezing1.SIR
