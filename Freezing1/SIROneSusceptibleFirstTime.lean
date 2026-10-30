module

public import Freezing1.SIROneSusceptibleLaw
public import Freezing1.SIRCountsExtinctionIndex

/-! Derived first-infection masses and exact extinction/reversed-birth
identities for the actual one-susceptible stopped trajectories. -/

@[expose] public section

namespace Freezing1.SIR.OneSusceptible

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem firstTimeShift_preimage_zero : firstTimeShift ⁻¹' ({0} : Set ℕ) = {0} := by
  ext t
  by_cases ht : t = 0 <;> simp [firstTimeShift, ht]

theorem firstTimeShift_preimage_one : firstTimeShift ⁻¹' ({1} : Set ℕ) = ∅ := by
  ext t
  by_cases ht : t = 0 <;> simp [firstTimeShift, ht]

theorem firstTimeShift_preimage_add_two (t : ℕ) :
    firstTimeShift ⁻¹' ({t + 2} : Set ℕ) = {t + 1} := by
  ext k
  by_cases hk : k = 0 <;> simp [firstTimeShift, hk]

theorem firstTimeLaw_succ_apply (p : unitInterval) (m : ℕ) (A : Set ℕ) :
    firstTimeLaw p (m + 1) A =
      (unitInterval.toNNReal p : ℝ≥0∞) * Measure.dirac (1 : ℕ) A +
      (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) *
        firstTimeLaw p m (firstTimeShift ⁻¹' A) := by
  rw [firstTimeLaw]
  change (unitInterval.toNNReal p : ℝ≥0∞) * Measure.dirac (1 : ℕ) A +
    (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) *
    ((firstTimeLaw p m).map firstTimeShift) A = _
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable A).measurableSet]

theorem firstTimeLaw_zero (p : unitInterval) (m : ℕ) :
    firstTimeLaw p m {0} = (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^ m := by
  induction m with
  | zero => simp [firstTimeLaw]
  | succ m ih =>
    rw [firstTimeLaw_succ_apply, firstTimeShift_preimage_zero, ih]
    simp [pow_succ, mul_comm]

theorem firstTimeLaw_positive_singleton (p : unitInterval) (m t : ℕ)
    (ht : 1 ≤ t) (htm : t ≤ m) :
    firstTimeLaw p m {t} = (unitInterval.toNNReal p : ℝ≥0∞) *
      (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^ (t - 1) := by
  induction m generalizing t with
  | zero => omega
  | succ m ih =>
    by_cases ht1 : t = 1
    · subst t
      rw [firstTimeLaw_succ_apply, firstTimeShift_preimage_one]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
      rw [firstTimeLaw_succ_apply, firstTimeShift_preimage_add_two,
        ih (k + 1) (by omega) (by omega)]
      simp [pow_succ, mul_comm, mul_left_comm]

theorem firstTimeLaw_singleton_gt (p : unitInterval) (m t : ℕ) (ht : m < t) :
    firstTimeLaw p m {t} = 0 := by
  induction m generalizing t with
  | zero => simp [firstTimeLaw, show t ≠ 0 by omega]
  | succ m ih =>
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
    rw [firstTimeLaw_succ_apply, firstTimeShift_preimage_add_two, ih (k + 1) (by omega)]
    simp

theorem firstTimeLaw_supported (p : unitInterval) (m : ℕ) :
    ∀ᵐ t ∂firstTimeLaw p m, t ≤ m := by
  apply ae_iff_of_countable.mpr
  intro t ht
  by_contra hn
  exact ht (firstTimeLaw_singleton_gt p m t (Nat.lt_of_not_ge hn))

def terminalTime (m t : ℕ) : ℕ := if t = 0 then m else m + 2

noncomputable def extinctionIndex (m : ℕ) : History → ℕ := boundedExtinctionIndex (m + 2)

theorem run_firstZero (m t : ℕ) (htm : t ≤ m) :
    (run m t (terminalTime m t)).infectious = 0 ∧
      ∀ k < terminalTime m t, 0 < (run m t k).infectious := by
  by_cases ht0 : t = 0
  · subst t
    simp only [terminalTime, run, ite_true, true_or]
    refine ⟨?_, ?_⟩
    · simp
    · intro k hk
      exact Nat.sub_pos_of_lt hk
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
    have htend : ¬m + 2 < t := by omega
    simp only [terminalTime, run, ht0, false_or, ite_false]
    refine ⟨?_, ?_⟩
    · simp only [ite_eq_right htend, Nat.sub_self]
    · intro k hk
      by_cases hkt : k < t
      · rw [ite_eq_left hkt]
        exact Nat.sub_pos_of_lt (hkt.trans_le htm)
      · rw [ite_eq_right hkt]
        exact Nat.sub_pos_of_lt hk

theorem run_extinctionIndex (m t : ℕ) (htm : t ≤ m) :
    extinctionIndex m (run m t) = terminalTime m t := by
  unfold extinctionIndex boundedExtinctionIndex
  apply (Nat.find_eq_iff _).mpr
  refine ⟨Or.inr (run_firstZero m t htm).1, ?_⟩
  intro k hk hc
  rcases hc with hdeadline | hzero
  · have hb : terminalTime m t ≤ m + 2 := by unfold terminalTime; split_ifs <;> omega
    omega
  · exact ((run_firstZero m t htm).2 k hk).ne' hzero

theorem run_reverse_birth_iff (m t j : ℕ) (htm : t ≤ m) (_hj : 1 ≤ j) (hjm : j ≤ m) :
    (run m t (extinctionIndex m (run m t) - j)).infectious <
      (run m t (extinctionIndex m (run m t) - j + 1)).infectious ↔
        t ≠ 0 ∧ j = m + 3 - t := by
  rw [run_extinctionIndex m t htm]
  by_cases ht0 : t = 0
  · subst t
    simpa [terminalTime, run] using
      (not_lt_of_ge (Nat.sub_le_sub_left (Nat.le_succ (m - j)) m))
  · simp only [terminalTime, run, ht0, false_or, ite_false, ne_eq, not_false_eq_true, true_and]
    split_ifs <;> dsimp only <;> omega

theorem run_reverse_birth_impossible_of_le_two (m t j : ℕ) (htm : t ≤ m)
    (ht2 : t ≤ 2) (hj : 1 ≤ j) (hjm : j ≤ m) :
    ¬ (run m t (extinctionIndex m (run m t) - j)).infectious <
      (run m t (extinctionIndex m (run m t) - j + 1)).infectious := by
  rw [run_reverse_birth_iff m t j htm hj hjm]
  omega

end Freezing1.SIR.OneSusceptible
