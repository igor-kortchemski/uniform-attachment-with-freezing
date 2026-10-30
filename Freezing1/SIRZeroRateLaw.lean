module

public import Freezing1.SIRAbsorption

/-! The actual zero-rate embedded chain recovers its sole root and stops. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory CountableMarkovChain
open scoped ENNReal NNReal Classical

def frozenRootState (n : ℕ) : TreeState := recoverTreeState (initialTreeState n) []

def zeroRateTreePath (n k : ℕ) : TreeState :=
  if k = 0 then initialTreeState n else frozenRootState n

@[simp] theorem frozenRootState_active (n : ℕ) : (frozenRootState n).tree.active = ∅ := by
  simp [frozenRootState, recoverTreeState, initialTreeState, PlaneForward.freeze,
    PlaneForward.initial]

theorem signedTreeLaw_initial_recovery (n : ℕ) :
    signedTreeLaw (initialTreeState n) false = Measure.dirac (frozenRootState n) := by
  ext A hA
  rw [signedTreeLaw_apply _ _ (by simp [initialTreeState, PlaneForward.initial])]
  rw [Measure.dirac_apply' _ hA]
  rw [show (initialTreeState n).tree.active = {[]} from rfl,
    Finset.card_singleton, Nat.cast_one, div_one, Finset.filter_singleton]
  have hs : treeStep (initialTreeState n) false [] = frozenRootState n := by
    simp [treeStep, initialTreeState, PlaneForward.initial, frozenRootState]
  rw [hs]
  by_cases ha : frozenRootState n ∈ A <;> simp [ha]

theorem treeKernel_zero_initial (n : ℕ) :
    treeKernel 0 (initialTreeState n) = Measure.dirac (frozenRootState n) := by
  change (bernoulliMeasure true false (infectionProbability 0 n)).bind
    (signedTreeLaw (initialTreeState n)) = _
  rw [infectionProbability_zero_rate, bernoulliMeasure_zero,
    Measure.dirac_bind (measurable_of_countable _), signedTreeLaw_initial_recovery]

theorem treeFullLaw_zero_map_eval (n k : ℕ) :
    (treeFullLaw 0 n).map (fun H => H k) = Measure.dirac (zeroRateTreePath n k) := by
  induction k with
  | zero => exact CountableMarkovChain.map_eval_zero _ _
  | succ k ih =>
    change (CountableMarkovChain.fullLaw (treeKernel 0) (initialTreeState n)).map
      (fun H => H (k + 1)) = _
    rw [CountableMarkovChain.map_eval_succ]
    change ((treeFullLaw 0 n).map (fun H => H k)).bind (treeKernel 0) = _
    rw [ih, Measure.dirac_bind (treeKernel 0).measurable]
    cases k with
    | zero => exact treeKernel_zero_initial n
    | succ k =>
      change treeKernel 0 (frozenRootState n) = Measure.dirac (frozenRootState n)
      exact treeKernel_absorbed 0 (frozenRootState_active n)

theorem treeFullLaw_zero_path_ae (n : ℕ) :
    ∀ᵐ H ∂treeFullLaw 0 n, H = zeroRateTreePath n := by
  have hh : ∀ k, ∀ᵐ H ∂treeFullLaw 0 n, H k = zeroRateTreePath n k := by
    intro k
    have hl : HasLaw (fun H => H k) (Measure.dirac (zeroRateTreePath n k))
        (treeFullLaw 0 n) :=
      ⟨(measurable_pi_apply k).aemeasurable, treeFullLaw_zero_map_eval n k⟩
    exact hl.ae_eq_of_dirac
  exact (ae_all_iff.mpr hh).mono fun _ h => funext h

theorem treeFullLaw_zero_eq_dirac (n : ℕ) :
    treeFullLaw 0 n = Measure.dirac (zeroRateTreePath n) := by
  have hh : HasLaw (id : (ℕ → TreeState) → (ℕ → TreeState))
      (Measure.dirac (zeroRateTreePath n)) (treeFullLaw 0 n) :=
    hasLaw_dirac_of_ae_eq (treeFullLaw_zero_path_ae n)
  simpa only [Measure.map_id] using hh.map_eq

end Freezing1.SIR
