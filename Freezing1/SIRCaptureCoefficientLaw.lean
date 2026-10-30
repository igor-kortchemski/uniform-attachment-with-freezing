module

public import Freezing1.SIRCaptureCoefficientWordBirth
public import Freezing1.SIRCaptureCoefficientProbability
public import Freezing1.ReversePairHeightTails

/-! Exact same-epsilon capture for the actual adaptive reverse-label sample law. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal Topology

set_option backward.isDefEq.respectTransparency false

/-- Every word of positive actual probability uses the genuine uniform
reverse-label law at its actual first-zero index. The unused infeasible
inputs are completed to probability measures. -/
noncomputable def wordReverseBirthKernel (n : ℕ) (w : Fin (2 * n + 1) → Bool) : Measure ℕ :=
  if SignWordFeasible n w then
    (uniformVertex (ForwardAnnealed.wordSchedule w) (captureWordExtinction n w)).map
      (birthTime (captureWordExtinction n w))
  else Measure.dirac 0

instance wordReverseBirthKernel_probability (n : ℕ) (w : Fin (2 * n + 1) → Bool) :
    IsProbabilityMeasure (wordReverseBirthKernel n w) := by
  unfold wordReverseBirthKernel
  split_ifs with hw
  · have hs := captureWordExtinction_spec n w hw
    have : IsProbabilityMeasure (uniformVertex (ForwardAnnealed.wordSchedule w)
        (captureWordExtinction n w)) := uniformVertex_isProbabilityMeasure
      (activeCount_nonneg_of_le_extinctionTime hs.2.1.symm.le)
    exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
      |>.mpr inferInstance
  · infer_instance

noncomputable def terminalReverseBirthLaw (r : ℝ≥0) (n : ℕ) : Measure ℕ :=
  (signWordLaw r n (2 * n + 1)).bind (wordReverseBirthKernel n)

instance terminalReverseBirthLaw_probability (r : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (terminalReverseBirthLaw r n) :=
  isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Eventually.of_forall fun _ => inferInstance)

theorem wordReverseBirthKernel_tail (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) (k : ℕ) :
    (wordReverseBirthKernel n w).real {j | k ≤ j} =
      reverseMissingFraction n k (wordCountsAt n w) := by
  rw [wordReverseBirthKernel, ite_eq_left hw,
    map_measureReal_apply (measurable_of_countable _) ((Set.to_countable _).measurableSet)]
  exact captureWord_reverse_birth_failure n w hw k

theorem terminalReverseBirthLaw_tail_eq_integral (r : ℝ≥0) (n k : ℕ) :
    (terminalReverseBirthLaw r n).real {j | k ≤ j} =
      ∫ w, reverseMissingFraction n k (wordCountsAt n w) ∂signWordLaw r n (2 * n + 1) := by
  have hb (j : ℕ) : 0 ≤ (if k ≤ j then (1 : ℝ) else 0) ∧
      (if k ≤ j then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hi : Integrable (fun j : ℕ => if k ≤ j then (1 : ℝ) else 0)
      (terminalReverseBirthLaw r n) :=
    integrable_unitInterval_function _ (measurable_of_countable _) hb
  rw [← integral_ite_indicator (terminalReverseBirthLaw r n) (fun j : ℕ => k ≤ j)
    ((Set.to_countable _).measurableSet)]
  change (∫ j : ℕ, (if k ≤ j then (1 : ℝ) else 0)
    ∂(signWordLaw r n (2 * n + 1)).bind (wordReverseBirthKernel n)) = _
  rw [integral_bind_of_integrable _ _ (measurable_of_countable _) hi]
  apply integral_congr_ae
  filter_upwards [signWordLaw_feasible r n (2 * n + 1)] with w hw
  rw [integral_ite_indicator _ (fun j : ℕ => k ≤ j) ((Set.to_countable _).measurableSet),
    wordReverseBirthKernel_tail n w hw k]

theorem terminalReverseBirthLaw_tail_eq_counts_integral (r : ℝ≥0) (n k : ℕ)
    (hk : k ≤ 2 * n + 1) :
    (terminalReverseBirthLaw r n).real {j | k ≤ j} =
      ∫ H, reverseMissingFraction n k H ∂countsFullLaw r n := by
  rw [terminalReverseBirthLaw_tail_eq_integral, signWordLaw_reverseMissing_integral_eq r n k hk]

/-- The literal unconditional coefficient in source A77, for every meaningful
fixed epsilon. It is stronger than its displayed liminf formulation. -/
theorem terminalReverseBirthLaw_same_epsilon (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      1 - eps ≤ (terminalReverseBirthLaw (rate n) n).real
        {j | (j : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} := by
  have ht : 0 < fluidExtinctionTime lam - eps := sub_pos.mpr hepsT
  have ht2 : fluidExtinctionTime lam - eps ≤ 2 := by
    have hh := (fluidExtinctionTime_spec hlam).2.1
    linarith only [hh, heps]
  filter_upwards [countsFullLaw_reverseMissing_same_epsilon rate lam hlam hscaled heps hepsT]
    with n hn
  let k : ℕ := ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊
  have hk : k ≤ 2 * n + 1 := by
    have h := StoppedCoupling.floor_time_index_le (n := n) (m := 2) ht2
    dsimp only [k]
    omega
  have htail : (terminalReverseBirthLaw (rate n) n).real {j | k ≤ j} < eps := by
    rw [terminalReverseBirthLaw_tail_eq_counts_integral _ _ _ hk]
    exact hn
  let A : Set ℕ := {j | (j : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)}
  have hsub : Aᶜ ⊆ {j | k ≤ j} := by
    intro j hj
    have hj' : (n : ℝ) * (fluidExtinctionTime lam - eps) < j := lt_of_not_ge hj
    have hf : (k : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps) :=
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) ht.le)
    exact_mod_cast (hf.trans hj'.le)
  have hcomp := (measureReal_mono hsub).trans_lt htail
  rw [probReal_compl_eq_one_sub ((Set.to_countable A).measurableSet)] at hcomp
  change 1 - eps ≤ (terminalReverseBirthLaw (rate n) n).real A
  linarith only [hcomp]

end Freezing1.SIR
