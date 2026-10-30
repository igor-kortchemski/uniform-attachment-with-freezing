module

public import Freezing1.SIROneSusceptibleTimeCoupling

/-! Both exact marginals of the noncausal time/sign coupling. The iid
coordinate is not conditioned on the epidemic or on a future event. -/

@[expose] public section

namespace Freezing1.SIR.OneSusceptible

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem chosenTime_bounds (m : ℕ) (x : SignSequence) (hx : x ∈ lastNegativeGate m) :
    3 ≤ chosenTime m x ∧ chosenTime m x ≤ m := by
  have hle := lastNegative_le m x
  change 3 ≤ m + 3 - lastNegative m x ∧ m + 3 - lastNegative m x ≤ m
  change 3 ≤ lastNegative m x at hx
  omega

noncomputable def mainTimeLaw (p : unitInterval) (m : ℕ) : Measure ℕ :=
  (unitInterval.toNNReal (unitInterval.symm p)) ^ 2 •
    ((auxiliaryLaw p).restrict (lastNegativeGate m)).map (chosenTime m)

theorem mainTimeLaw_singleton_small_or_gt (p : unitInterval) (m t : ℕ)
    (ht : t < 3 ∨ m < t) : mainTimeLaw p m {t} = 0 := by
  have hs : (chosenTime m) ⁻¹' {t} ∩ lastNegativeGate m = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨he, hx⟩
    have hb := chosenTime_bounds m x hx
    omega
  unfold mainTimeLaw
  rw [Measure.smul_apply,
    Measure.map_apply (measurable_chosenTime m) (measurableSet_singleton t),
    Measure.restrict_apply ((measurableSet_singleton t).preimage (measurable_chosenTime m)), hs]
  simp

theorem mainTimeLaw_singleton (p : unitInterval) (m t : ℕ) (ht : 3 ≤ t) (htm : t ≤ m) :
    mainTimeLaw p m {t} = (unitInterval.toNNReal p : ℝ≥0∞) *
      (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^ (t - 1) := by
  let j := m + 3 - t
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hjm : j ≤ m := by dsimp [j]; omega
  have hs : (chosenTime m) ⁻¹' {t} ∩ lastNegativeGate m = {x | lastNegative m x = j} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    have hle := lastNegative_le m x
    change (m + 3 - lastNegative m x = t ∧ 3 ≤ lastNegative m x) ↔ lastNegative m x = j
    dsimp [j]
    omega
  unfold mainTimeLaw
  rw [Measure.smul_apply,
    Measure.map_apply (measurable_chosenTime m) (measurableSet_singleton t),
    Measure.restrict_apply ((measurableSet_singleton t).preimage (measurable_chosenTime m)), hs]
  change (unitInterval.toNNReal (unitInterval.symm p)) ^ 2 •
    (ForwardAnnealed.iidSignLaw (unitInterval.symm p)) {x | lastNegative m x = j} = _
  rw [iid_lastNegative_probability p m j hj hjm]
  simp only [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow]
  calc
    _ = (unitInterval.toNNReal p : ℝ≥0∞) *
        ((unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^ 2 *
          (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^ (m - j)) := by ac_rfl
    _ = _ := by
      rw [← pow_add]
      have he : 2 + (m - j) = t - 1 := by dsimp [j]; omega
      rw [he]

theorem timeSignCoupling_map_fst (p : unitInterval) (m : ℕ) (hm : 2 ≤ m) :
    (timeSignCoupling p m).map Prod.fst = firstTimeLaw p m := by
  unfold timeSignCoupling
  rw [Measure.map_add _ _ measurable_fst,
    Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_map measurable_fst (measurable_chosenTime_pair m),
    Measure.map_fst_prod, residualAuxLaw_mass p m hm]
  change mainTimeLaw p m + residualSize p m • residualTimeLaw p m = firstTimeLaw p m
  unfold residualTimeLaw
  rw [smul_smul, mul_inv_cancel₀ (residualSize_pos p m).ne', one_smul]
  apply Measure.ext_of_singleton
  intro t
  rw [Measure.add_apply]
  by_cases ht : t ≤ 2
  · rw [mainTimeLaw_singleton_small_or_gt p m t (Or.inl (by omega)), zero_add]
    interval_cases t
    · rw [firstTimeLaw_zero]
      simp [smallTimeLaw]
    · rw [firstTimeLaw_positive_singleton p m 1 (by omega) (by omega)]
      simp [smallTimeLaw]
    · rw [firstTimeLaw_positive_singleton p m 2 (by omega) hm]
      simp [smallTimeLaw]
  · have ht3 : 3 ≤ t := by omega
    have ht0 : t ≠ 0 := by omega
    have ht1 : t ≠ 1 := by omega
    have ht2 : t ≠ 2 := by omega
    have hs : smallTimeLaw p m {t} = 0 := by
      simp [smallTimeLaw, Ne.symm ht0, Ne.symm ht1, Ne.symm ht2]
    rw [hs, add_zero]
    by_cases htm : t ≤ m
    · rw [mainTimeLaw_singleton p m t ht3 htm,
        firstTimeLaw_positive_singleton p m t (by omega) htm]
    · rw [mainTimeLaw_singleton_small_or_gt p m t (Or.inr (by omega)),
        firstTimeLaw_singleton_gt p m t (by omega)]

theorem timeSignCoupling_probability (p : unitInterval) (m : ℕ) :
    IsProbabilityMeasure (timeSignCoupling p m) := by
  constructor
  have hh := congrArg (fun μ : Measure SignSequence => μ univ) (timeSignCoupling_map_snd p m)
  rw [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ] at hh
  have haux : auxiliaryLaw p univ = 1 := measure_univ
  rw [haux] at hh
  exact hh

end Freezing1.SIR.OneSusceptible
