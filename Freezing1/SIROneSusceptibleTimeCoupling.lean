module

public import Freezing1.SIROneSusceptibleFirstTime
public import Freezing1.SIROneSusceptibleLastNegative

/-! A genuine joint first-infection-time / iid-sign law. Its main part
thins the last iid negative by q²; its residual part uses only times
zero, one and two, whose reversed births lie outside the prefix. -/

@[expose] public section

namespace Freezing1.SIR.OneSusceptible

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def auxiliaryLaw (p : unitInterval) : Measure SignSequence :=
  ForwardAnnealed.iidSignLaw (unitInterval.symm p)

instance auxiliaryLaw_probability (p : unitInterval) : IsProbabilityMeasure (auxiliaryLaw p) := by
  unfold auxiliaryLaw
  infer_instance

noncomputable def residualSize (p : unitInterval) (m : ℕ) : ℝ≥0 :=
  (unitInterval.toNNReal (unitInterval.symm p)) ^ m + unitInterval.toNNReal p +
    unitInterval.toNNReal p * unitInterval.toNNReal (unitInterval.symm p)

noncomputable def smallTimeLaw (p : unitInterval) (m : ℕ) : Measure ℕ :=
  (unitInterval.toNNReal (unitInterval.symm p)) ^ m • Measure.dirac 0 +
    unitInterval.toNNReal p • Measure.dirac 1 +
    (unitInterval.toNNReal p * unitInterval.toNNReal (unitInterval.symm p)) • Measure.dirac 2

noncomputable def residualTimeLaw (p : unitInterval) (m : ℕ) : Measure ℕ :=
  (residualSize p m)⁻¹ • smallTimeLaw p m

noncomputable def residualAuxLaw (p : unitInterval) (m : ℕ) : Measure SignSequence :=
  (1 - (unitInterval.toNNReal (unitInterval.symm p)) ^ 2) • auxiliaryLaw p +
    (unitInterval.toNNReal (unitInterval.symm p)) ^ 2 •
      (auxiliaryLaw p).restrict (lastNegativeGate m)ᶜ

def chosenTime (m : ℕ) (x : SignSequence) : ℕ := m + 3 - lastNegative m x

theorem measurable_chosenTime (m : ℕ) : Measurable (chosenTime m) :=
  (measurable_of_countable (fun j : ℕ => m + 3 - j)).comp (measurable_lastNegative m)

theorem measurable_chosenTime_pair (m : ℕ) :
    Measurable (fun x : SignSequence => (chosenTime m x, x)) :=
  (measurable_chosenTime m).prodMk measurable_id

noncomputable def timeSignCoupling (p : unitInterval) (m : ℕ) : Measure (ℕ × SignSequence) :=
  (unitInterval.toNNReal (unitInterval.symm p)) ^ 2 •
      ((auxiliaryLaw p).restrict (lastNegativeGate m)).map (fun x => (chosenTime m x, x)) +
    (residualTimeLaw p m).prod (residualAuxLaw p m)

instance smallTimeLaw_finite (p : unitInterval) (m : ℕ) : IsFiniteMeasure (smallTimeLaw p m) := by
  unfold smallTimeLaw
  infer_instance

instance residualTimeLaw_finite (p : unitInterval) (m : ℕ) : IsFiniteMeasure (residualTimeLaw p m) := by
  unfold residualTimeLaw
  infer_instance

instance residualAuxLaw_finite (p : unitInterval) (m : ℕ) : IsFiniteMeasure (residualAuxLaw p m) := by
  unfold residualAuxLaw
  infer_instance

theorem positiveWeight_square_le_one (p : unitInterval) :
    (unitInterval.toNNReal (unitInterval.symm p)) ^ 2 ≤ 1 := by
  have hq : unitInterval.toNNReal (unitInterval.symm p) ≤ 1 := by
    exact_mod_cast (unitInterval.symm p).property.2
  exact pow_le_one₀ (by positivity) hq

theorem positiveWeight_deficit (p : unitInterval) :
    1 - (unitInterval.toNNReal (unitInterval.symm p)) ^ 2 =
      unitInterval.toNNReal p + unitInterval.toNNReal p * unitInterval.toNNReal (unitInterval.symm p) := by
  let P := unitInterval.toNNReal p
  let Q := unitInterval.toNNReal (unitInterval.symm p)
  have hpq : P + Q = 1 := unitInterval.toNNReal_add_toNNReal_symm p
  apply tsub_eq_of_eq_add
  change 1 = (P + P * Q) + Q ^ 2
  calc
    1 = P + Q * (P + Q) := by rw [hpq, mul_one, hpq]
    _ = _ := by ring

theorem residualSize_pos (p : unitInterval) (m : ℕ) : 0 < residualSize p m := by
  by_cases hp : unitInterval.toNNReal p = 0
  · have hq : unitInterval.toNNReal (unitInterval.symm p) = 1 := by
      simpa only [hp, zero_add] using unitInterval.toNNReal_add_toNNReal_symm p
    simp [residualSize, hp, hq]
  · have hp0 : 0 < unitInterval.toNNReal p := pos_iff_ne_zero.mpr hp
    unfold residualSize
    positivity

theorem smallTimeLaw_mass (p : unitInterval) (m : ℕ) :
    smallTimeLaw p m univ = (residualSize p m : ℝ≥0∞) := by
  simp [smallTimeLaw, residualSize, ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_pow]

theorem residualTimeLaw_mass (p : unitInterval) (m : ℕ) : residualTimeLaw p m univ = 1 := by
  have hD : residualSize p m ≠ 0 := (residualSize_pos p m).ne'
  unfold residualTimeLaw
  rw [Measure.smul_apply, smallTimeLaw_mass]
  change ((residualSize p m)⁻¹ * residualSize p m : ℝ≥0) = (1 : ℝ≥0∞)
  rw [inv_mul_cancel₀ hD]
  rfl

theorem residualAuxLaw_mass (p : unitInterval) (m : ℕ) (hm : 2 ≤ m) :
    residualAuxLaw p m univ = (residualSize p m : ℝ≥0∞) := by
  unfold residualAuxLaw
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one,
    Measure.restrict_apply_univ]
  rw [show auxiliaryLaw p = ForwardAnnealed.iidSignLaw (unitInterval.symm p) from rfl,
    iid_lastNegativeGate_compl_probability]
  have hpow : (unitInterval.toNNReal (unitInterval.symm p)) ^ 2 *
      (unitInterval.toNNReal (unitInterval.symm p)) ^ (m - 2) =
        (unitInterval.toNNReal (unitInterval.symm p)) ^ m := by
    rw [← pow_add, Nat.add_sub_of_le hm]
  have hcalc : (1 - (unitInterval.toNNReal (unitInterval.symm p)) ^ 2) +
      (unitInterval.toNNReal (unitInterval.symm p)) ^ 2 *
        (unitInterval.toNNReal (unitInterval.symm p)) ^ (m - 2) = residualSize p m := by
    rw [hpow, positiveWeight_deficit]
    unfold residualSize
    ring
  exact_mod_cast hcalc

theorem timeSignCoupling_map_snd (p : unitInterval) (m : ℕ) :
    (timeSignCoupling p m).map Prod.snd = auxiliaryLaw p := by
  unfold timeSignCoupling
  rw [Measure.map_add _ _ measurable_snd,
    Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_map measurable_snd (measurable_chosenTime_pair m),
    Measure.map_snd_prod, residualTimeLaw_mass, one_smul]
  change (unitInterval.toNNReal (unitInterval.symm p)) ^ 2 •
      ((auxiliaryLaw p).restrict (lastNegativeGate m)).map id + residualAuxLaw p m = auxiliaryLaw p
  rw [Measure.map_id]
  unfold residualAuxLaw
  calc
    _ = (1 - (unitInterval.toNNReal (unitInterval.symm p)) ^ 2) • auxiliaryLaw p +
        (unitInterval.toNNReal (unitInterval.symm p)) ^ 2 •
          ((auxiliaryLaw p).restrict (lastNegativeGate m) +
            (auxiliaryLaw p).restrict (lastNegativeGate m)ᶜ) := by
      rw [smul_add]
      exact add_left_comm _ _ _
    _ = _ := by
      rw [Measure.restrict_add_restrict_compl (measurableSet_lastNegativeGate m),
        ← add_smul, tsub_add_cancel_of_le (positiveWeight_square_le_one p), one_smul]

end Freezing1.SIR.OneSusceptible
