module

public import Freezing1.CountableMarkovObservations
public import Freezing1.CountableMarkovAvoidance
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# Extinction of the actual absorbed biased walk

The walk starts at one and holds at zero. A harmonic exponential and a
strictly contracting exponential, masked off at zero, determine its genuine
extinction probabilities. No survival or random-walk limit is assumed.
-/

@[expose] public section

namespace Freezing1.SIR.BiasedWalk

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def transition (p : unitInterval) : Kernel ℕ ℕ where
  toFun i := if i = 0 then Measure.dirac 0 else bernoulliMeasure (i + 1) (i - 1) p
  measurable' := measurable_of_countable _

instance transition_markov (p : unitInterval) : IsMarkovKernel (transition p) := by
  constructor
  intro i
  change IsProbabilityMeasure (if i = 0 then Measure.dirac 0 else
    bernoulliMeasure (i + 1) (i - 1) p)
  split_ifs <;> infer_instance

noncomputable def fullLaw (p : unitInterval) : Measure (ℕ → ℕ) :=
  CountableMarkovChain.fullLaw (transition p) 1

instance fullLaw_probability (p : unitInterval) : IsProbabilityMeasure (fullLaw p) := by
  unfold fullLaw
  infer_instance

theorem transition_lintegral (p : unitInterval) (i : ℕ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ j, f j ∂transition p i = if i = 0 then f 0 else
      (unitInterval.toNNReal p : ℝ≥0∞) * f (i + 1) +
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) * f (i - 1) := by
  by_cases hi : i = 0
  · simp [transition, hi]
  · change (∫⁻ j, f j ∂(if i = 0 then Measure.dirac 0 else
      bernoulliMeasure (i + 1) (i - 1) p)) = _
    simp only [ite_eq_right hi, bernoulliMeasure_def, lintegral_add_measure,
      lintegral_smul_measure, lintegral_dirac, ENNReal.smul_def, smul_eq_mul]

theorem fullLaw_lintegral_succ (p : unitInterval) (k : ℕ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ H, f (H (k + 1)) ∂fullLaw p =
      ∫⁻ H, ∫⁻ j, f j ∂transition p (H k) ∂fullLaw p :=
  CountableMarkovChain.lintegral_accumulate_succ (transition p) 1 ()
    (fun _ _ => ()) (fun _ => f) k

private theorem weighted_ofReal (p : unitInterval) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (unitInterval.toNNReal p : ℝ≥0∞) * ENNReal.ofReal a +
      (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) * ENNReal.ofReal b =
      ENNReal.ofReal ((p : ℝ) * a + (1 - (p : ℝ)) * b) := by
  rw [ENNReal.ofReal_add (mul_nonneg p.property.1 ha)
    (mul_nonneg (unitInterval.one_sub_nonneg _) hb),
    ENNReal.ofReal_mul p.property.1,
    ENNReal.ofReal_mul (unitInterval.one_sub_nonneg _)]
  simp only [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal,
    unitInterval.coe_symm_eq]

theorem transition_power_harmonic (p : unitInterval) {r : ℝ}
    (hr : 0 ≤ r) (hodds : (p : ℝ) * r = 1 - (p : ℝ)) (i : ℕ) :
    ∫⁻ j, ENNReal.ofReal (r ^ j) ∂transition p i = ENNReal.ofReal (r ^ i) := by
  rw [transition_lintegral]
  split_ifs with hi
  · rw [hi]
  · rw [weighted_ofReal p (pow_nonneg hr _) (pow_nonneg hr _)]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    congr 1
    simp only [Nat.succ_sub_one, pow_succ]
    calc
      _ = r ^ j * r + r ^ j * (r - 1) * ((p : ℝ) * r - (1 - (p : ℝ))) := by ring
      _ = _ := by rw [hodds, sub_self]; ring

theorem fullLaw_power_harmonic (p : unitInterval) {r : ℝ}
    (hr : 0 ≤ r) (hodds : (p : ℝ) * r = 1 - (p : ℝ)) (k : ℕ) :
    ∫⁻ H, ENNReal.ofReal (r ^ H k) ∂fullLaw p = ENNReal.ofReal r := by
  induction k with
  | zero =>
    calc
      _ = ∫⁻ _ : ℕ → ℕ, ENNReal.ofReal r ∂fullLaw p := by
        apply lintegral_congr_ae
        filter_upwards [CountableMarkovChain.fullLaw_initial (transition p) 1] with H hH
        simp [hH]
      _ = _ := by simp
  | succ k ih =>
    rw [fullLaw_lintegral_succ p k (fun i => ENNReal.ofReal (r ^ i))]
    simp_rw [transition_power_harmonic p hr hodds]
    exact ih

noncomputable def positivePower (q : ℝ) (i : ℕ) : ℝ := if i = 0 then 0 else q ^ i

theorem positivePower_nonneg {q : ℝ} (hq : 0 ≤ q) (i : ℕ) :
    0 ≤ positivePower q i := by unfold positivePower; split_ifs <;> positivity

theorem transition_positivePower_le (p : unitInterval) {q rho : ℝ}
    (hq : 0 < q) (hrho : 0 ≤ rho)
    (he : (p : ℝ) * q + (1 - (p : ℝ)) / q = rho) (i : ℕ) :
    ∫⁻ j, ENNReal.ofReal (positivePower q j) ∂transition p i ≤
      ENNReal.ofReal rho * ENNReal.ofReal (positivePower q i) := by
  rw [transition_lintegral]
  by_cases hi : i = 0
  · simp [hi, positivePower]
  · rw [ite_eq_right hi, weighted_ofReal p (positivePower_nonneg hq.le _)
      (positivePower_nonneg hq.le _), ← ENNReal.ofReal_mul hrho]
    apply ENNReal.ofReal_le_ofReal
    have hupper : positivePower q (i + 1) = q ^ (i + 1) := by simp [positivePower]
    have hlower : positivePower q (i - 1) ≤ q ^ (i - 1) := by
      unfold positivePower
      split_ifs
      · exact pow_nonneg hq.le _
      · exact le_rfl
    have hcurrent : positivePower q i = q ^ i := by simp [positivePower, hi]
    rw [hupper, hcurrent, ← he]
    calc
      _ ≤ (p : ℝ) * q ^ (i + 1) + (1 - (p : ℝ)) * q ^ (i - 1) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hlower (unitInterval.one_sub_nonneg p))
      _ = _ := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
        simp only [Nat.succ_sub_one, pow_succ]
        field_simp

theorem fullLaw_positivePower_le (p : unitInterval) {q rho : ℝ}
    (hq : 0 < q) (hrho : 0 ≤ rho)
    (he : (p : ℝ) * q + (1 - (p : ℝ)) / q = rho) (k : ℕ) :
    ∫⁻ H, ENNReal.ofReal (positivePower q (H k)) ∂fullLaw p ≤
      ENNReal.ofReal (rho ^ k * q) := by
  induction k with
  | zero =>
    calc
      _ = ∫⁻ _ : ℕ → ℕ, ENNReal.ofReal q ∂fullLaw p := by
        apply lintegral_congr_ae
        filter_upwards [CountableMarkovChain.fullLaw_initial (transition p) 1] with H hH
        simp [hH, positivePower]
      _ = _ := by simp
      _ ≤ _ := le_rfl
  | succ k ih =>
    rw [fullLaw_lintegral_succ p k (fun i => ENNReal.ofReal (positivePower q i))]
    calc
      _ ≤ ∫⁻ H, ENNReal.ofReal rho * ENNReal.ofReal (positivePower q (H k)) ∂fullLaw p :=
        lintegral_mono fun H => transition_positivePower_le p hq hrho he _
      _ = ENNReal.ofReal rho * ∫⁻ H, ENNReal.ofReal (positivePower q (H k)) ∂fullLaw p :=
        lintegral_const_mul _ ((measurable_of_countable
          (fun i : ℕ => ENNReal.ofReal (positivePower q i))).comp (measurable_pi_apply k))
      _ ≤ ENNReal.ofReal rho * ENNReal.ofReal (rho ^ k * q) := mul_le_mul' le_rfl ih
      _ = _ := by rw [← ENNReal.ofReal_mul hrho, pow_succ]; congr 1; ring

end Freezing1.SIR.BiasedWalk
