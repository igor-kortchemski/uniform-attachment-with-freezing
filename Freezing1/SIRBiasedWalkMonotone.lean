module

public import Freezing1.SIRBiasedWalkExtinction
public import Freezing1.PlaneGraftHistory

/-!
# Monotone coupling of genuine absorbed biased walks

A single three-atom transition couples attachment probabilities p ≤ q.
Both projected infinite path laws are the actual biased-walk laws. Thus
extinction probabilities can be compared without an assumed coupling.
-/

@[expose] public section

namespace Freezing1.SIR.BiasedWalk

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

def step (i : ℕ) (b : Bool) : ℕ := if i = 0 then 0 else if b then i + 1 else i - 1

theorem step_mono (b : Bool) : Monotone (fun i => step i b) := by
  intro i j hij
  cases b <;> by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [step, hi, hj] <;> omega

theorem step_false_le_true (i : ℕ) : step i false ≤ step i true := by
  by_cases hi : i = 0
  · simp [step, hi]
  · simp only [step, ite_eq_right hi, Bool.false_eq_true, ite_false, ite_true]
    omega

theorem transition_eq_step (p : unitInterval) (i : ℕ) :
    transition p i = bernoulliMeasure (step i true) (step i false) p := by
  by_cases hi : i = 0
  · simp [transition, step, hi]
  · simp [transition, step, hi]

private theorem weights_total {p q : unitInterval} (hpq : p ≤ q) :
    unitInterval.toNNReal p +
      (unitInterval.toNNReal q - unitInterval.toNNReal p) +
        unitInterval.toNNReal (unitInterval.symm q) = 1 := by
  have hpq' : unitInterval.toNNReal p ≤ unitInterval.toNNReal q := by exact_mod_cast hpq
  apply NNReal.coe_injective
  rw [NNReal.coe_add, NNReal.coe_add, NNReal.coe_sub hpq']
  simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq, NNReal.coe_one]
  ring

private theorem weights_down {p q : unitInterval} (hpq : p ≤ q) :
    (unitInterval.toNNReal q - unitInterval.toNNReal p) +
      unitInterval.toNNReal (unitInterval.symm q) =
        unitInterval.toNNReal (unitInterval.symm p) := by
  have hpq' : unitInterval.toNNReal p ≤ unitInterval.toNNReal q := by exact_mod_cast hpq
  apply NNReal.coe_injective
  rw [NNReal.coe_add, NNReal.coe_sub hpq']
  simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  ring

private theorem weights_up {p q : unitInterval} (hpq : p ≤ q) :
    unitInterval.toNNReal p + (unitInterval.toNNReal q - unitInterval.toNNReal p) =
      unitInterval.toNNReal q := by
  have hpq' : unitInterval.toNNReal p ≤ unitInterval.toNNReal q := by exact_mod_cast hpq
  exact add_tsub_cancel_of_le hpq'

noncomputable def coupledTransition (p q : unitInterval) (_hpq : p ≤ q) :
    Kernel (ℕ × ℕ) (ℕ × ℕ) where
  toFun z :=
    unitInterval.toNNReal p • Measure.dirac (step z.1 true, step z.2 true) +
      (unitInterval.toNNReal q - unitInterval.toNNReal p) •
        Measure.dirac (step z.1 false, step z.2 true) +
      unitInterval.toNNReal (unitInterval.symm q) •
        Measure.dirac (step z.1 false, step z.2 false)
  measurable' := measurable_of_countable _

instance coupledTransition_markov (p q : unitInterval) (hpq : p ≤ q) :
    IsMarkovKernel (coupledTransition p q hpq) := by
  constructor
  intro z
  constructor
  change (_ + _ + _ : Measure (ℕ × ℕ)) univ = 1
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    ENNReal.smul_def]
  rw [← ENNReal.coe_add, ← ENNReal.coe_add, weights_total hpq, ENNReal.coe_one]

theorem coupledTransition_fst (p q : unitInterval) (hpq : p ≤ q) (z : ℕ × ℕ) :
    (coupledTransition p q hpq z).map Prod.fst = transition p z.1 := by
  change ((_ + _ + _ : Measure (ℕ × ℕ)).map Prod.fst) = _
  simp only [Measure.map_add _ _ measurable_fst,
    Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_dirac' measurable_fst]
  rw [add_assoc, ← add_smul, weights_down hpq, transition_eq_step, bernoulliMeasure_def]

theorem coupledTransition_snd (p q : unitInterval) (hpq : p ≤ q) (z : ℕ × ℕ) :
    (coupledTransition p q hpq z).map Prod.snd = transition q z.2 := by
  change ((_ + _ + _ : Measure (ℕ × ℕ)).map Prod.snd) = _
  simp only [Measure.map_add _ _ measurable_snd,
    Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_dirac' measurable_snd]
  rw [← add_smul, weights_up hpq, transition_eq_step, bernoulliMeasure_def]

theorem coupledTransition_order (p q : unitInterval) (hpq : p ≤ q) (z : ℕ × ℕ)
    (hz : z.1 ≤ z.2) : ∀ᵐ w ∂coupledTransition p q hpq z, w.1 ≤ w.2 := by
  change ∀ᵐ w ∂(_ + _ + _ : Measure (ℕ × ℕ)), w.1 ≤ w.2
  rw [ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩, Measure.ae_smul_measure ?_ _⟩
  · exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr (step_mono true hz)
  · exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr
      ((step_mono false hz).trans (step_false_le_true z.2))
  · exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr (step_mono false hz)

noncomputable def coupledFullLaw (p q : unitInterval) (hpq : p ≤ q) : Measure (ℕ → ℕ × ℕ) :=
  CountableMarkovChain.fullLaw (coupledTransition p q hpq) (1, 1)

instance coupledFullLaw_probability (p q : unitInterval) (hpq : p ≤ q) :
    IsProbabilityMeasure (coupledFullLaw p q hpq) := by unfold coupledFullLaw; infer_instance

theorem coupledFullLaw_fst (p q : unitInterval) (hpq : p ≤ q) :
    (coupledFullLaw p q hpq).map (fun H k => (H k).1) = fullLaw p := by
  apply CountableMarkovChain.map_fullLaw_of_ae_intertwining
  intro k
  exact Filter.Eventually.of_forall fun H => coupledTransition_fst p q hpq (H k)

theorem coupledFullLaw_snd (p q : unitInterval) (hpq : p ≤ q) :
    (coupledFullLaw p q hpq).map (fun H k => (H k).2) = fullLaw q := by
  apply CountableMarkovChain.map_fullLaw_of_ae_intertwining
  intro k
  exact Filter.Eventually.of_forall fun H => coupledTransition_snd p q hpq (H k)

theorem coupledFullLaw_order (p q : unitInterval) (hpq : p ≤ q) :
    ∀ᵐ H ∂coupledFullLaw p q hpq, ∀ k, (H k).1 ≤ (H k).2 := by
  have hs := CountableMarkovChain.fullLaw_steps (coupledTransition p q hpq) (1, 1)
    (fun z w => z.1 ≤ z.2 → w.1 ≤ w.2) (fun z => by
      by_cases hz : z.1 ≤ z.2
      · exact (coupledTransition_order p q hpq z hz).mono fun w hw _ => hw
      · exact Filter.Eventually.of_forall fun w h => (hz h).elim)
  filter_upwards [hs, CountableMarkovChain.fullLaw_initial (coupledTransition p q hpq) (1, 1)]
    with H hH h0
  intro k
  induction k with
  | zero => simp [h0]
  | succ k ih => exact hH k ih

theorem zero_probability_antitone {p q : unitInterval} (hpq : p ≤ q) (k : ℕ) :
    fullLaw q {H | H k = 0} ≤ fullLaw p {H | H k = 0} := by
  rw [← coupledFullLaw_snd p q hpq, ← coupledFullLaw_fst p q hpq,
    Measure.map_apply (by fun_prop) (by measurability),
    Measure.map_apply (by fun_prop) (by measurability)]
  apply measure_mono_ae
  filter_upwards [coupledFullLaw_order p q hpq] with H hH hz
  exact Nat.eq_zero_of_le_zero (hz ▸ hH k)

end Freezing1.SIR.BiasedWalk
