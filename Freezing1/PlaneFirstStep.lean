module

public import Freezing1.PlaneGraftShape
public import Freezing1.ForwardPlaneKernel
public import Freezing1.CountableMarkovAvoidance

/-!
# Exact first-step decomposition of the actual plane process

At the first attachment the state is a graft of two initial one-vertex
states. The first freezing step absorbs the one-vertex state forever.
The formula is unconditional and includes the zero-parameter endpoint.
-/

@[expose] public section

namespace Freezing1.PlaneForward

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem attach_initial_eq_graft : attach initial [] = graft initial initial := by
  simp only [attach, newChild, childCount_initial, List.nil_append]
  simp [initial, graft, shiftRoot]

theorem signedTransitionLaw_initial (sign : Bool) :
    signedTransitionLaw initial sign = Measure.dirac (step initial sign []) := by
  rw [signedTransitionLaw, ite_eq_left (by simp [initial] : initial.active.Nonempty)]
  simp [initial, Measure.uniformOfFinset]

theorem transition_initial (p : unitInterval) :
    transition p initial = unitInterval.toNNReal p • Measure.dirac (graft initial initial) +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac (freeze initial []) := by
  ext A hA
  rw [transition_apply_split, signedTransitionLaw_initial, signedTransitionLaw_initial]
  have ha : [] ∈ initial.active := by simp [initial]
  have ht : step initial true [] = graft initial initial := by
    rw [step, ite_eq_left ha]
    exact attach_initial_eq_graft
  have hf : step initial false [] = freeze initial [] := by
    rw [step, ite_eq_left ha]
    rfl
  rw [ht, hf]
  simp only [Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply]
  rfl

theorem fullLaw_eval_of_active_empty (p : unitInterval) (s : State)
    (hs : s.active = ∅) (n : ℕ) :
    (fullLaw p s).map (fun H => H n) = Measure.dirac s := by
  induction n with
  | zero => exact CountableMarkovChain.map_eval_zero _ _
  | succ n ih =>
    rw [fullLaw, CountableMarkovChain.map_eval_succ]
    change ((fullLaw p s).map (fun H => H n)).bind (transition p) = _
    rw [ih, Measure.dirac_bind (transition p).measurable,
      transition_eq_dirac_of_empty p hs]

theorem fullLaw_shape_frozen_initial (p : unitInterval) (n : ℕ) :
    (fullLaw p (freeze initial [])).map (fun H => shape (H n)) = Measure.dirac PlaneTree.leaf := by
  have hh := congrArg (fun μ : Measure State => μ.map shape)
    (fullLaw_eval_of_active_empty p (freeze initial []) (by simp [freeze, initial]) n)
  rw [Measure.map_map (measurable_of_countable _) (by fun_prop),
    Measure.map_dirac' (measurable_of_countable _), shape_freeze initial_valid, shape_initial] at hh
  exact hh

theorem fullLaw_shape_succ_bind (p : unitInterval) (s : State) (n : ℕ) :
    (fullLaw p s).map (fun H => shape (H (n + 1))) =
      (transition p s).bind (fun z => (fullLaw p z).map (fun H => shape (H n))) := by
  have hm : Measurable (fun H : ℕ → State => shape (H n)) :=
    (measurable_of_countable (shape : State → PlaneTree.Tree)).comp (measurable_pi_apply n)
  have hh := congrArg (fun μ : Measure (ℕ → State) => μ.map (fun H => shape (H n)))
    (CountableMarkovChain.fullLaw_map_shift_one (transition p) s)
  rw [Measure.map_map hm (CountableMarkovChain.measurable_shift 1),
    Measure.map_bind (measurable_of_countable _).aemeasurable hm.aemeasurable] at hh
  simpa only [fullLaw, Function.comp_def, CountableMarkovChain.shift, Nat.add_comm] using hh

theorem firstStep_shapeLaw (p : unitInterval) (n : ℕ) :
    (fullLaw p initial).map (fun H => shape (H (n + 1))) =
      unitInterval.toNNReal p •
        (fullLaw p (graft initial initial)).map (fun H => shape (H n)) +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac PlaneTree.leaf := by
  rw [fullLaw_shape_succ_bind, transition_initial]
  ext A hA
  rw [Measure.bind_apply hA (measurable_of_countable _).aemeasurable]
  simp only [lintegral_add_measure, lintegral_smul_measure]
  rw [lintegral_dirac' _ (measurable_of_countable _),
    lintegral_dirac' _ (measurable_of_countable _), fullLaw_shape_frozen_initial]
  rfl

end Freezing1.PlaneForward
