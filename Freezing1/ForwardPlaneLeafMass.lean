module

public import Freezing1.ForwardPlaneLimit
public import Freezing1.ForwardLocalExtinction
public import Freezing1.PlaneFirstStep
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# The actual plane limit is a leaf with probability one minus p

The first freezing action absorbs the singleton. The first attachment
creates child address `[1]`, which is retained forever. No subtree
independence is used to compute this mass.
-/

@[expose] public section

namespace Freezing1.PlaneForward

open MeasureTheory
open scoped Classical

theorem degree_shape_initial_step_false : PlaneTree.degree (shape (step initial false [])) = 0 := by
  have ha : [] ∈ initial.active := by simp [initial]
  rw [step, ite_eq_left ha]
  change PlaneTree.degree (shape (freeze initial [])) = 0
  rw [shape_freeze initial_valid, shape_initial, PlaneTree.degree_leaf]

theorem degree_shape_initial_step_true : PlaneTree.degree (shape (step initial true [])) = 1 := by
  have ha : [] ∈ initial.active := by simp [initial]
  rw [step, ite_eq_left ha]
  change (shape (attach initial [])).val [] = 1
  rw [(initial_valid.attach ha).shape_offspring,
    initial_valid.childCount_attach_self (by simp [initial]), childCount_initial]

end Freezing1.PlaneForward

namespace Freezing1.ForwardAnnealed

open Forward ForwardInfiniteHistory Filter MeasureTheory
open scoped ENNReal Topology Classical

def degreeZero : Set PlaneTree.Tree := {T | PlaneTree.degree T = 0}

theorem degreeZero_isClopen : IsClopen degreeZero :=
  (isClopen_discrete ({0} : Set ℕ)).preimage PlaneTree.continuous_degree

theorem planeProbabilityLaw_one (p : unitInterval) :
    (planeProbabilityLaw p 1 : Measure PlaneTree.Tree) =
      (PlaneForward.transition p PlaneForward.initial).map PlaneForward.shape := by
  rw [planeProbabilityLaw_eq_chainShape]
  have he : (PlaneForward.fullLaw p PlaneForward.initial).map
      (fun H : ℕ → PlaneForward.State => H 1) = PlaneForward.transition p PlaneForward.initial := by
    rw [PlaneForward.fullLaw, CountableMarkovChain.map_eval_succ,
      CountableMarkovChain.map_eval_zero,
      Measure.dirac_bind (PlaneForward.transition p).measurable]
  calc
    _ = ((PlaneForward.fullLaw p PlaneForward.initial).map
        (fun H : ℕ → PlaneForward.State => H 1)).map PlaneForward.shape :=
      (Measure.map_map (show Measurable PlaneForward.shape from measurable_of_countable _)
        (measurable_pi_apply 1)).symm
    _ = _ := congrArg (fun μ => μ.map PlaneForward.shape) he

theorem planeProbabilityLaw_one_degreeZero (p : unitInterval) :
    (planeProbabilityLaw p 1 : Measure PlaneTree.Tree) degreeZero =
      ENNReal.ofReal (1 - (p : ℝ)) := by
  rw [planeProbabilityLaw_one, Measure.map_apply (measurable_of_countable _)
    degreeZero_isClopen.1.measurableSet, PlaneForward.transition_apply_split,
    PlaneForward.signedTransitionLaw_initial, PlaneForward.signedTransitionLaw_initial]
  rw [Measure.dirac_apply' _ (degreeZero_isClopen.1.measurableSet.preimage
      (measurable_of_countable _)),
    Measure.dirac_apply' _ (degreeZero_isClopen.1.measurableSet.preimage
      (measurable_of_countable _))]
  simp only [Set.indicator_apply, Set.mem_preimage, degreeZero, Set.mem_ofPred_eq,
    PlaneForward.degree_shape_initial_step_true, PlaneForward.degree_shape_initial_step_false,
    one_ne_zero, ite_false, mul_zero, zero_add, ite_true, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_coe_nnreal]
  rfl

theorem projected_vertices_monotone {H : History}
    (hv : ∀ n, ValidAt n (H n))
    (hl : ∀ n, ∃ sign : Bool, LegalOrHeld (fun _ => sign) n (H n) (H (n + 1))) :
    Monotone (fun n => (H n).toPlaneState.vertices) := by
  apply monotone_nat_of_le_succ
  intro n
  obtain ⟨sign, hs⟩ := hl n
  rcases hs with ⟨_, he⟩ | ⟨v, ha, he⟩
  · rw [he]
  · rw [he, toPlaneState_step (hv n) sign ((hv n).active_subset ha)]
    exact PlaneForward.vertices_subset_step _ _ _

theorem first_action_cases {H : History} (h0 : H 0 = initial)
    (hl : ∀ n, ∃ sign : Bool, LegalOrHeld (fun _ => sign) n (H n) (H (n + 1))) :
    H 1 = freeze initial 1 0 ∨ H 1 = attach initial 1 0 := by
  obtain ⟨sign, hs⟩ := hl 0
  rw [h0] at hs
  rcases hs with ⟨he, _⟩ | ⟨v, ha, he⟩
  · simp [initial] at he
  · have hv : v = 0 := Finset.mem_singleton.mp ha
    subst v
    cases sign
    · exact Or.inl (by simpa [step, initial] using he)
    · exact Or.inr (by simpa [step, initial] using he)

theorem fullLaw_degreeZero_iff_at_one (p : unitInterval) :
    ∀ᵐ H ∂fullLaw p, ∀ n ≥ 1,
      PlaneTree.degree (PlaneForward.shape (H n).toPlaneState) = 0 ↔
        PlaneTree.degree (PlaneForward.shape (H 1).toPlaneState) = 0 := by
  filter_upwards [fullLaw_initial p, fullLaw_valid p, fullLaw_legalOrHeld p,
    fullLaw_toPlaneState_valid p] with H h0 hv hl hp
  rcases first_action_cases h0 hl with hf | ht
  · obtain ⟨x, hx⟩ := exists_schedule_of_legalOrHeld hl
    have ha : (H 1).active = ∅ := by rw [hf]; simp [freeze, initial]
    have hc := history_constant_of_active_empty hx ha
    intro n hn
    rw [hc n hn]
  · have hchild : [1] ∈ (H 1).toPlaneState.vertices := by
      rw [ht, toPlaneState_attach initial_valid (by simp [initial]), toPlaneState_initial]
      simp [PlaneForward.attach, PlaneForward.newChild, PlaneForward.childCount_initial]
    have hm := projected_vertices_monotone hv hl
    have hnz : ∀ n ≥ 1, PlaneTree.degree (PlaneForward.shape (H n).toPlaneState) ≠ 0 := by
      intro n hn hz
      have hc : ([] : PlaneTree.Address) ++ [1] ∈ (H n).toPlaneState.vertices :=
        hm hn hchild
      have hh := ((hp n).children_iff [] (hp n).root_mem 1).mp hc
      change (PlaneForward.shape (H n).toPlaneState).val [] = 0 at hz
      rw [(hp n).shape_offspring] at hz
      omega
    exact fun n hn => iff_of_false (hnz n hn) (hnz 1 le_rfl)

theorem planeProbabilityLaw_degreeZero_eq_path (p : unitInterval) (n : ℕ) :
    (planeProbabilityLaw p n : Measure PlaneTree.Tree) degreeZero =
      fullLaw p {H | PlaneTree.degree (PlaneForward.shape (H n).toPlaneState) = 0} := by
  have he : (planeProbabilityLaw p n : Measure PlaneTree.Tree) =
      (treeLaw p n).map (fun s => PlaneForward.shape s.toPlaneState) := by
    change ((treeLaw p n).map localTreeOfState).map LocalTree.toPlaneTree = _
    rw [Measure.map_map LocalTree.continuous_toPlaneTree.measurable measurable_from_top]
    apply Measure.map_congr
    filter_upwards [treeLaw_shape_eq_toPlaneTree p n] with s hs
    exact hs.symm
  rw [he, ← map_eval p n, Measure.map_map measurable_from_top (measurable_pi_apply n),
    Measure.map_apply (measurable_from_top.comp (measurable_pi_apply n))
      degreeZero_isClopen.1.measurableSet]
  rfl

theorem planeProbabilityLaw_degreeZero (p : unitInterval) (n : ℕ) (hn : 1 ≤ n) :
    (planeProbabilityLaw p n : Measure PlaneTree.Tree) degreeZero =
      ENNReal.ofReal (1 - (p : ℝ)) := by
  rw [planeProbabilityLaw_degreeZero_eq_path]
  calc
    _ = fullLaw p {H | PlaneTree.degree (PlaneForward.shape (H 1).toPlaneState) = 0} := by
      apply measure_congr
      filter_upwards [fullLaw_degreeZero_iff_at_one p] with H hH
      exact propext (hH n hn)
    _ = _ := by rw [← planeProbabilityLaw_degreeZero_eq_path, planeProbabilityLaw_one_degreeZero]

theorem planeLimitLaw_degreeZero (p : unitInterval) (hp : (p : ℝ) < 1) :
    (planeLimitLaw p : Measure PlaneTree.Tree) {T | PlaneTree.degree T = 0} =
      ENNReal.ofReal (1 - (p : ℝ)) := by
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (tendsto_planeProbabilityLaw p hp) (E := degreeZero)
    (by simp [degreeZero_isClopen.frontier_eq])
  have hconst : Tendsto (fun n => (planeProbabilityLaw p n : Measure PlaneTree.Tree) degreeZero)
      atTop (𝓝 (ENNReal.ofReal (1 - (p : ℝ)))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (planeProbabilityLaw_degreeZero p n hn).symm
  exact tendsto_nhds_unique hlim hconst

theorem planeLimitLaw_leaf (p : unitInterval) (hp : (p : ℝ) < 1) :
    (planeLimitLaw p : Measure PlaneTree.Tree) {PlaneTree.leaf} =
      ENNReal.ofReal (1 - (p : ℝ)) := by
  have he : {T : PlaneTree.Tree | PlaneTree.degree T = 0} = {PlaneTree.leaf} := by
    ext T
    exact PlaneTree.degree_zero_iff T
  rw [← he]
  exact planeLimitLaw_degreeZero p hp

end Freezing1.ForwardAnnealed
