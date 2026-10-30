module

public import Freezing1.PlaneFiniteState
public import Freezing1.ForwardAnnealed
public import Freezing1.InterleavedChainKernel

/-!
# The genuine uniform attachment/freezing kernel on finite plane states

The countable ambient state space retains both its vertex set and active
set. On every raw state a uniform active vertex is selected, then the fresh
Bernoulli sign chooses attachment or freezing. The empty active set is
absorbing. No branching or splitting law is assumed.
-/

@[expose] public section

namespace Freezing1.PlaneForward

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem uniform_active_probability (s : State) (h : s.active.Nonempty) :
    IsProbabilityMeasure (Measure.uniformOfFinset s.active) := by
  constructor
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast h.card_pos.ne') (by simp)

noncomputable def signedTransitionLaw (s : State) (sign : Bool) : Measure State :=
  if s.active.Nonempty then
    (Measure.uniformOfFinset s.active).map (fun u => step s sign u)
  else Measure.dirac s

instance signedTransitionLaw_probability (s : State) (sign : Bool) :
    IsProbabilityMeasure (signedTransitionLaw s sign) := by
  unfold signedTransitionLaw
  split_ifs with h
  · have := uniform_active_probability s h
    exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
      |>.mpr inferInstance
  · infer_instance

theorem signedTransitionLaw_apply (s : State) (sign : Bool)
    (h : s.active.Nonempty) (A : Set State) :
    signedTransitionLaw s sign A =
      ((s.active.filter (fun u => step s sign u ∈ A)).card : ℝ≥0∞) / s.active.card := by
  rw [signedTransitionLaw, ite_eq_left h,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable A).measurableSet,
    Measure.uniformOfFinset_apply]
  rfl

theorem signedTransitionLaw_eq_dirac_of_empty (s : State) (sign : Bool)
    (h : s.active = ∅) : signedTransitionLaw s sign = Measure.dirac s := by
  simp [signedTransitionLaw, h]

theorem signedTransitionLaw_ae (s : State) (sign : Bool) (P : State → Prop)
    (hempty : s.active = ∅ → P s)
    (hstep : ∀ u ∈ s.active, P (step s sign u)) :
    ∀ᵐ r ∂signedTransitionLaw s sign, P r := by
  apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
  by_cases h : s.active.Nonempty
  · rw [signedTransitionLaw_apply s sign h]
    have hf : s.active.filter (fun u => step s sign u ∈ {r | P r}) = s.active :=
      Finset.filter_eq_self.mpr hstep
    rw [hf]
    exact ENNReal.div_self (by exact_mod_cast h.card_pos.ne') (by simp)
  · have he : s.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [signedTransitionLaw_eq_dirac_of_empty s sign he]
    simp [hempty he]

noncomputable def transition (p : unitInterval) : Kernel State State where
  toFun s := (ForwardAnnealed.signLaw p).bind (signedTransitionLaw s)
  measurable' := measurable_of_countable _

instance transition_markov (p : unitInterval) : IsMarkovKernel (transition p) := by
  constructor
  intro s
  exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall fun sign => signedTransitionLaw_probability s sign)

theorem transition_apply (p : unitInterval) (s : State) (A : Set State) :
    transition p s A = ∫⁻ sign, signedTransitionLaw s sign A ∂ForwardAnnealed.signLaw p :=
  Measure.bind_apply (Set.to_countable A).measurableSet (measurable_of_countable _).aemeasurable

theorem transition_eq_dirac_of_empty (p : unitInterval) {s : State}
    (hs : s.active = ∅) : transition p s = Measure.dirac s := by
  change (ForwardAnnealed.signLaw p).bind (signedTransitionLaw s) = _
  have hfun : signedTransitionLaw s = fun _ => Measure.dirac s := by
    funext sign
    exact signedTransitionLaw_eq_dirac_of_empty s sign hs
  rw [hfun, Measure.bind_const]
  haveI := ForwardAnnealed.signLaw_probability p
  rw [measure_univ, one_smul]

theorem transition_apply_split (p : unitInterval) (s : State) (A : Set State) :
    transition p s A =
      (unitInterval.toNNReal p : ℝ≥0∞) * signedTransitionLaw s true A +
      (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) * signedTransitionLaw s false A := by
  rw [transition_apply, ForwardAnnealed.signLaw, bernoulliMeasure_def, lintegral_add_measure]
  simp

theorem transition_ae (p : unitInterval) (s : State) (P : State → Prop)
    (hempty : s.active = ∅ → P s)
    (hstep : ∀ sign u, u ∈ s.active → P (step s sign u)) :
    ∀ᵐ r ∂transition p s, P r := by
  apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
  rw [transition_apply]
  calc
    _ = ∫⁻ _sign, (1 : ℝ≥0∞) ∂ForwardAnnealed.signLaw p := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun sign =>
        (ae_iff_prob_eq_one (measurable_of_countable _)).mp
          (signedTransitionLaw_ae s sign P hempty (hstep sign))
    _ = 1 := by
      haveI := ForwardAnnealed.signLaw_probability p
      rw [lintegral_one, measure_univ]

/-- Growth is bounded on every raw state, even if its finite address set is
not a valid plane tree. This is the bound needed for non-starvation. -/
theorem transition_active_card_le (p : unitInterval) (s : State) :
    ∀ᵐ r ∂transition p s, r.active.card ≤ s.active.card + 1 := by
  apply transition_ae
  · intro _; omega
  · intro sign u _; exact step_active_card_le s sign u

theorem signedTransitionLaw_freeze_self {s : State} (hs : s.active.Nonempty) :
    signedTransitionLaw s false {s} = 0 := by
  rw [signedTransitionLaw_apply s false hs]
  have hno : ∀ u ∈ s.active, step s false u ≠ s := by
    intro u hu
    simpa [step, hu] using (freeze_ne_of_mem hu)
  letI : DecidablePred (fun u : PlaneTree.Address => step s false u ∈ ({s} : Set State)) :=
    Classical.decPred _
  have hcard : (s.active.filter (fun u => step s false u ∈ ({s} : Set State))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u hu
    simpa only [Set.mem_singleton_iff] using hno u hu
  simp only [hcard, Nat.cast_zero, div_eq_mul_inv, zero_mul]

/-- For p<1, exactly the empty-active states are absorbing. -/
theorem absorbing_iff_active_empty (p : unitInterval) (hp : (p : ℝ) < 1) (s : State) :
    CountableMarkovChain.Absorbing (transition p) s ↔ s.active = ∅ := by
  constructor
  · intro h
    by_contra he
    have hs := Finset.nonempty_iff_ne_empty.mpr he
    have hbound : transition p s {s} ≤ (unitInterval.toNNReal p : ℝ≥0∞) := by
      rw [transition_apply_split, signedTransitionLaw_freeze_self hs, mul_zero, add_zero]
      exact mul_le_of_le_one_right' prob_le_one
    have hp' : (unitInterval.toNNReal p : ℝ≥0∞) < 1 := by exact_mod_cast hp
    exact (ne_of_lt (hbound.trans_lt hp')) h
  · intro he
    rw [CountableMarkovChain.Absorbing, transition_eq_dirac_of_empty p he]
    simp

/-- Probability that a uniform active choice in the disjoint union belongs
to its first component. The source chooses the first component when both
components are absorbed. -/
noncomputable def selectionParameter (q : State × State) : unitInterval :=
  if hz : q.1.active.card + q.2.active.card = 0 then 1 else
  ⟨(q.1.active.card : ℝ) / (q.1.active.card + q.2.active.card : ℝ), by
    constructor
    · positivity
    · have hp : (0 : ℝ) < q.1.active.card + q.2.active.card := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      apply (div_le_one₀ hp).mpr
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)⟩

theorem selectionParameter_eq (s t : State) (h : s.active.card + t.active.card ≠ 0) :
    (selectionParameter (s, t) : ℝ) =
      (s.active.card : ℝ) / (s.active.card + t.active.card : ℝ) := by
  simp only [selectionParameter, dif_neg h]

theorem selectionParameter_both_empty (s t : State)
    (hs : s.active = ∅) (ht : t.active = ∅) : selectionParameter (s, t) = 1 := by
  simp [selectionParameter, hs, ht]

noncomputable def fullLaw (p : unitInterval) (s : State) : Measure (ℕ → State) :=
  CountableMarkovChain.fullLaw (transition p) s

instance fullLaw_probability (p : unitInterval) (s : State) :
    IsProbabilityMeasure (fullLaw p s) := by unfold fullLaw; infer_instance

end Freezing1.PlaneForward
