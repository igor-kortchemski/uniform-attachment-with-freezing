module

public import Freezing1.ForwardSchedulePrefix
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# The actual forward kernel with a fresh random sign

A fresh attachment/freezing sign has Bernoulli parameter p. The next state is
then sampled from Algorithm 1's existing uniform-active-vertex kernel. The
result includes absorption and p=0; averaging a sign is proved to commute
with sampling the preceding state. No branching-tree law is assumed here.
-/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open Forward MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def signLaw (p : unitInterval) : Measure Bool :=
  bernoulliMeasure true false p

instance signLaw_probability (p : unitInterval) : IsProbabilityMeasure (signLaw p) := by
  unfold signLaw
  infer_instance

noncomputable def transitionLaw (p : unitInterval) (s : State) (t : ℕ) : Measure State :=
  (signLaw p).bind (fun sign => Forward.transitionLaw s t sign)

instance transitionLaw_probability (p : unitInterval) (s : State) (t : ℕ) :
    IsProbabilityMeasure (transitionLaw p s t) :=
  isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall fun sign => Forward.transitionLaw_probability s t sign)

noncomputable def transitionKernel (p : unitInterval) (t : ℕ) : Kernel State State :=
  ⟨fun s => transitionLaw p s t, measurable_from_top⟩

instance transitionKernel_markov (p : unitInterval) (t : ℕ) :
    IsMarkovKernel (transitionKernel p t) := ⟨fun s => transitionLaw_probability p s t⟩

theorem transitionLaw_apply (p : unitInterval) (s : State) (t : ℕ) (A : Set State) :
    transitionLaw p s t A = ∫⁻ sign, Forward.transitionLaw s t sign A ∂signLaw p :=
  Measure.bind_apply (by trivial) (measurable_of_countable _).aemeasurable

theorem transitionLaw_eq_dirac_of_empty (p : unitInterval) {s : State}
    (hs : s.active = ∅) (t : ℕ) : transitionLaw p s t = Measure.dirac s := by
  unfold transitionLaw
  simp only [Forward.transitionLaw_eq_dirac_of_empty s t _ hs]
  rw [Measure.bind_const, measure_univ, one_smul]

theorem transitionLaw_zero (s : State) (t : ℕ) :
    transitionLaw 0 s t = Forward.transitionLaw s t false := by
  rw [transitionLaw, signLaw, bernoulliMeasure_zero,
    Measure.dirac_bind (measurable_of_countable _)]

theorem transitionLaw_one (s : State) (t : ℕ) :
    transitionLaw 1 s t = Forward.transitionLaw s t true := by
  rw [transitionLaw, signLaw, bernoulliMeasure_one,
    Measure.dirac_bind (measurable_of_countable _)]

/-- Averaging the next independent sign and sampling the old state commute;
the identity is derived by Tonelli for the actual transition probabilities. -/
theorem bind_transitionLaw (p : unitInterval) (μ : Measure State) [SFinite μ] (t : ℕ) :
    μ.bind (fun s => transitionLaw p s t) =
      (signLaw p).bind (fun sign => μ.bind (fun s => Forward.transitionLaw s t sign)) := by
  ext A hA
  rw [Measure.bind_apply hA measurable_from_top.aemeasurable,
    Measure.bind_apply hA (measurable_of_countable _).aemeasurable]
  simp_rw [transitionLaw_apply,
    Measure.bind_apply hA measurable_from_top.aemeasurable]
  exact lintegral_lintegral_swap
    (measurable_from_prod_countable_left (fun _ => measurable_from_top)).aemeasurable

noncomputable def treeLaw (p : unitInterval) : ℕ → Measure State
  | 0 => Measure.dirac initial
  | n + 1 => (treeLaw p n).bind (fun s => transitionLaw p s (n + 1))

instance treeLaw_probability (p : unitInterval) (n : ℕ) : IsProbabilityMeasure (treeLaw p n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac initial); infer_instance
  | succ n ih =>
      exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
        (Filter.Eventually.of_forall fun s => transitionLaw_probability p s (n + 1))

theorem treeLaw_succ (p : unitInterval) (n : ℕ) :
    treeLaw p (n + 1) = (signLaw p).bind
      (fun sign => (treeLaw p n).bind (fun s => Forward.transitionLaw s (n + 1) sign)) :=
  bind_transitionLaw p (treeLaw p n) (n + 1)

theorem treeLaw_zero_parameter (n : ℕ) : treeLaw 0 n = Forward.treeLaw (fun _ => false) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [treeLaw, Forward.treeLaw, ih, transitionLaw_zero]

theorem treeLaw_one_parameter (n : ℕ) : treeLaw 1 n = Forward.treeLaw (fun _ => true) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [treeLaw, Forward.treeLaw, ih, transitionLaw_one]

end Freezing1.ForwardAnnealed
