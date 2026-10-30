module

public import Freezing1.SIRProbability
public import Freezing1.CountableMarkovObservations
public import Freezing1.CountableMarkovShift
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.SubGaussian

/-!
# The genuine unstopped susceptible chain

This chain is continued after the derived infectious count reaches zero.
That derived count is integer valued and is allowed to become negative.
The susceptible count itself remains a natural number and is absorbed at 0.
-/

@[expose] public section

namespace Freezing1.SIR.Susceptible

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def transition (rate : ℝ≥0) : Kernel ℕ ℕ where
  toFun u := bernoulliMeasure (u - 1) u (infectionProbability rate u)
  measurable' := measurable_of_countable _

instance transition_markov (rate : ℝ≥0) : IsMarkovKernel (transition rate) := by
  constructor
  intro u
  change IsProbabilityMeasure (bernoulliMeasure (u - 1) u (infectionProbability rate u))
  infer_instance

noncomputable def fullLaw (rate : ℝ≥0) (n : ℕ) : Measure (ℕ → ℕ) :=
  CountableMarkovChain.fullLaw (transition rate) n

instance fullLaw_probability (rate : ℝ≥0) (n : ℕ) : IsProbabilityMeasure (fullLaw rate n) := by
  unfold fullLaw
  infer_instance

theorem transition_zero (rate : ℝ≥0) : transition rate 0 = Measure.dirac 0 := by
  simp [transition]

theorem transition_support (rate : ℝ≥0) (u : ℕ) :
    ∀ᵐ v ∂transition rate u, v = u - 1 ∨ v = u := by
  apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
  simp [transition, bernoulliMeasure_def]
  rw [← ENNReal.coe_add, unitInterval.toNNReal_add_toNNReal_symm]
  rfl

theorem fullLaw_initial (rate : ℝ≥0) (n : ℕ) : ∀ᵐ H ∂fullLaw rate n, H 0 = n :=
  CountableMarkovChain.fullLaw_initial (transition rate) n

theorem fullLaw_steps (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂fullLaw rate n, ∀ k, H (k + 1) = H k - 1 ∨ H (k + 1) = H k :=
  CountableMarkovChain.fullLaw_steps (transition rate) n _ (transition_support rate)

theorem fullLaw_bounds (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂fullLaw rate n, ∀ k, n - k ≤ H k ∧ H k ≤ n := by
  filter_upwards [fullLaw_initial rate n, fullLaw_steps rate n] with H h0 hs
  intro k
  induction k with
  | zero => simp [h0]
  | succ k ih => rcases hs k with he | he <;> rw [he] <;> omega

theorem fullLaw_antitone (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂fullLaw rate n, Antitone H := by
  filter_upwards [fullLaw_steps rate n] with H hs
  apply antitone_nat_of_succ_le
  intro k
  rcases hs k with he | he
  · rw [he]
    exact Nat.sub_le _ _
  · exact he.le

theorem transition_drift (rate : ℝ≥0) (u : ℕ) :
    (∫ v : ℕ, ((v : ℝ) - (u : ℝ)) ∂transition rate u) =
      -(rate : ℝ) * u / (1 + (rate : ℝ) * u) := by
  change (∫ v : ℕ, ((v : ℝ) - (u : ℝ))
    ∂bernoulliMeasure (u - 1) u (infectionProbability rate u)) = _
  rw [integral_bernoulliMeasure]
  by_cases hu : u = 0
  · simp [hu]
  · rw [Nat.cast_sub (by omega), Nat.cast_one]
    simp only [sub_self, smul_zero, add_zero, sub_sub_cancel_left]
    change (infectionProbability rate u : ℝ) * (-1) = _
    rw [infectionProbability_coe]
    ring

def infectious (n k : ℕ) (H : ℕ → ℕ) : ℤ := 2 * ((n : ℤ) - H k) - k + 1

noncomputable def centeredIncrement (rate : ℝ≥0) (u v : ℕ) : ℝ :=
  (v : ℝ) - u + (infectionProbability rate u : ℝ)

theorem centeredIncrement_integral (rate : ℝ≥0) (u : ℕ) :
    (∫ v : ℕ, centeredIncrement rate u v ∂transition rate u) = 0 := by
  change (∫ v : ℕ, centeredIncrement rate u v
    ∂bernoulliMeasure (u - 1) u (infectionProbability rate u)) = _
  rw [integral_bernoulliMeasure]
  by_cases hu : u = 0
  · simp [hu, centeredIncrement]
  · rw [show centeredIncrement rate u (u - 1) = (infectionProbability rate u : ℝ) - 1 by
      simp [centeredIncrement, Nat.cast_sub (by omega : 1 ≤ u)]; ring]
    change (infectionProbability rate u : ℝ) * ((infectionProbability rate u : ℝ) - 1) +
      (1 - (infectionProbability rate u : ℝ)) * centeredIncrement rate u u = 0
    simp only [centeredIncrement, sub_self, zero_add]
    ring

theorem centeredIncrement_mem_Icc (rate : ℝ≥0) (u : ℕ) :
    ∀ᵐ v ∂transition rate u, centeredIncrement rate u v ∈ Icc (-1 : ℝ) 1 := by
  filter_upwards [transition_support rate u] with v hv
  have hp := (infectionProbability rate u).property
  rcases hv with rfl | rfl
  · by_cases hu : u = 0
    · simp [hu, centeredIncrement]
    · have hu' : 1 ≤ u := by omega
      simp only [centeredIncrement, Nat.cast_sub hu', Nat.cast_one]
      constructor <;> linarith [hp.1, hp.2]
  · simp only [centeredIncrement, sub_self, zero_add]
    exact ⟨by linarith [hp.1], hp.2⟩

theorem centeredIncrement_subgaussian (rate : ℝ≥0) (u : ℕ) :
    HasSubgaussianMGF (centeredIncrement rate u) (1 : ℝ≥0) (transition rate u) := by
  convert hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (measurable_of_countable (centeredIncrement rate u)).aemeasurable
    (centeredIncrement_mem_Icc rate u) (centeredIncrement_integral rate u) using 1
  norm_num

noncomputable def noise (rate : ℝ≥0) (n : ℕ) (H : ℕ → ℕ) (k : ℕ) : ℝ :=
  (H k : ℝ) - n + ∑ i ∈ Finset.range k, (infectionProbability rate (H i) : ℝ)

theorem noise_zero (rate : ℝ≥0) (n : ℕ) {H : ℕ → ℕ} (h0 : H 0 = n) :
    noise rate n H 0 = 0 := by simp [noise, h0]

theorem noise_succ (rate : ℝ≥0) (n : ℕ) (H : ℕ → ℕ) (k : ℕ) :
    noise rate n H (k + 1) = noise rate n H k + centeredIncrement rate (H k) (H (k + 1)) := by
  simp only [noise, Finset.sum_range_succ, centeredIncrement]
  ring

theorem noise_eq_sum (rate : ℝ≥0) (n : ℕ) {H : ℕ → ℕ} (h0 : H 0 = n) (k : ℕ) :
    noise rate n H k = ∑ i ∈ Finset.range k, centeredIncrement rate (H i) (H (i + 1)) := by
  induction k with
  | zero => simp [noise_zero rate n h0]
  | succ k ih => rw [noise_succ, ih, Finset.sum_range_succ]

theorem susceptible_noise_decomposition (rate : ℝ≥0) {n : ℕ} (hn : 0 < n)
    (H : ℕ → ℕ) (k : ℕ) :
    (H k : ℝ) / n = 1 + noise rate n H k / n -
      (1 / (n : ℝ)) * ∑ i ∈ Finset.range k, (infectionProbability rate (H i) : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold noise
  field_simp
  ring

theorem centeredIncrement_exp_bound (rate : ℝ≥0) (u : ℕ) (theta : ℝ) :
    (∫⁻ v, ENNReal.ofReal (Real.exp (theta * centeredIncrement rate u v)) ∂transition rate u) ≤
      ENNReal.ofReal (Real.exp (theta ^ 2 / 2)) := by
  have hs := centeredIncrement_subgaussian rate u
  have hh := ENNReal.ofReal_le_ofReal (hs.mgf_le theta)
  change ENNReal.ofReal (∫ v, Real.exp (theta * centeredIncrement rate u v) ∂transition rate u) ≤ _ at hh
  rw [ofReal_integral_eq_lintegral_ofReal (hs.integrable_exp_mul theta)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)] at hh
  simpa only [NNReal.coe_one, one_mul] using hh

noncomputable def updateNoise (rate : ℝ≥0) (a : ℝ × ℕ) (v : ℕ) : ℝ × ℕ :=
  (a.1 + centeredIncrement rate a.2 v, v)

theorem accumulate_noise (rate : ℝ≥0) (n : ℕ) {H : ℕ → ℕ} (h0 : H 0 = n) (k : ℕ) :
    CountableMarkovChain.accumulate ((0 : ℝ), n) (updateNoise rate) H k =
      (noise rate n H k, H k) := by
  induction k with
  | zero => simp [CountableMarkovChain.accumulate_zero, noise_zero rate n h0, h0]
  | succ k ih => rw [CountableMarkovChain.accumulate_succ, ih, noise_succ]; rfl

theorem updateNoise_exp_bound (rate : ℝ≥0) (a : ℝ × ℕ) (theta : ℝ) :
    (∫⁻ v, ENNReal.ofReal (Real.exp (theta * (updateNoise rate a v).1)) ∂transition rate a.2) ≤
      ENNReal.ofReal (Real.exp (theta * a.1)) * ENNReal.ofReal (Real.exp (theta ^ 2 / 2)) := by
  have he : (fun v => ENNReal.ofReal (Real.exp (theta * (updateNoise rate a v).1))) =
      fun v => ENNReal.ofReal (Real.exp (theta * a.1)) *
        ENNReal.ofReal (Real.exp (theta * centeredIncrement rate a.2 v)) := by
    funext v
    simp only [updateNoise, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [he, lintegral_const_mul _ (measurable_of_countable _)]
  exact mul_le_mul_of_nonneg_left (centeredIncrement_exp_bound rate a.2 theta) zero_le

theorem noise_lintegral_exp_le (rate : ℝ≥0) (n k : ℕ) (theta : ℝ) :
    (∫⁻ H, ENNReal.ofReal (Real.exp (theta * noise rate n H k)) ∂fullLaw rate n) ≤
      ENNReal.ofReal (Real.exp ((k : ℝ) * theta ^ 2 / 2)) := by
  let f : (ℝ × ℕ) → ℕ → ℝ≥0∞ := fun a _ => ENNReal.ofReal (Real.exp (theta * a.1))
  have hacc : ∀ k,
      (∫⁻ H, f (CountableMarkovChain.accumulate ((0 : ℝ), n) (updateNoise rate) H k) (H k)
        ∂fullLaw rate n) ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * theta ^ 2 / 2)) := by
    intro k
    induction k with
    | zero => simp [f, CountableMarkovChain.accumulate_zero]
    | succ k ih =>
      rw [fullLaw, CountableMarkovChain.lintegral_accumulate_succ]
      change (∫⁻ H, ∫⁻ v, f (updateNoise rate
        (CountableMarkovChain.accumulate ((0 : ℝ), n) (updateNoise rate) H k) v) v
        ∂transition rate (H k) ∂fullLaw rate n) ≤ _
      calc
        _ ≤ ∫⁻ H, f (CountableMarkovChain.accumulate ((0 : ℝ), n) (updateNoise rate) H k) (H k) *
            ENNReal.ofReal (Real.exp (theta ^ 2 / 2)) ∂fullLaw rate n := by
          apply lintegral_mono_ae
          filter_upwards [fullLaw_initial rate n] with H hH
          rw [accumulate_noise rate n hH]
          exact updateNoise_exp_bound rate (noise rate n H k, H k) theta
        _ = (∫⁻ H, f (CountableMarkovChain.accumulate ((0 : ℝ), n) (updateNoise rate) H k) (H k)
              ∂fullLaw rate n) * ENNReal.ofReal (Real.exp (theta ^ 2 / 2)) := by
          apply lintegral_mul_const
          let F : CountableMarkovChain.Prefix (E := ℕ) k → ℝ≥0∞ := fun H =>
            f (CountableMarkovChain.accumulatePrefix ((0 : ℝ), n) (updateNoise rate) k H)
              (H ⟨k, Finset.mem_Iic.mpr le_rfl⟩)
          exact (measurable_of_countable F).comp (by fun_prop)
        _ ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * theta ^ 2 / 2)) *
            ENNReal.ofReal (Real.exp (theta ^ 2 / 2)) := mul_le_mul_of_nonneg_right ih zero_le
        _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          push_cast
          ring
  have he : (∫⁻ H, ENNReal.ofReal (Real.exp (theta * noise rate n H k)) ∂fullLaw rate n) =
      ∫⁻ H, f (CountableMarkovChain.accumulate ((0 : ℝ), n) (updateNoise rate) H k) (H k)
        ∂fullLaw rate n := by
    apply lintegral_congr_ae
    filter_upwards [fullLaw_initial rate n] with H hH
    rw [accumulate_noise rate n hH]
  rw [he]
  exact hacc k

end Freezing1.SIR.Susceptible
