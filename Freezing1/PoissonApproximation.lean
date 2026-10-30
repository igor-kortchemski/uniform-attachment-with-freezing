module

public import Freezing1.BernoulliProductLaw
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A quantitative Poisson approximation for independent Bernoulli sums

The error is bounded for every test function taking values in `[0,1]`, hence
for every event. This uses the usual probability total-variation normalization;
Mathlib's `tvDist` uses twice that normalization. The proof proceeds from the
single-coordinate mass comparison and contraction under convolution.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

/-- Uniform error on all `[0,1]`-valued tests, in the usual probability convention. -/
def BoundedTestError (μ ν : Measure ℕ) (error : ℝ) : Prop :=
  ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) → (∀ k, f k ≤ 1) →
    |(∫ k, f k ∂μ) - ∫ k, f k ∂ν| ≤ error

theorem unit_test_integrable (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {f : ℕ → ℝ} (h0 : ∀ k, 0 ≤ f k) (h1 : ∀ k, f k ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable f).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun k => by simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 k)] using h1 k

theorem unit_test_integral_bounds (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {f : ℕ → ℝ} (h0 : ∀ k, 0 ≤ f k) (h1 : ∀ k, f k ≤ 1) :
    0 ≤ (∫ k, f k ∂μ) ∧ (∫ k, f k ∂μ) ≤ 1 := by
  refine ⟨integral_nonneg h0, ?_⟩
  simpa using integral_mono (unit_test_integrable μ h0 h1) (integrable_const (1 : ℝ)) h1

theorem BoundedTestError.refl (μ : Measure ℕ) : BoundedTestError μ μ 0 := by
  intro f _ _
  simp

theorem BoundedTestError.symm {μ ν : Measure ℕ} {error : ℝ}
    (h : BoundedTestError μ ν error) : BoundedTestError ν μ error := by
  intro f h0 h1
  simpa only [abs_sub_comm] using h f h0 h1

theorem BoundedTestError.trans {μ ν ξ : Measure ℕ} {a b : ℝ}
    (h1 : BoundedTestError μ ν a) (h2 : BoundedTestError ν ξ b) :
    BoundedTestError μ ξ (a + b) := by
  intro f h0 h1f
  exact (abs_sub_le _ _ _).trans (add_le_add (h1 f h0 h1f) (h2 f h0 h1f))

theorem BoundedTestError.event {μ ν : Measure ℕ} {error : ℝ}
    (h : BoundedTestError μ ν error) (A : Set ℕ) : |μ.real A - ν.real A| ≤ error := by
  have hh := h (A.indicator (fun _ => (1 : ℝ)))
    (fun k => by by_cases hk : k ∈ A <;> simp [hk])
    (fun k => by by_cases hk : k ∈ A <;> simp [hk])
  simpa using hh

/-- Averaging a test function over an independent summand preserves its range. -/
theorem BoundedTestError.conv_right {μ ν : Measure ℕ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {error : ℝ}
    (h : BoundedTestError μ ν error) (ρ : Measure ℕ) [IsProbabilityMeasure ρ] :
    BoundedTestError (μ ∗ ρ) (ν ∗ ρ) error := by
  intro f h0 h1
  rw [integral_conv (unit_test_integrable _ h0 h1),
    integral_conv (unit_test_integrable _ h0 h1)]
  exact h _ (fun k => (unit_test_integral_bounds ρ (fun j => h0 (k + j)) (fun j => h1 (k + j))).1)
    (fun k => (unit_test_integral_bounds ρ (fun j => h0 (k + j)) (fun j => h1 (k + j))).2)

theorem BoundedTestError.conv_left {μ ν : Measure ℕ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {error : ℝ}
    (h : BoundedTestError μ ν error) (ρ : Measure ℕ) [IsProbabilityMeasure ρ] :
    BoundedTestError (ρ ∗ μ) (ρ ∗ ν) error := by
  rw [Measure.conv_comm ρ μ, Measure.conv_comm ρ ν]
  exact h.conv_right ρ

/-- Regard a Bernoulli probability as a nonnegative Poisson rate. -/
def bernoulliRate (p : unitInterval) : ℝ≥0 := ⟨(p : ℝ), p.property.1⟩

@[simp] theorem bernoulliRate_coe (p : unitInterval) : (bernoulliRate p : ℝ) = p := rfl

/-- Keeping just masses zero and one gives a lower bound for a nonnegative test. -/
theorem poisson_integral_ge_zero_one (rate : ℝ≥0) {f : ℕ → ℝ}
    (h0 : ∀ k, 0 ≤ f k) (h1 : ∀ k, f k ≤ 1) :
    Real.exp (-(rate : ℝ)) * f 0 + Real.exp (-(rate : ℝ)) * rate * f 1 ≤
      ∫ k, f k ∂poissonMeasure rate := by
  let g0 : ℕ → ℝ := ({0} : Set ℕ).indicator (fun _ => f 0)
  let g1 : ℕ → ℝ := ({1} : Set ℕ).indicator (fun _ => f 1)
  have hi0 : Integrable g0 (poissonMeasure rate) :=
    (integrable_const (f 0)).indicator (by measurability)
  have hi1 : Integrable g1 (poissonMeasure rate) :=
    (integrable_const (f 1)).indicator (by measurability)
  have hh : (∫ k, g0 k + g1 k ∂poissonMeasure rate) ≤ ∫ k, f k ∂poissonMeasure rate := by
    apply integral_mono (hi0.add hi1) (unit_test_integrable _ h0 h1)
    intro k
    by_cases hk0 : k = 0
    · simp [g0, g1, hk0]
    · by_cases hk1 : k = 1
      · simp [g0, g1, hk1]
      · simpa [g0, g1, hk0, hk1] using h0 k
  rw [integral_add hi0 hi1] at hh
  dsimp only [g0, g1] at hh
  rw [integral_indicator_const (f 0) (measurableSet_singleton 0),
    integral_indicator_const (f 1) (measurableSet_singleton 1)] at hh
  simpa only [smul_eq_mul, poissonMeasure_real_singleton, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, mul_one, div_one] using hh

/-- One Bernoulli coordinate has one-sided test error at most `p²`. -/
theorem bernoulli_poisson_integral_sub_le (p : unitInterval) {f : ℕ → ℝ}
    (h0 : ∀ k, 0 ≤ f k) (h1 : ∀ k, f k ≤ 1) :
    (∫ k, f k ∂bernoulliMeasure (1 : ℕ) 0 p) - ∫ k, f k ∂poissonMeasure (bernoulliRate p) ≤
      (p : ℝ) ^ 2 := by
  have hp0 := p.property.1
  have he : 1 - (p : ℝ) ≤ Real.exp (-(p : ℝ)) := by
    have hh := Real.add_one_le_exp (-(p : ℝ))
    linarith
  have he1 : Real.exp (-(p : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hδ0 : 0 ≤ (p : ℝ) * (1 - Real.exp (-(p : ℝ))) := mul_nonneg hp0 (by linarith)
  have hδ : (p : ℝ) * (1 - Real.exp (-(p : ℝ))) ≤ (p : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left he hp0
    nlinarith
  have hz : (1 - (p : ℝ) - Real.exp (-(p : ℝ))) * f 0 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (h0 0)
  have ho := mul_le_mul_of_nonneg_left (h1 1) hδ0
  have hP := poisson_integral_ge_zero_one (bernoulliRate p) h0 h1
  simp only [bernoulliRate_coe] at hP
  rw [integral_bernoulliMeasure]
  simp only [smul_eq_mul]
  nlinarith

/-- Complementing the test gives the full two-sided single-coordinate bound. -/
theorem bernoulli_poisson_boundedTestError (p : unitInterval) :
    BoundedTestError (bernoulliMeasure (1 : ℕ) 0 p) (poissonMeasure (bernoulliRate p)) ((p : ℝ) ^ 2) := by
  intro f h0 h1
  have hup := bernoulli_poisson_integral_sub_le p h0 h1
  have hlow := bernoulli_poisson_integral_sub_le p
    (f := fun k => 1 - f k) (fun k => by linarith [h1 k]) (fun k => by linarith [h0 k])
  rw [integral_sub (integrable_const (1 : ℝ)) (unit_test_integrable _ h0 h1),
    integral_sub (integrable_const (1 : ℝ)) (unit_test_integrable _ h0 h1)] at hlow
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlow
  exact abs_le.mpr ⟨by linarith, hup⟩

/-- Increasing the numerical error preserves the uniform test estimate. -/
theorem BoundedTestError.mono {μ ν : Measure ℕ} {a b : ℝ}
    (h : BoundedTestError μ ν a) (hab : a ≤ b) : BoundedTestError μ ν b :=
  fun f h0 h1 => (h f h0 h1).trans hab

@[simp] theorem poissonMeasure_zero_eq_dirac : poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro k
  rw [poissonMeasure_singleton]
  cases k <;> simp

/-- Le Cam's useful event-error bound, proved from the actual independent
Bernoulli product and the Poisson convolution identity. -/
theorem bernoulliPartialSumLaw_poisson_boundedTestError {ι : Type*} [Fintype ι]
    [DecidableEq ι] (p : ι → unitInterval) (s : Finset ι) :
    BoundedTestError (bernoulliPartialSumLaw p s)
      (poissonMeasure (∑ i ∈ s, bernoulliRate (p i))) (∑ i ∈ s, (p i : ℝ) ^ 2) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, bernoulliPartialSumLaw_empty, poissonMeasure_zero_eq_dirac]
    exact BoundedTestError.refl _
  | @insert i s his ih =>
    have hP : poissonMeasure (∑ j ∈ insert i s, bernoulliRate (p j)) =
        poissonMeasure (∑ j ∈ s, bernoulliRate (p j)) ∗ poissonMeasure (bernoulliRate (p i)) := by
      rw [Finset.sum_insert his, add_comm, poissonMeasure_conv_poissonMeasure]
    rw [bernoulliPartialSumLaw_insert p s his, bind_shifted_bernoulli_eq_conv,
      hP, Finset.sum_insert his]
    have hh := (ih.conv_right (bernoulliMeasure (1 : ℕ) 0 (p i))).trans
      ((bernoulli_poisson_boundedTestError (p i)).conv_left
        (poissonMeasure (∑ j ∈ s, bernoulliRate (p j))))
    simpa only [add_comm] using hh

/-- Every event has the same sum-of-squares approximation error. -/
theorem bernoulliPartialSumLaw_poisson_event {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → unitInterval) (s : Finset ι) (A : Set ℕ) :
    |(bernoulliPartialSumLaw p s).real A -
      (poissonMeasure (∑ i ∈ s, bernoulliRate (p i))).real A| ≤
        ∑ i ∈ s, (p i : ℝ) ^ 2 :=
  (bernoulliPartialSumLaw_poisson_boundedTestError p s).event A

/-- A probability law is close to its atom at zero by at most its mass off zero. -/
theorem boundedTestError_dirac_zero (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    BoundedTestError μ (Measure.dirac 0) (1 - μ.real {0}) := by
  intro f h0 h1
  have hif := unit_test_integrable μ h0 h1
  have hd : Integrable (fun k => f k - f 0) μ := hif.sub (integrable_const (f 0))
  have hnorm : |(∫ k, f k ∂μ) - f 0| ≤ ∫ k, |f k - f 0| ∂μ := by
    have hh := norm_integral_le_integral_norm (fun k => f k - f 0) (μ := μ)
    rw [integral_sub hif (integrable_const (f 0))] at hh
    simpa only [integral_const, probReal_univ, one_smul, Real.norm_eq_abs] using hh
  rw [integral_dirac]
  calc
    _ ≤ ∫ k, |f k - f 0| ∂μ := hnorm
    _ ≤ ∫ k, {j : ℕ | j ≠ 0}.indicator (fun _ => (1 : ℝ)) k ∂μ := by
      apply integral_mono hd.abs ((integrable_const (1 : ℝ)).indicator (by measurability))
      intro k
      by_cases hk : k = 0
      · simp [hk]
      · simp only [Set.indicator_of_mem (show k ∈ {j : ℕ | j ≠ 0} from hk)]
        exact abs_le.mpr ⟨by linarith [h0 k, h1 0], by linarith [h1 k, h0 0]⟩
    _ = 1 - μ.real {0} := by
      rw [integral_indicator_const (1 : ℝ) (by measurability)]
      simp only [smul_eq_mul, mul_one]
      change μ.real ({0}ᶜ) = 1 - μ.real {0}
      exact probReal_compl_eq_one_sub (by measurability)

/-- The probability that a Poisson variable is nonzero is at most its rate. -/
theorem poisson_dirac_boundedTestError (rate : ℝ≥0) :
    BoundedTestError (poissonMeasure rate) (Measure.dirac 0) (rate : ℝ) := by
  apply (boundedTestError_dirac_zero (poissonMeasure rate)).mono
  rw [poissonMeasure_real_singleton]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  have hh := Real.add_one_le_exp (-(rate : ℝ))
  linarith

/-- Adding an independent Poisson increment controls a change of parameter. -/
theorem poisson_boundedTestError_of_le {rate other : ℝ≥0} (h : rate ≤ other) :
    BoundedTestError (poissonMeasure rate) (poissonMeasure other)
      ((other : ℝ) - (rate : ℝ)) := by
  have hh := (poisson_dirac_boundedTestError (other - rate)).conv_left (poissonMeasure rate)
  rw [poissonMeasure_conv_poissonMeasure, add_tsub_cancel_of_le h, Measure.conv_dirac_zero] at hh
  simpa only [NNReal.coe_sub h] using hh.symm

/-- Parameter mismatch adds at most the absolute difference of Poisson rates. -/
theorem poisson_parameter_boundedTestError (rate other : ℝ≥0) :
    BoundedTestError (poissonMeasure rate) (poissonMeasure other)
      |(rate : ℝ) - (other : ℝ)| := by
  rcases le_total rate other with h | h
  · simpa only [abs_of_nonpos (sub_nonpos.mpr (show (rate : ℝ) ≤ other from h)), neg_sub] using poisson_boundedTestError_of_le h
  · simpa only [abs_of_nonneg (sub_nonneg.mpr (show (other : ℝ) ≤ rate from h))] using (poisson_boundedTestError_of_le h).symm

/-- The approximation includes an explicit mismatch between the Bernoulli
mean and the requested Poisson parameter. -/
theorem bernoulliPartialSumLaw_poisson_parameter_event {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → unitInterval) (s : Finset ι) (rate : ℝ≥0) (A : Set ℕ) :
    |(bernoulliPartialSumLaw p s).real A - (poissonMeasure rate).real A| ≤
      (∑ i ∈ s, (p i : ℝ) ^ 2) + |(∑ i ∈ s, (p i : ℝ)) - (rate : ℝ)| := by
  have hh := ((bernoulliPartialSumLaw_poisson_boundedTestError p s).trans
    (poisson_parameter_boundedTestError (∑ i ∈ s, bernoulliRate (p i)) rate)).event A
  simpa only [NNReal.coe_sum, bernoulliRate_coe] using hh

end Freezing1
