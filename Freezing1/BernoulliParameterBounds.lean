module

public import Freezing1.PoissonApproximation

/-!
# Comparing independent Bernoulli sums with different parameters

Convolution contracts the error on all tests with values in `[0,1]`. Summing
single-coordinate parameter errors proves the event comparison used in the
source's variance argument. This is a marginal comparison of actual product
laws, not a construction of the joint pair of forest heights.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

/-- The error of a Bernoulli test is controlled by the parameter difference. -/
theorem bernoulli_parameter_boundedTestError (p q : unitInterval) :
    BoundedTestError (bernoulliMeasure (1 : ℕ) 0 p) (bernoulliMeasure (1 : ℕ) 0 q)
      |(p : ℝ) - (q : ℝ)| := by
  intro f h0 h1
  rw [integral_bernoulliMeasure, integral_bernoulliMeasure]
  simp only [smul_eq_mul]
  have he : (p : ℝ) * f 1 + (1 - (p : ℝ)) * f 0 -
      ((q : ℝ) * f 1 + (1 - (q : ℝ)) * f 0) = ((p : ℝ) - (q : ℝ)) * (f 1 - f 0) := by ring
  rw [he, abs_mul]
  exact (mul_le_mul_of_nonneg_left
    (abs_le.mpr ⟨by linarith [h0 1, h1 0], by linarith [h1 1, h0 0]⟩)
    (abs_nonneg ((p : ℝ) - (q : ℝ)))).trans_eq (mul_one _)

/-- Perturbing independent Bernoulli parameters changes every bounded test
by at most the sum of their absolute differences. -/
theorem bernoulliPartialSumLaw_parameter_boundedTestError {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p q : ι → unitInterval) (s : Finset ι) :
    BoundedTestError (bernoulliPartialSumLaw p s) (bernoulliPartialSumLaw q s)
      (∑ i ∈ s, |(p i : ℝ) - (q i : ℝ)|) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [bernoulliPartialSumLaw_empty, Finset.sum_empty]
    exact BoundedTestError.refl _
  | @insert i s his ih =>
    rw [bernoulliPartialSumLaw_insert p s his, bernoulliPartialSumLaw_insert q s his,
      bind_shifted_bernoulli_eq_conv, bind_shifted_bernoulli_eq_conv, Finset.sum_insert his]
    have hh := (ih.conv_right (bernoulliMeasure (1 : ℕ) 0 (p i))).trans
      ((bernoulli_parameter_boundedTestError (p i) (q i)).conv_left (bernoulliPartialSumLaw q s))
    simpa only [add_comm] using hh

/-- The same sharp parameter bound holds for every event of the sum. -/
theorem bernoulliPartialSumLaw_parameter_event {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p q : ι → unitInterval) (s : Finset ι) (E : Set ℕ) :
    |(bernoulliPartialSumLaw p s).real E - (bernoulliPartialSumLaw q s).real E| ≤
      ∑ i ∈ s, |(p i : ℝ) - (q i : ℝ)| :=
  (bernoulliPartialSumLaw_parameter_boundedTestError p q s).event E

/-- Under pointwise ordering the error is simply the difference of the means. -/
theorem bernoulliPartialSumLaw_parameter_event_of_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p q : ι → unitInterval) (s : Finset ι)
    (hpq : ∀ i ∈ s, p i ≤ q i) (E : Set ℕ) :
    |(bernoulliPartialSumLaw p s).real E - (bernoulliPartialSumLaw q s).real E| ≤
      (∑ i ∈ s, (q i : ℝ)) - ∑ i ∈ s, (p i : ℝ) := by
  have hh := bernoulliPartialSumLaw_parameter_event p q s E
  have he : (∑ i ∈ s, |(p i : ℝ) - (q i : ℝ)|) =
      (∑ i ∈ s, (q i : ℝ)) - ∑ i ∈ s, (p i : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_nonpos (sub_nonpos.mpr (show (p i : ℝ) ≤ q i from hpq i hi)), neg_sub]
  rwa [he] at hh

/-- The scalar discrepancy in the manuscript's parameters `1/S` and `1/(S-1)`. -/
theorem reciprocal_parameter_difference {S : ℝ} (hS : 1 < S) :
    |1 / S - 1 / (S - 1)| = 1 / (S * (S - 1)) := by
  have hS0 : 0 < S := by linarith
  have hS1 : 0 < S - 1 := by linarith
  rw [abs_of_nonpos (sub_nonpos.mpr (one_div_le_one_div_of_le hS1 (by linarith)))]
  field_simp
  ring

/-- For `S≥2`, replacing `1/S` by `1/(S-1)` costs at most `2/S²`. -/
theorem reciprocal_parameter_difference_le {S : ℝ} (hS : 2 ≤ S) :
    |1 / S - 1 / (S - 1)| ≤ 2 / S ^ 2 := by
  rw [reciprocal_parameter_difference (by linarith)]
  have hS0 : 0 < S := by linarith
  have hS1 : 0 < S - 1 := by linarith
  apply (div_le_div_iff₀ (mul_pos hS0 hS1) (sq_pos_of_pos hS0)).mpr
  nlinarith

end Freezing1
