module

public import Freezing1.UniformPermutationWeighted

/-!
# One growth step under uniform matching

The population bound is `m ≤ a+1`, as required by the initial root in the
paper's walk. For `a ≥ 3`, four marked descendants per old block size leave
a factor-three conditional mean and a factor-two growth target. The good-set
target is any positive real number, allowing the repaired base `ρ*2^k`.

These are statements about the actual uniform matching measure. Identifying
the tree continuation with that matching remains a separate obligation.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

theorem probability_lt_two_le_of_mean_three {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M)
    (hmean : 3 * b ≤ ∫ ω, X ω ∂μ)
    (hvar : variance X μ ≤ M * ∫ ω, X ω ∂μ) :
    μ.real {ω | X ω < 2 * b} ≤ 3 * M / b := by
  let m := ∫ ω, X ω ∂μ
  have hm : 0 < m := by dsimp [m]; linarith
  have hthird : 0 < m / 3 := by positivity
  have hcheb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (meas_ge_le_variance_div_sq hX hthird)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg _))] at hcheb
  calc
    _ ≤ μ.real {ω | m / 3 ≤ |X ω - m|} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      change X ω < 2 * b at hω
      have hdiff : m / 3 ≤ -(X ω - m) := by dsimp [m] at *; linarith
      exact hdiff.trans (neg_le_abs _)
    _ ≤ variance X μ / (m / 3) ^ 2 := hcheb
    _ ≤ (M * m) / (m / 3) ^ 2 := div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 9 * M / m := by field_simp; ring
    _ ≤ 3 * M / b := by
      apply (div_le_div_iff₀ hm hb).mpr
      have hh := mul_le_mul_of_nonneg_left hmean
        (show 0 ≤ 3 * M from mul_nonneg (by norm_num) hM)
      dsimp [m]
      nlinarith

/-- Corrected population arithmetic for the source's one-step mean. -/
theorem integral_weightedPermutationCount_ge_three {ι : Type*} [Fintype ι]
    (G : Finset ι) (w : ι → ℝ) {a b : ℝ} (ha : 3 ≤ a) (hb : 0 < b)
    (hm : (Fintype.card ι : ℝ) ≤ a + 1) (hg : b ≤ G.card)
    (hweight : 4 * a ≤ ∑ i, w i) :
    3 * b ≤ ∫ σ, weightedPermutationCount G w σ ∂uniformPermutationLaw ι := by
  have hcard : (G.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast G.card_le_univ
  have hm0 : (0 : ℝ) < Fintype.card ι := lt_of_lt_of_le (hb.trans_le hg) hcard
  rw [integral_weightedPermutationCount, div_mul_eq_mul_div]
  apply (le_div_iff₀ hm0).mpr
  have ha0 : 0 ≤ 4 * a := by linarith
  have hg0 : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
  calc
    _ ≤ b * (4 * a) := by nlinarith [mul_le_mul_of_nonneg_left hm hb.le]
    _ ≤ _ := mul_le_mul hg hweight ha0 hg0

/-- The paper's conditional second-moment step under the actual uniform
matching law, with the initial-root correction included. -/
theorem uniformPermutation_growth_failure_le {ι : Type*} [Fintype ι]
    (G : Finset ι) (w : ι → ℝ) {a b M : ℝ} (ha : 3 ≤ a) (hb : 0 < b)
    (hm : (Fintype.card ι : ℝ) ≤ a + 1) (hg : b ≤ G.card)
    (hweight : 4 * a ≤ ∑ i, w i) (hM : 0 ≤ M)
    (hw : ∀ i, 0 ≤ w i) (hwM : ∀ i, w i ≤ M) :
    (uniformPermutationLaw ι).real {σ | weightedPermutationCount G w σ < 2 * b} ≤
      3 * M / b := by
  exact probability_lt_two_le_of_mean_three (uniformPermutation_memLp _ 2) hb hM
    (integral_weightedPermutationCount_ge_three G w ha hb hm hg hweight)
    (variance_weightedPermutationCount_le G w hw hwM)

end Freezing1
