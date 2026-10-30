module

public import Freezing1.UniformPermutationMoments

/-!
# Mean and variance of weighted uniform matching

Each root has a fixed nonnegative number of marked descendants. A uniformly
random bijection matches roots to the good set. The resulting weighted count
has mean `|G|/m` times the total weight and variance at most its mean times
the largest weight. This is the finite sampling calculation used in the
paper's chaining argument, independently of the still separate grafting law.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

variable {ι : Type*} [Fintype ι]

noncomputable def weightedPermutationCount (G : Finset ι) (w : ι → ℝ)
    (σ : Equiv.Perm ι) : ℝ := ∑ i, w i * permutationIndicator G σ i

theorem integral_weightedPermutationCount (G : Finset ι) (w : ι → ℝ) :
    (∫ σ, weightedPermutationCount G w σ ∂uniformPermutationLaw ι) =
      ((G.card : ℝ) / Fintype.card ι) * ∑ i, w i := by
  unfold weightedPermutationCount
  rw [integral_finsetSum Finset.univ (fun i _ => uniformPermutation_integrable _)]
  simp only [integral_const_mul, integral_permutationIndicator, ← Finset.sum_mul]
  ring

theorem integral_weightedPermutationCount_sq_eq (G : Finset ι) (w : ι → ℝ) :
    (∫ σ, weightedPermutationCount G w σ ^ 2 ∂uniformPermutationLaw ι) =
      ∑ i, ∑ j, w i * w j *
        ∫ σ, permutationIndicator G σ i * permutationIndicator G σ j
          ∂uniformPermutationLaw ι := by
  have hpoint : ∀ σ, weightedPermutationCount G w σ ^ 2 =
      ∑ i, ∑ j, w i * w j *
        (permutationIndicator G σ i * permutationIndicator G σ j) := by
    intro σ
    simp only [weightedPermutationCount, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ => uniformPermutation_integrable _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => uniformPermutation_integrable _)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_const_mul _ _

theorem weighted_pair_majorant_sum (w : ι → ℝ) (p : ℝ) :
    (∑ i, ∑ j, w i * w j * (p ^ 2 + if i = j then p else 0)) =
      p ^ 2 * (∑ i, w i) ^ 2 + p * ∑ i, w i ^ 2 := by
  calc
    _ = ∑ i, ((∑ j, p ^ 2 * w i * w j) +
        (∑ j, if j = i then p * w i ^ 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j; simp only [ite_true]; ring
      · simp only [hij, Ne.symm hij, ite_false, add_zero]; ring
    _ = ∑ i, ((p ^ 2 * w i) * (∑ j, w j) + p * w i ^ 2) := by
      simp only [← Finset.mul_sum]
      simp
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
      ring

theorem integral_weightedPermutationCount_sq_le (G : Finset ι) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (∫ σ, weightedPermutationCount G w σ ^ 2 ∂uniformPermutationLaw ι) ≤
      ((G.card : ℝ) / Fintype.card ι) ^ 2 * (∑ i, w i) ^ 2 +
        ((G.card : ℝ) / Fintype.card ι) * ∑ i, w i ^ 2 := by
  rw [integral_weightedPermutationCount_sq_eq, ← weighted_pair_majorant_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw i) (hw j))
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have he : (∫ σ, permutationIndicator G σ i * permutationIndicator G σ i
        ∂uniformPermutationLaw ι) = (G.card : ℝ) / Fintype.card ι := by
      simpa only [← pow_two, permutationIndicator_sq] using integral_permutationIndicator G i
    rw [he]
    linarith [sq_nonneg ((G.card : ℝ) / Fintype.card ι)]
  · simp only [hij, ite_false, add_zero]
    exact integral_permutationIndicator_pair_le G hij

/-- The variance bound for the actual uniform matching. It includes zero
weights and the empty/singleton underlying types. -/
theorem variance_weightedPermutationCount_le (G : Finset ι) (w : ι → ℝ)
    {M : ℝ} (hw : ∀ i, 0 ≤ w i) (hM : ∀ i, w i ≤ M) :
    variance (weightedPermutationCount G w) (uniformPermutationLaw ι) ≤
      M * ∫ σ, weightedPermutationCount G w σ ∂uniformPermutationLaw ι := by
  rw [variance_eq_sub (uniformPermutation_memLp _ 2)]
  simp only [Pi.pow_apply]
  have hsecond := integral_weightedPermutationCount_sq_le G w hw
  have hsum : (∑ i, w i ^ 2) ≤ M * ∑ i, w i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hM i) (hw i)
  have hp : 0 ≤ (G.card : ℝ) / Fintype.card ι :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [integral_weightedPermutationCount] at *
  nlinarith [mul_le_mul_of_nonneg_left hsum hp]

end Freezing1
