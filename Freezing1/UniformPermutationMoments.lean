module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic

/-!
# Weighted sampling through an actual uniform permutation

These are moments under the uniform probability measure on all permutations.
They will be used for the paper's grafting step after that step is identified
with this sampling law. No independence or conditional grafting law is assumed
by the finite calculation itself.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

instance permutationMeasurableSpace (ι : Type*) : MeasurableSpace (Equiv.Perm ι) := ⊤

noncomputable def uniformPermutationLaw (ι : Type*) [Fintype ι] :
    Measure (Equiv.Perm ι) := Measure.uniformOfFinset Finset.univ

instance uniformPermutationLaw_isProbabilityMeasure (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (uniformPermutationLaw ι) := by
  constructor
  rw [uniformPermutationLaw, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ]
  exact ENNReal.div_self (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm ι)).ne')
    (ENNReal.natCast_ne_top _)

variable {ι : Type*} [Fintype ι]

theorem uniformPermutation_memLp (f : Equiv.Perm ι → ℝ) (p : ℝ≥0∞) :
    MemLp f p (uniformPermutationLaw ι) := by
  apply MemLp.of_bound measurable_from_top.aestronglyMeasurable (∑ σ, ‖f σ‖)
  exact Filter.Eventually.of_forall fun σ =>
    Finset.single_le_sum (fun τ _ => norm_nonneg (f τ)) (Finset.mem_univ σ)

theorem uniformPermutation_integrable (f : Equiv.Perm ι → ℝ) :
    Integrable f (uniformPermutationLaw ι) :=
  (uniformPermutation_memLp f 1).integrable le_rfl

theorem integral_uniformPermutation (f : Equiv.Perm ι → ℝ) :
    (∫ σ, f σ ∂uniformPermutationLaw ι) =
      (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ * ∑ σ, f σ := by
  rw [integral_fintype (uniformPermutation_integrable f), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp [uniformPermutationLaw, measureReal_def]

/-- Precomposition by any fixed permutation is a permutation of the sample
space, including the empty underlying type. -/
def permutationPrecompose (τ : Equiv.Perm ι) : Equiv.Perm (Equiv.Perm ι) where
  toFun σ := τ.trans σ
  invFun σ := τ.symm.trans σ
  left_inv σ := by ext i; simp
  right_inv σ := by ext i; simp

theorem integral_uniformPermutation_precompose (τ : Equiv.Perm ι)
    (f : Equiv.Perm ι → ℝ) :
    (∫ σ, f (τ.trans σ) ∂uniformPermutationLaw ι) =
      ∫ σ, f σ ∂uniformPermutationLaw ι := by
  rw [integral_uniformPermutation, integral_uniformPermutation]
  congr 1
  exact Equiv.sum_comp (permutationPrecompose τ) f

noncomputable def permutationIndicator (G : Finset ι) (σ : Equiv.Perm ι) (i : ι) : ℝ :=
  if σ i ∈ G then 1 else 0

omit [Fintype ι] in
theorem permutationIndicator_nonneg (G : Finset ι) (σ : Equiv.Perm ι) (i : ι) :
    0 ≤ permutationIndicator G σ i := by unfold permutationIndicator; split_ifs <;> norm_num

omit [Fintype ι] in
theorem permutationIndicator_sq (G : Finset ι) (σ : Equiv.Perm ι) (i : ι) :
    permutationIndicator G σ i ^ 2 = permutationIndicator G σ i := by
  unfold permutationIndicator; split_ifs <;> norm_num

theorem sum_permutationIndicator (G : Finset ι) (σ : Equiv.Perm ι) :
    ∑ i, permutationIndicator G σ i = (G.card : ℝ) := by
  change (∑ i, if σ i ∈ G then (1 : ℝ) else 0) = _
  rw [Equiv.sum_comp σ (fun j => if j ∈ G then (1 : ℝ) else 0)]
  simp

theorem integral_permutationIndicator_eq (G : Finset ι) (i j : ι) :
    (∫ σ, permutationIndicator G σ i ∂uniformPermutationLaw ι) =
      ∫ σ, permutationIndicator G σ j ∂uniformPermutationLaw ι := by
  have h := integral_uniformPermutation_precompose (Equiv.swap i j)
    (fun σ => permutationIndicator G σ i)
  simpa only [permutationIndicator, Equiv.trans_apply, Equiv.swap_apply_left] using h.symm

/-- Every image is genuinely uniform under the permutation measure. -/
theorem integral_permutationIndicator (G : Finset ι) (i : ι) :
    (∫ σ, permutationIndicator G σ i ∂uniformPermutationLaw ι) =
      (G.card : ℝ) / Fintype.card ι := by
  have hsum : (∑ j, ∫ σ, permutationIndicator G σ j ∂uniformPermutationLaw ι) =
      (G.card : ℝ) := by
    rw [← integral_finsetSum Finset.univ (fun j _ => uniformPermutation_integrable _)]
    simp only [sum_permutationIndicator]
    simp
  have hi : (Fintype.card ι : ℝ) ≠ 0 := by
    have : Nonempty ι := ⟨i⟩
    exact_mod_cast (Fintype.card_pos (α := ι)).ne'
  have heq : (Fintype.card ι : ℝ) *
      (∫ σ, permutationIndicator G σ i ∂uniformPermutationLaw ι) = (G.card : ℝ) := by
    calc
      _ = ∑ _j : ι, ∫ σ, permutationIndicator G σ i ∂uniformPermutationLaw ι := by simp
      _ = ∑ j : ι, ∫ σ, permutationIndicator G σ j ∂uniformPermutationLaw ι := by
        apply Finset.sum_congr rfl
        intro j _
        exact integral_permutationIndicator_eq G i j
      _ = _ := hsum
  apply (eq_div_iff hi).mpr
  simpa only [mul_comm] using heq

theorem integral_permutationIndicator_pair_eq (G : Finset ι) {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) :
    (∫ σ, permutationIndicator G σ i * permutationIndicator G σ j
      ∂uniformPermutationLaw ι) =
      ∫ σ, permutationIndicator G σ i * permutationIndicator G σ k
        ∂uniformPermutationLaw ι := by
  have h := integral_uniformPermutation_precompose (Equiv.swap j k)
    (fun σ => permutationIndicator G σ i * permutationIndicator G σ j)
  simpa only [permutationIndicator, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_left] using h.symm

/-- The exact two-image moment, in a multiplication form which avoids any
division by zero on types with fewer than two elements. -/
theorem integral_permutationIndicator_pair_mul (G : Finset ι) {i j : ι} (hij : i ≠ j) :
    ((Fintype.card ι : ℝ) - 1) *
      (∫ σ, permutationIndicator G σ i * permutationIndicator G σ j
        ∂uniformPermutationLaw ι) =
      ((G.card : ℝ) / Fintype.card ι) * ((G.card : ℝ) - 1) := by
  have hsum : (∑ k, ∫ σ, permutationIndicator G σ i * permutationIndicator G σ k
      ∂uniformPermutationLaw ι) =
      (G.card : ℝ) * ((G.card : ℝ) / Fintype.card ι) := by
    rw [← integral_finsetSum Finset.univ (fun k _ => uniformPermutation_integrable _)]
    simp only [← Finset.mul_sum, sum_permutationIndicator]
    rw [integral_mul_const, integral_permutationIndicator]
    ring
  have hdiag : (∫ σ, permutationIndicator G σ i * permutationIndicator G σ i
      ∂uniformPermutationLaw ι) = (G.card : ℝ) / Fintype.card ι := by
    simpa only [← pow_two, permutationIndicator_sq] using integral_permutationIndicator G i
  have hsum' : (∑ k ∈ Finset.univ.erase i,
      ∫ σ, permutationIndicator G σ i * permutationIndicator G σ k
        ∂uniformPermutationLaw ι) =
      ((Fintype.card ι : ℝ) - 1) *
        (∫ σ, permutationIndicator G σ i * permutationIndicator G σ j
          ∂uniformPermutationLaw ι) := by
    calc
      _ = ∑ _k ∈ Finset.univ.erase i,
          ∫ σ, permutationIndicator G σ i * permutationIndicator G σ j
            ∂uniformPermutationLaw ι := by
        apply Finset.sum_congr rfl
        intro k hk
        exact integral_permutationIndicator_pair_eq G (Finset.mem_erase.mp hk).1.symm hij
      _ = _ := by
        have : Nonempty ι := ⟨i⟩
        simp [Finset.card_erase_of_mem (Finset.mem_univ i),
          Nat.cast_sub (Nat.succ_le_of_lt (Fintype.card_pos (α := ι)))]
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun k => ∫ σ, permutationIndicator G σ i * permutationIndicator G σ k
      ∂uniformPermutationLaw ι) (Finset.mem_univ i)
  rw [hsum', hdiag, hsum] at hsplit
  nlinarith

/-- Distinct images have nonpositive covariance, proved from the actual
uniform permutation law rather than supplied as a sampling assumption. -/
theorem integral_permutationIndicator_pair_le (G : Finset ι) {i j : ι} (hij : i ≠ j) :
    (∫ σ, permutationIndicator G σ i * permutationIndicator G σ j
      ∂uniformPermutationLaw ι) ≤ ((G.card : ℝ) / Fintype.card ι) ^ 2 := by
  have hm : (2 : ℝ) ≤ Fintype.card ι := by
    have hcard : ({i, j} : Finset ι).card ≤ Fintype.card ι := Finset.card_le_univ _
    simpa [hij] using (show (({i, j} : Finset ι).card : ℝ) ≤ Fintype.card ι by exact_mod_cast hcard)
  have hm0 : (0 : ℝ) < Fintype.card ι := by linarith
  have hp0 : 0 ≤ (G.card : ℝ) / Fintype.card ι := div_nonneg (Nat.cast_nonneg _) hm0.le
  have hp1 : (G.card : ℝ) / Fintype.card ι ≤ 1 := by
    apply (div_le_one hm0).mpr
    exact_mod_cast G.card_le_univ
  have hp := div_mul_cancel₀ (G.card : ℝ) hm0.ne'
  have hp2 := congrArg (fun z : ℝ => z * ((G.card : ℝ) / Fintype.card ι)) hp
  have hq := integral_permutationIndicator_pair_mul G hij
  have hprod : 0 ≤ ((G.card : ℝ) / Fintype.card ι) *
      (1 - (G.card : ℝ) / Fintype.card ι) := mul_nonneg hp0 (sub_nonneg.mpr hp1)
  apply (mul_le_mul_iff_right₀ (show 0 < (Fintype.card ι : ℝ) - 1 by linarith)).mp
  nlinarith

end Freezing1
