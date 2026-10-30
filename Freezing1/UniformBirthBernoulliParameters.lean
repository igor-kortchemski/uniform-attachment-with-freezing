module

public import Freezing1.ReverseHistoryBernoulli
public import Freezing1.HeightScale

/-!
# The unmasked Bernoulli array in the uniform-birth representation

The paper's independent driving variables have parameter `1 / S_i` even
on freezing steps. The sign mask is applied only in the truncated sum.
Strictly positive populations are therefore retained as a typing condition.
-/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators

set_option backward.isDefEq.respectTransparency false

theorem horizon_le_extinction {x : SignSequence} {n : ℕ} (h : PositiveThrough x n) :
    (n : ℕ∞) ≤ extinctionTime x := ((lt_extinctionTime_iff x n).mpr h).le

noncomputable def reciprocalParameter (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (i : Fin n) : unitInterval :=
  ⟨1 / (activeCount x (i.val + 1) : ℝ), by
    have hs : (1 : ℝ) ≤ activeCount x (i.val + 1) := by
      have hh : (1 : ℤ) ≤ activeCount x (i.val + 1) := by
        have := h (i.val + 1) (by omega)
        omega
      exact_mod_cast hh
    exact ⟨by positivity, (div_le_one (by linarith : 0 < (activeCount x (i.val + 1) : ℝ))).mpr hs⟩⟩

@[simp] theorem reciprocalParameter_coe (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (i : Fin n) :
    (reciprocalParameter x n h i : ℝ) = 1 / (activeCount x (i.val + 1) : ℝ) := rfl

def maskedCoordinate (x : SignSequence) {n : ℕ} (i : Fin n) (Y : Fin n → ℕ) : ℕ :=
  if x (i.val + 1) then Y i else 0

theorem maskedCoordinate_hasLaw (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (i : Fin n) :
    HasLaw (maskedCoordinate x i)
      (bernoulliMeasure (1 : ℕ) 0 (Reverse.attachmentParameter x n (horizon_le_extinction h) i))
      (bernoulliProductLaw (reciprocalParameter x n h)) := by
  have hmap := bernoulliProductLaw_coordinate (reciprocalParameter x n h) i
  cases hx : x (i.val + 1) with
  | false =>
    have hp : Reverse.attachmentParameter x n (horizon_le_extinction h) i = 0 := by
      apply Subtype.ext
      norm_num [Reverse.attachmentParameter_coe, hx]
    rw [hp]
    refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
    have he : maskedCoordinate x i = fun _ : Fin n → ℕ => (0 : ℕ) := by
      funext Y
      simp only [maskedCoordinate, hx, Bool.false_eq_true, ite_false]
    rw [he, Measure.map_const]
    simp
  | true =>
    have hp : Reverse.attachmentParameter x n (horizon_le_extinction h) i = reciprocalParameter x n h i := by
      apply Subtype.ext
      simp only [Reverse.attachmentParameter_coe, hx, ite_true, reciprocalParameter_coe]
    rw [hp]
    convert hmap using 1
    funext Y
    simp only [maskedCoordinate, hx, ite_true]

theorem maskedCoordinates_hasLaw (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    HasLaw (fun Y => fun i : Fin n => maskedCoordinate x i Y)
      (bernoulliProductLaw (Reverse.attachmentParameter x n (horizon_le_extinction h)))
      (bernoulliProductLaw (reciprocalParameter x n h)) := by
  have hi : iIndepFun (fun i : Fin n => maskedCoordinate x i)
      (bernoulliProductLaw (reciprocalParameter x n h)) := by
    exact (bernoulliProductLaw_independent (reciprocalParameter x n h)).comp
      (fun i (z : ℕ) => if x (i.val + 1) then z else 0) (fun _ => measurable_of_countable _)
  exact hi.hasLaw_pi (maskedCoordinate_hasLaw x n h)

def truncatedSum (x : SignSequence) {n : ℕ} (b : ℕ) (Y : Fin n → ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < b), maskedCoordinate x i Y

noncomputable def truncatedMean (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (b : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < b),
    (Reverse.attachmentParameter x n (horizon_le_extinction h) i : ℝ)

theorem truncatedSum_hasLaw (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (b : ℕ) :
    HasLaw (truncatedSum x b)
      (bernoulliPartialSumLaw (Reverse.attachmentParameter x n (horizon_le_extinction h))
        (Finset.univ.filter fun i : Fin n => i.val < b))
      (bernoulliProductLaw (reciprocalParameter x n h)) := by
  exact (bernoulliPartialSumLaw_hasLaw _ _).fun_comp (maskedCoordinates_hasLaw x n h)

theorem sum_fin_filter_lt_eq_sum_range (f : ℕ → ℝ) {b n : ℕ} (hbn : b ≤ n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < b), f i.val) =
      ∑ i ∈ Finset.range b, f i := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i < b then f i else 0),
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem truncatedMean_eq_heightScale (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    {b : ℕ} (hb : b ≤ n) : truncatedMean x n h b = heightScale x b := by
  unfold truncatedMean
  simp_rw [Reverse.attachmentParameter_coe]
  unfold heightScale
  exact sum_fin_filter_lt_eq_sum_range
    (fun i => if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0) hb

theorem truncatedMean_nonneg (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (b : ℕ) :
    0 ≤ truncatedMean x n h b := Finset.sum_nonneg (fun _ _ => unitInterval.nonneg _)

theorem truncatedMean_le_heightScale (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (b : ℕ) :
    truncatedMean x n h b ≤ heightScale x n := by
  rw [← truncatedMean_eq_heightScale x n h (b := n) le_rfl]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ i, i.isLt⟩
  · exact fun _ _ _ => unitInterval.nonneg _

end Freezing1.UniformBirth
