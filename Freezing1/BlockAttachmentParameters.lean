module

public import Freezing1.ReverseHeightLaw
public import Freezing1.LinearRegimeIntervals

/-!
# The actual attachment parameters on a paper block

The block `(a,b]` is represented by coordinates `i : Fin b` with `a ≤ i.val`;
coordinate `i` corresponds to paper step `i+1`. Its mean is the exact height
interval, and a uniform active-population lower bound controls its square sum.
-/

@[expose] public section

namespace Freezing1

open scoped BigOperators Classical

/-- Restrict the actual schedule parameters to the first `b` coordinates. -/
noncomputable def blockAttachmentParameter (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (b : ℕ) (hbn : b ≤ n) : Fin b → unitInterval :=
  fun i => Reverse.attachmentParameter x n hn ⟨i.val, i.isLt.trans_le hbn⟩

/-- Coordinates representing exactly the paper interval `(a,b]`. -/
def blockAttachmentIndices (a b : ℕ) : Finset (Fin b) :=
  Finset.univ.filter fun i => a ≤ i.val

theorem blockAttachmentParameter_coe (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (b : ℕ) (hbn : b ≤ n) (i : Fin b) :
    (blockAttachmentParameter x n hn b hbn i : ℝ) =
      if x (i.val + 1) then 1 / (activeCount x (i.val + 1) : ℝ) else 0 :=
  Reverse.attachmentParameter_coe x n hn _

/-- No rounding or endpoint error is present in the block's mean. -/
theorem sum_blockAttachmentParameter (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a b : ℕ) (hbn : b ≤ n) :
    (∑ i ∈ blockAttachmentIndices a b, (blockAttachmentParameter x n hn b hbn i : ℝ)) =
      heightInterval x a b := by
  have hfilter : (Finset.range b).filter (fun i => a ≤ i) = Finset.Ico a b := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    tauto
  unfold blockAttachmentIndices
  rw [Finset.sum_filter]
  simp_rw [blockAttachmentParameter_coe]
  rw [Fin.sum_univ_eq_sum_range (fun i => if a ≤ i then
    (if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0) else 0) b]
  rw [← Finset.sum_filter, hfilter]
  rfl

/-- A population lower bound on actual attachment steps bounds every parameter. -/
theorem blockAttachmentParameter_le_of_population_lower (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a b : ℕ) (hbn : b ≤ n)
    {d : ℝ} (hd : 0 < d)
    (hS : ∀ j ∈ Finset.Ioc a b, x j = true → d ≤ (activeCount x j : ℝ)) :
    ∀ i ∈ blockAttachmentIndices a b, (blockAttachmentParameter x n hn b hbn i : ℝ) ≤ 1 / d := by
  intro i hi
  have hai : a ≤ i.val := (Finset.mem_filter.mp hi).2
  have hij : i.val + 1 ∈ Finset.Ioc a b := Finset.mem_Ioc.mpr (by omega)
  rw [blockAttachmentParameter_coe]
  cases hx : x (i.val + 1)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    positivity
  · simp only [↓reduceIte]
    exact one_div_le_one_div_of_le hd (hS _ hij hx)

/-- The Le Cam square error is at most the mean divided by the uniform
population lower bound. -/
theorem sum_sq_blockAttachmentParameter_le (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a b : ℕ) (hbn : b ≤ n)
    {d : ℝ} (hd : 0 < d)
    (hS : ∀ j ∈ Finset.Ioc a b, x j = true → d ≤ (activeCount x j : ℝ)) :
    (∑ i ∈ blockAttachmentIndices a b, (blockAttachmentParameter x n hn b hbn i : ℝ) ^ 2) ≤
      heightInterval x a b / d := by
  calc
    _ ≤ ∑ i ∈ blockAttachmentIndices a b,
        (1 / d) * (blockAttachmentParameter x n hn b hbn i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp := blockAttachmentParameter_le_of_population_lower x n hn a b hbn hd hS i hi
      have hm := mul_le_mul_of_nonneg_right hp (blockAttachmentParameter x n hn b hbn i).property.1
      simpa only [pow_two] using hm
    _ = heightInterval x a b / d := by
      rw [← Finset.mul_sum, sum_blockAttachmentParameter]
      ring

/-- Uniform linear population control makes the square error of order `mean/a`. -/
theorem sum_sq_blockAttachmentParameter_le_linear (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a b : ℕ) (hbn : b ≤ n)
    (ha : 1 ≤ a) {c : ℝ} (hc : 0 < c)
    (herr : ∀ j ∈ Finset.Icc a b, |(activeCount x j : ℝ) / j - c| ≤ c / 2) :
    (∑ i ∈ blockAttachmentIndices a b, (blockAttachmentParameter x n hn b hbn i : ℝ) ^ 2) ≤
      (2 / (c * a)) * heightInterval x a b := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hS : ∀ j ∈ Finset.Ioc a b, x j = true → c * a / 2 ≤ (activeCount x j : ℝ) := by
    intro j hj _
    obtain ⟨haj, hjb⟩ := Finset.mem_Ioc.mp hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hja : (a : ℝ) ≤ j := by exact_mod_cast haj.le
    have he := (abs_le.mp (herr j (Finset.mem_Icc.mpr ⟨haj.le, hjb⟩))).1
    have hratio : c / 2 ≤ (activeCount x j : ℝ) / j := by linarith
    have hs := (le_div_iff₀ hj0).mp hratio
    nlinarith
  have hh := sum_sq_blockAttachmentParameter_le x n hn a b hbn
    (by positivity : 0 < c * a / 2) hS
  convert hh using 1
  field_simp

end Freezing1
