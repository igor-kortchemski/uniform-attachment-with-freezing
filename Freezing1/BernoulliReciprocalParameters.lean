module

public import Freezing1.BernoulliParameterBounds
public import Freezing1.BlockAttachmentParameters
public import Freezing1.LinearRegimeUniform

/-!
# The source's enlarged reciprocal Bernoulli parameters

The auxiliary independent coordinates use `1/(S_i-1)` on attachment steps.
The law comparison with the exact attachment parameters is proved from their
scalar discrepancies. It does not assume or assert a coupling with two
simultaneously tracked component heights.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology

/-- The manuscript's auxiliary parameter is well-defined even at the extinction
endpoint, since every actual attachment step has population at least two. -/
noncomputable def enlargedAttachmentParameter (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (i : Fin n) : unitInterval :=
  if h : x (i.val + 1) = true then
    ⟨1 / ((activeCount x (i.val + 1) : ℝ) - 1), by
      have hiτ : ((i.val + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
        le_trans (by exact_mod_cast Nat.succ_le_of_lt i.isLt) hn
      have htwo : (2 : ℝ) ≤ activeCount x (i.val + 1) := by
        exact_mod_cast two_le_activeCount_succ_of_attachment hiτ h
      have hp : (0 : ℝ) < (activeCount x (i.val + 1) : ℝ) - 1 := by linarith
      exact ⟨one_div_nonneg.mpr hp.le, (div_le_iff₀ hp).mpr (by linarith)⟩⟩
  else 0

theorem enlargedAttachmentParameter_coe (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (i : Fin n) :
    (enlargedAttachmentParameter x n hn i : ℝ) =
      if x (i.val + 1) then 1 / ((activeCount x (i.val + 1) : ℝ) - 1) else 0 := by
  unfold enlargedAttachmentParameter
  split_ifs <;> rfl

theorem attachmentParameter_le_enlarged (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (i : Fin n) :
    Reverse.attachmentParameter x n hn i ≤ enlargedAttachmentParameter x n hn i := by
  change (Reverse.attachmentParameter x n hn i : ℝ) ≤ enlargedAttachmentParameter x n hn i
  rw [Reverse.attachmentParameter_coe, enlargedAttachmentParameter_coe]
  cases hx : x (i.val + 1)
  · simp
  · simp only [↓reduceIte]
    have hiτ : ((i.val + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
      le_trans (by exact_mod_cast Nat.succ_le_of_lt i.isLt) hn
    have htwo : (2 : ℝ) ≤ activeCount x (i.val + 1) := by
      exact_mod_cast two_le_activeCount_succ_of_attachment hiτ hx
    exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- A single enlarged parameter differs by at most twice the original square. -/
theorem attachmentParameter_enlarged_difference_le (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (i : Fin n) :
    |(Reverse.attachmentParameter x n hn i : ℝ) - enlargedAttachmentParameter x n hn i| ≤
      2 * (Reverse.attachmentParameter x n hn i : ℝ) ^ 2 := by
  rw [Reverse.attachmentParameter_coe, enlargedAttachmentParameter_coe]
  cases hx : x (i.val + 1)
  · simp
  · simp only [↓reduceIte]
    have hiτ : ((i.val + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
      le_trans (by exact_mod_cast Nat.succ_le_of_lt i.isLt) hn
    have htwo : (2 : ℝ) ≤ activeCount x (i.val + 1) := by
      exact_mod_cast two_le_activeCount_succ_of_attachment hiτ hx
    simpa only [div_pow, one_pow, mul_one_div] using reciprocal_parameter_difference_le htwo

/-- Actual product-law comparison on the exact paper block `(a,b]`. -/
theorem block_enlarged_parameter_event (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a b : ℕ) (hbn : b ≤ n)
    (E : Set ℕ) :
    |(bernoulliPartialSumLaw (blockAttachmentParameter x n hn b hbn)
        (blockAttachmentIndices a b)).real E -
      (bernoulliPartialSumLaw
        (fun i : Fin b => enlargedAttachmentParameter x n hn ⟨i.val, i.isLt.trans_le hbn⟩)
        (blockAttachmentIndices a b)).real E| ≤
      2 * ∑ i ∈ blockAttachmentIndices a b, (blockAttachmentParameter x n hn b hbn i : ℝ)^2 := by
  apply (bernoulliPartialSumLaw_parameter_event _ _ _ E).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact attachmentParameter_enlarged_difference_le x n hn ⟨i.val, i.isLt.trans_le hbn⟩

/-- In a linearly controlled block the enlarged-law error has order `mean/a`. -/
theorem block_enlarged_parameter_event_le_linear (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a b : ℕ) (hbn : b ≤ n)
    (ha : 1 ≤ a) {c : ℝ} (hc : 0 < c)
    (herr : ∀ j ∈ Finset.Icc a b, |(activeCount x j : ℝ) / j - c| ≤ c / 2)
    (E : Set ℕ) :
    |(bernoulliPartialSumLaw (blockAttachmentParameter x n hn b hbn)
        (blockAttachmentIndices a b)).real E -
      (bernoulliPartialSumLaw
        (fun i : Fin b => enlargedAttachmentParameter x n hn ⟨i.val, i.isLt.trans_le hbn⟩)
        (blockAttachmentIndices a b)).real E| ≤
      (4 / (c * a)) * heightInterval x a b := by
  apply (block_enlarged_parameter_event x n hn a b hbn E).trans
  have hh := mul_le_mul_of_nonneg_left
    (sum_sq_blockAttachmentParameter_le_linear x n hn a b hbn ha hc herr) (by norm_num : (0 : ℝ) ≤ 2)
  convert hh using 1
  ring

/-- The source's parameter-comparison error is uniformly of order `1/a`
on each fixed-ratio geometric block in its full near-origin window. -/
theorem uniform_geometricBlock_enlarged_parameter_error
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hn : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A c)
    (C : ℕ) (hC : 1 < C) :
    ∃ M : ℝ, 0 < M ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ (a : ℕ) (hbn : a * C ≤ n), A n ≤ (a : ℝ) →
        ((a * C : ℕ) : ℝ) ≤ ε * n → ∀ E : Set ℕ,
        |(bernoulliPartialSumLaw (blockAttachmentParameter (x n) n (hn n) (a * C) hbn)
            (blockAttachmentIndices a (a * C))).real E -
          (bernoulliPartialSumLaw
            (fun i : Fin (a * C) => enlargedAttachmentParameter (x n) n (hn n)
              ⟨i.val, i.isLt.trans_le hbn⟩)
            (blockAttachmentIndices a (a * C))).real E| ≤ M / a := by
  let K := (c + 1) / (2 * c)
  let L := Real.log (C : ℝ)
  let C0 := ((C : ℝ) + 1) / 2
  let M := (4 / c) * ((K + 1) * L)
  have hCR : (1 : ℝ) < C := by exact_mod_cast hC
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := Real.log_pos hCR
  have hM : 0 < M := by dsimp [M]; positivity
  have hC0 : 1 < C0 := by dsimp [C0]; linarith
  have hC0C : C0 < (C : ℝ) := by dsimp [C0]; linarith
  obtain ⟨ε1, hε1, hε1lt, hpoint⟩ := hnear (c / 2) (half_pos hc)
  obtain ⟨ε2, hε2, hε2lt, hblock⟩ :=
    uniformLogIntervals_of_nearOriginLinear hnear hA hc hC0 1 zero_lt_one
  let ε := min ε1 ε2
  refine ⟨M, hM, ε, lt_min hε1 hε2, (min_le_left _ _).trans_lt hε1lt, ?_⟩
  filter_upwards [hpoint, hblock, hA.eventually_ge_atTop 1] with n hpointn hblockn hAn
  intro a hbn hAa hupper E
  have ha1 : (1 : ℝ) ≤ a := hAn.trans hAa
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
  have ha : 1 ≤ a := by exact_mod_cast ha1
  have hab : a < a * C := by nlinarith
  have hupper1 : ((a * C : ℕ) : ℝ) ≤ ε1 * n :=
    hupper.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))
  have hupper2 : ((a * C : ℕ) : ℝ) ≤ ε2 * n :=
    hupper.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n))
  have herr : ∀ j ∈ Finset.Icc a (a * C),
      |(activeCount (x n) j : ℝ) / j - c| ≤ c / 2 := by
    intro j hj
    obtain ⟨haj, hjb⟩ := Finset.mem_Icc.mp hj
    exact hpointn j (hAa.trans (by exact_mod_cast haj))
      ((by exact_mod_cast hjb : (j : ℝ) ≤ (a * C : ℕ)).trans hupper1)
  have hsep : (a : ℝ) * C0 < (a * C : ℕ) := by
    push_cast
    exact mul_lt_mul_of_pos_left hC0C ha0
  have hmid := hblockn a (a * C) hAa hab hupper2 hsep
  have hlogratio : Real.log (((a * C : ℕ) : ℝ) / a) = L := by
    dsimp [L]
    congr 1
    push_cast
    field_simp
  rw [hlogratio] at hmid
  have hmean : heightInterval (x n) a (a * C) ≤ (K + 1) * L := by
    apply (div_le_iff₀ hL).mp
    have hh := (abs_le.mp hmid).2
    change heightInterval (x n) a (a * C) / L - K ≤ 1 at hh
    linarith
  apply (block_enlarged_parameter_event_le_linear (x n) n (hn n) a (a * C) hbn ha hc herr E).trans
  calc
    _ ≤ (4 / (c * a)) * ((K + 1) * L) := mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = M / a := by dsimp [M]; ring

end Freezing1
