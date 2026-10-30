module

public import Freezing1.BernoulliPairCouplingThinningBounds
public import Freezing1.BernoulliPairCouplingActual

/-! Exact source reciprocal discrepancy and its population-controlled finite sum. -/

@[expose] public section

namespace Freezing1.BernoulliPairCoupling

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators Topology

set_option backward.isDefEq.respectTransparency false

theorem sum_descending_eq_sum_Ico (f : ℕ → ℝ) (a k : ℕ) :
    (∑ j : Fin k, f (a + k - 1 - j.val)) = ∑ i ∈ Finset.Ico a (a + k), f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    have hhead : f (a + (k + 1) - 1 - (0 : Fin (k + 1)).val) = f (a + k) := by
      congr 1
    have he : (fun j : Fin k => f (a + (k + 1) - 1 - j.succ.val)) =
        (fun j => f (a + k - 1 - j.val)) := by
      funext j
      congr 1
      simp only [Fin.val_succ]
      have := j.isLt
      omega
    rw [hhead, he, ih]
    rw [show a + (k + 1) = (a + k) + 1 by omega,
      Finset.sum_Ico_succ_top (Nat.le_add_right a k)]
    ring

theorem step_parameter_gap (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {i : ℕ} (hi : i < n) :
    (auxiliaryParameter x n hn i : ℝ) - Reverse.stepParameter x n hn i =
      if x (i + 1) then
        1 / ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1)) else 0 := by
  rw [auxiliaryParameter_of_lt x n hn hi, Reverse.stepParameter_of_lt x n hn hi,
    enlargedAttachmentParameter_coe, Reverse.attachmentParameter_coe]
  cases hx : x (i + 1)
  · simp
  · simp only [↓reduceIte]
    have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
      le_trans (by exact_mod_cast Nat.succ_le_of_lt hi) hn
    have htwo : (2 : ℝ) ≤ activeCount x (i + 1) :=
      by exact_mod_cast two_le_activeCount_succ_of_attachment hiτ hx
    have h := reciprocal_parameter_difference (S := (activeCount x (i + 1) : ℝ))
      (by linarith only [htwo])
    rw [abs_of_nonpos (sub_nonpos.mpr
      (one_div_le_one_div_of_le (by linarith only [htwo]) (by linarith))), neg_sub] at h
    exact h

noncomputable def auxiliaryError (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a k : ℕ) : ℝ :=
  ∑ j : Fin k, ((descendingParameter (auxiliaryParameter x n hn) a k j : ℝ) -
    descendingParameter (Reverse.stepParameter x n hn) a k j)

theorem auxiliaryError_eq_reciprocal_sum (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a k : ℕ) (hk : a + k ≤ n) :
    auxiliaryError x n hn a k = ∑ i ∈ Finset.Ico a (a + k),
      if x (i + 1) then
        1 / ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1)) else 0 := by
  change (∑ j : Fin k, ((auxiliaryParameter x n hn (a + k - 1 - j.val) : ℝ) -
    Reverse.stepParameter x n hn (a + k - 1 - j.val))) = _
  rw [sum_descending_eq_sum_Ico
    (fun i => (auxiliaryParameter x n hn i : ℝ) - Reverse.stepParameter x n hn i) a k]
  apply Finset.sum_congr rfl
  intro i hi
  exact step_parameter_gap x n hn ((Finset.mem_Ico.mp hi).2.trans_le hk)

theorem sum_fin_ge_eq_sum_Ico (f : ℕ → ℝ) (a b : ℕ) :
    (∑ i ∈ blockAttachmentIndices a b, f i.val) = ∑ i ∈ Finset.Ico a b, f i := by
  rw [blockAttachmentIndices, Finset.sum_filter,
    Fin.sum_univ_eq_sum_range (fun i => if a ≤ i then f i else 0) b,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  tauto

theorem auxiliaryError_eq_finite_parameter_sum (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a k : ℕ) (hk : a + k ≤ n) :
    auxiliaryError x n hn a k = ∑ i ∈ blockAttachmentIndices a (a + k),
      ((enlargedAttachmentParameter x n hn ⟨i.val, i.isLt.trans_le hk⟩ : ℝ) -
        blockAttachmentParameter x n hn (a + k) hk i) := by
  change (∑ j : Fin k, ((auxiliaryParameter x n hn (a + k - 1 - j.val) : ℝ) -
    Reverse.stepParameter x n hn (a + k - 1 - j.val))) = _
  rw [sum_descending_eq_sum_Ico
    (fun i => (auxiliaryParameter x n hn i : ℝ) - Reverse.stepParameter x n hn i) a k,
    ← sum_fin_ge_eq_sum_Ico
      (fun i => (auxiliaryParameter x n hn i : ℝ) - Reverse.stepParameter x n hn i) a (a + k)]
  apply Finset.sum_congr rfl
  intro i _
  rw [auxiliaryParameter_of_lt x n hn (i.isLt.trans_le hk),
    Reverse.stepParameter_of_lt x n hn (i.isLt.trans_le hk)]
  rfl

theorem auxiliaryError_le_twice_square_sum (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a k : ℕ) (hk : a + k ≤ n) :
    auxiliaryError x n hn a k ≤
      2 * ∑ i ∈ blockAttachmentIndices a (a + k),
        (blockAttachmentParameter x n hn (a + k) hk i : ℝ)^2 := by
  rw [auxiliaryError_eq_finite_parameter_sum x n hn a k hk, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := attachmentParameter_enlarged_difference_le x n hn ⟨i.val, i.isLt.trans_le hk⟩
  have ho := attachmentParameter_le_enlarged x n hn ⟨i.val, i.isLt.trans_le hk⟩
  rw [abs_of_nonpos (sub_nonpos.mpr (show
    (Reverse.attachmentParameter x n hn ⟨i.val, i.isLt.trans_le hk⟩ : ℝ) ≤
      enlargedAttachmentParameter x n hn ⟨i.val, i.isLt.trans_le hk⟩ from ho)), neg_sub] at h
  exact h

theorem auxiliaryError_le_linear (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a k : ℕ) (hk : a + k ≤ n)
    (ha : 1 ≤ a) {c : ℝ} (hc : 0 < c)
    (herr : ∀ j ∈ Finset.Icc a (a + k), |(activeCount x j : ℝ) / j - c| ≤ c / 2) :
    auxiliaryError x n hn a k ≤ (4 / (c * a)) * heightInterval x a (a + k) := by
  apply (auxiliaryError_le_twice_square_sum x n hn a k hk).trans
  have h := mul_le_mul_of_nonneg_left
    (sum_sq_blockAttachmentParameter_le_linear x n hn a (a + k) hk ha hc herr)
    (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1
  ring

/-- Source A61's error is uniformly of order `1/a` in every admissible
fixed-ratio near-origin block. The constant does not depend on the vertices. -/
theorem uniform_geometric_auxiliaryError
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hn : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A c)
    (C : ℕ) (hC : 1 < C) :
    ∃ M : ℝ, 0 < M ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ (a : ℕ) (_hbn : a * C ≤ n), A n ≤ (a : ℝ) →
        ((a * C : ℕ) : ℝ) ≤ ε * n →
          auxiliaryError (x n) n (hn n) a (a * C - a) ≤ M / a := by
  let K := (c + 1) / (2 * c)
  let L := Real.log (C : ℝ)
  let C0 := ((C : ℝ) + 1) / 2
  let M := (4 / c) * ((K + 1) * L)
  have hCR : (1 : ℝ) < C := by exact_mod_cast hC
  have hK : 0 < K := by dsimp only [K]; positivity
  have hL : 0 < L := Real.log_pos hCR
  have hM : 0 < M := by dsimp only [M]; positivity
  have hC0 : 1 < C0 := by dsimp only [C0]; linarith only [hCR]
  have hC0C : C0 < (C : ℝ) := by dsimp only [C0]; linarith only [hCR]
  obtain ⟨ε1, hε1, hε1lt, hpoint⟩ := hnear (c / 2) (half_pos hc)
  obtain ⟨ε2, hε2, hε2lt, hblock⟩ :=
    uniformLogIntervals_of_nearOriginLinear hnear hA hc hC0 1 zero_lt_one
  let ε := min ε1 ε2
  refine ⟨M, hM, ε, lt_min hε1 hε2, (min_le_left _ _).trans_lt hε1lt, ?_⟩
  filter_upwards [hpoint, hblock, hA.eventually_ge_atTop 1] with n hpointn hblockn hAn
  intro a hbn hAa hupper
  have ha1 : (1 : ℝ) ≤ a := hAn.trans hAa
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
  have ha : 1 ≤ a := by exact_mod_cast ha1
  have hab : a < a * C := by nlinarith only [ha, hC]
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
    dsimp only [L]
    congr 1
    push_cast
    field_simp
  rw [hlogratio] at hmid
  have hmean : heightInterval (x n) a (a * C) ≤ (K + 1) * L := by
    apply (div_le_iff₀ hL).mp
    have hh := (abs_le.mp hmid).2
    change heightInterval (x n) a (a * C) / L - K ≤ 1 at hh
    linarith only [hh]
  have he : a + (a * C - a) = a * C := Nat.add_sub_of_le hab.le
  have herror : auxiliaryError (x n) n (hn n) a (a * C - a) ≤
      (4 / (c * a)) * heightInterval (x n) a (a * C) := by
    have h := auxiliaryError_le_linear (x n) n (hn n) a (a * C - a)
      (by omega) ha hc (by simpa only [he] using herr)
    simpa only [he] using h
  apply herror.trans
  calc
    _ ≤ (4 / (c * a)) * ((K + 1) * L) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = M / a := by dsimp only [M]; ring

end Freezing1.BernoulliPairCoupling
