module

import Challenge.LocalLimits

open Freezing1 Filter

/-! Independent reconstruction of T01 from the tex only (own walk, own tau-condition, own series). -/

def S' (x : SignSequence) : ℕ → ℤ
  | 0 => 1
  | n + 1 => S' x n + (if x (n + 1) = true then 1 else -1)

theorem S'_eq (x : SignSequence) (n : ℕ) : S' x n = activeCount x n := by
  induction n with
  | zero => simp [S', activeCount]
  | succ n ih =>
    rw [S', ih]
    unfold activeCount
    rw [Finset.sum_range_succ]; ring

/-- the tex term `1/S_i * 1_{X_i = -1}` -/
noncomputable def term (y : SignSequence) (i : ℕ) : ℝ :=
  if y i = true then 0 else 1 / (S' y i : ℝ)

theorem sum_eq (y : SignSequence) (n : ℕ) :
    freezingReciprocalSum y n = ∑ i ∈ Finset.range n, term y (i + 1) := by
  induction n with
  | zero => simp [freezingReciprocalSum]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold freezingReciprocalSum
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp [term, S'_eq]

/-- T01, tex 257-268, restated independently: tau = infinity is `S_n ≠ 0 for all n`;
(III) is `¬ Summable`. -/
theorem T01_indep (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : ∀ n, S' y n ≠ 0) :
    (DiagonalLocalConvergence x ↔ AlmostSureLocalConvergence y) ∧
      (AlmostSureLocalConvergence y ↔ ¬ Summable (fun i => term y (i + 1))) := by
  have htop : extinctionTime y = ⊤ := by
    unfold extinctionTime
    rw [dif_neg]
    rintro ⟨k, hk⟩
    exact hτ k (by rw [S'_eq]; exact hk)
  have hnn : ∀ i, 0 ≤ term y (i + 1) := by
    intro i
    unfold term
    split_ifs with h
    · exact le_rfl
    · have hpos : 0 < S' y (i + 1) := by
        -- S' never zero and moves by one from 1 so positive
        have : ∀ m, 0 < S' y m := by
          intro m
          induction m with
          | zero => simp [S']
          | succ m ih =>
            have h1 := hτ (m + 1)
            rw [S'] at h1 ⊢
            split_ifs at h1 ⊢ <;> omega
        exact this _
      positivity
  obtain ⟨h1, h2⟩ := local_convergence_equivalences x y hxy htop
  refine ⟨h1, h2.trans ?_⟩
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg hnn]
  simp only [← sum_eq]
