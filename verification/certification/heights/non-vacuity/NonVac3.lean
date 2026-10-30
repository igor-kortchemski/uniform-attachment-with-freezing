module

import Challenge.Heights

open Freezing1 Filter Topology
open scoped ENNReal NNReal

set_option backward.isDefEq.respectTransparency false

namespace Review

/-- alternating schedule +,-,+,-,... -/
def alt : SignSequence := fun i => decide (i % 2 = 1)

theorem activeCount_succ (x : SignSequence) (i : ℕ) :
    activeCount x (i + 1) = activeCount x i + (if x (i + 1) then 1 else -1) := by
  simp [activeCount, Finset.sum_range_succ]
  ring

theorem activeCount_alt (i : ℕ) : activeCount alt i = if i % 2 = 1 then 2 else 1 := by
  induction i with
  | zero => simp [activeCount]
  | succ i ih =>
    rw [activeCount_succ, ih]
    by_cases h : i % 2 = 1
    · have h2 : (i + 1) % 2 = 0 := by omega
      simp [alt, h, h2]
    · have h' : i % 2 = 0 := by omega
      have h2 : (i + 1) % 2 = 1 := by omega
      simp [alt, h', h2]

theorem extinctionTime_alt : extinctionTime alt = ⊤ := by
  unfold extinctionTime
  rw [dif_neg]
  rintro ⟨k, hk⟩
  rw [activeCount_alt] at hk
  split_ifs at hk <;> omega

theorem hτ_alt : ∀ n : ℕ, (n : ℕ∞) < extinctionTime ((fun _ => alt) n) := by
  intro n
  simp only [extinctionTime_alt]
  exact ENat.natCast_lt_top n

theorem heightScale_succ (x : SignSequence) (n : ℕ) :
    heightScale x (n + 1) =
      heightScale x n + (if x (n + 1) then 1 / (activeCount x (n + 1) : ℝ) else 0) := by
  simp [heightScale, Finset.sum_range_succ]

theorem heightScale_alt (n : ℕ) : heightScale alt n = (((n + 1) / 2 : ℕ) : ℝ) * (1 / 2) := by
  induction n with
  | zero => simp [heightScale]
  | succ n ih =>
    rw [heightScale_succ, ih, activeCount_alt]
    by_cases h : (n + 1) % 2 = 1
    · have e : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      simp [alt, h, e]
      ring
    · have e : (n + 1 + 1) / 2 = (n + 1) / 2 := by omega
      simp [alt, h, e]

theorem hlog_alt :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale ((fun _ => alt) n) n) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    exact this.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun n : ℕ => 4 * (Real.log (n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
    simpa using hlim.const_mul 4
  refine squeeze_zero' ?_ ?_ hup
  · filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [heightScale_alt]
    have : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    simp only [heightScale_alt]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
    have hk : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by
      have : n ≤ 2 * ((n + 1) / 2) := by omega
      exact_mod_cast this
    have hkpos : (0 : ℝ) < (((n + 1) / 2 : ℕ) : ℝ) := by
      have : 0 < (n + 1) / 2 := by omega
      exact_mod_cast this
    rw [div_le_iff₀ (by positivity)]
    have : 4 * (Real.log n / n) * ((((n + 1) / 2 : ℕ) : ℝ) * (1 / 2)) =
        2 * Real.log n * ((((n + 1) / 2 : ℕ) : ℝ) / n) := by
      field_simp
      ring
    rw [this]
    have h3 : (1:ℝ) ≤ 2 * ((((n + 1) / 2 : ℕ) : ℝ) / n) := by
      rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
      linarith
    nlinarith

/-- the alternating schedule violates the bulk condition (S_i is bounded) -/
theorem not_bulk_alt : ¬ BulkLiminf (fun _ => alt) := by
  intro h
  have h0 := h (1 / 2) (by norm_num) (by norm_num)
  have hnn : ∀ n : ℕ, 0 ≤ bulkMinimum (fun _ => alt) (1 / 2) n := by
    intro n
    unfold bulkMinimum
    apply Finset.le_inf'
    intro i _
    rw [activeCount_alt]
    split_ifs <;> positivity
  have hle : ∀ n : ℕ, bulkMinimum (fun _ => alt) (1 / 2) n ≤ 2 / (n : ℝ) := by
    intro n
    unfold bulkMinimum
    refine (Finset.inf'_le _ (by simp [bulkIndices] : n ∈ bulkIndices (1 / 2) n)).trans ?_
    rw [activeCount_alt]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    split_ifs <;> norm_num
  have ht : Tendsto (bulkMinimum (fun _ => alt) (1 / 2)) atTop (𝓝 0) := by
    refine squeeze_zero hnn hle ?_
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [ht.liminf_eq] at h0
  exact lt_irrefl _ h0

end Review
