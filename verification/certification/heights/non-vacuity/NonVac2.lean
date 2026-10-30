module

import Challenge.Heights

open Freezing1 Filter Topology
open scoped ENNReal NNReal

set_option backward.isDefEq.respectTransparency false

namespace Review

def allPlus : SignSequence := fun _ => true

theorem activeCount_allPlus (i : ℕ) : activeCount allPlus i = (i : ℤ) + 1 := by
  simp [activeCount, allPlus]
  ring

noncomputable def Afun (n : ℕ) : ℝ := 1 + Real.sqrt (Real.log n)

theorem Afun_pos (n : ℕ) : 0 < Afun n := by
  unfold Afun; positivity

theorem log_tendsto : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem Afun_tendsto : Tendsto Afun atTop atTop := by
  have h2 := Real.tendsto_sqrt_atTop.comp log_tendsto
  exact tendsto_atTop_add_const_left _ 1 h2

theorem Afun_small : Tendsto (fun n : ℕ => Afun n / Real.log n) atTop (𝓝 0) := by
  have h3 : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp log_tendsto
  have h4 : Tendsto (fun n : ℕ => (Real.sqrt (Real.log n))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp log_tendsto)
  have h5 := h3.add h4
  rw [add_zero] at h5
  refine h5.congr' ?_
  filter_upwards [log_tendsto.eventually_gt_atTop 0] with n hn
  unfold Afun
  rw [add_div, Real.sqrt_div_self']
  simp only [one_div]

theorem nearOrigin_allPlus : NearOriginLimsup (fun _ => allPlus) Afun 1 := by
  unfold NearOriginLimsup
  have key : ∀ ε : ℝ, 0 < ε →
      limsup (nearOriginMaximum (fun _ => allPlus) Afun 1 ε) atTop = 0 := by
    intro ε hε
    have hle : ∀ n, nearOriginMaximum (fun _ => allPlus) Afun 1 ε n ≤ (Afun n)⁻¹ := by
      intro n
      have hB : 0 ≤ (Afun n)⁻¹ := (inv_pos.mpr (Afun_pos n)).le
      unfold nearOriginMaximum
      calc _ ≤ (((Afun n)⁻¹).toNNReal : ℝ) := by
            apply NNReal.coe_le_coe.mpr
            apply Finset.sup_le
            intro i hi
            rw [Real.le_toNNReal_iff_coe_le hB]
            simp only [nearOriginIndices, Finset.mem_filter] at hi
            have hi' : Afun n ≤ (i : ℝ) := hi.2.1
            have hipos : 0 < (i : ℝ) := lt_of_lt_of_le (Afun_pos n) hi'
            show |(activeCount allPlus i : ℝ) / i - 1| ≤ (Afun n)⁻¹
            rw [activeCount_allPlus]
            push_cast
            have : ((i : ℝ) + 1) / i - 1 = (i : ℝ)⁻¹ := by field_simp; ring
            rw [this, abs_of_pos (inv_pos.mpr hipos)]
            exact inv_anti₀ (Afun_pos n) hi'
        _ = (Afun n)⁻¹ := Real.coe_toNNReal _ hB
    have hnn : ∀ n, 0 ≤ nearOriginMaximum (fun _ => allPlus) Afun 1 ε n := fun n =>
      NNReal.coe_nonneg _
    have ht : Tendsto (nearOriginMaximum (fun _ => allPlus) Afun 1 ε) atTop (𝓝 0) :=
      squeeze_zero hnn hle (tendsto_inv_atTop_zero.comp Afun_tendsto)
    exact ht.limsup_eq
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (key ε hε).symm

theorem bulk_allPlus : BulkLiminf (fun _ => allPlus) := by
  intro ε hε hε1
  have hge : ∀ n : ℕ, 1 ≤ n → ε ≤ bulkMinimum (fun _ => allPlus) ε n := by
    intro n hn
    unfold bulkMinimum
    apply Finset.le_inf'
    intro i hi
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [activeCount_allPlus]
    push_cast
    rw [le_div_iff₀ hnpos]
    simp only [bulkIndices, Finset.mem_insert, Finset.mem_filter] at hi
    rcases hi with rfl | ⟨_, hi2⟩
    · nlinarith
    · nlinarith
  have hbd : ∀ n : ℕ, bulkMinimum (fun _ => allPlus) ε n ≤ 2 := by
    intro n
    unfold bulkMinimum
    refine (Finset.inf'_le _ (by simp [bulkIndices] : n ∈ bulkIndices ε n)).trans ?_
    rw [activeCount_allPlus]
    push_cast
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_iff₀ hnpos]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  calc (0 : ℝ) < ε := hε
    _ ≤ liminf (bulkMinimum (fun _ => allPlus) ε) atTop := by
      apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hbd)
      filter_upwards [eventually_ge_atTop 1] with n hn using hge n hn

end Review
