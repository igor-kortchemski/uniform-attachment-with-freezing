module

import Challenge.Heights

open Freezing1 Filter Topology
open scoped ENNReal NNReal

set_option backward.isDefEq.respectTransparency false

namespace Review

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

/-- General criterion: bounded deviation from the line `c i`. -/
theorem nearOrigin_of_linear (x : ℕ → SignSequence) (c K : ℝ) (hK : 0 ≤ K)
    (hdev : ∀ n i, |(activeCount (x n) i : ℝ) - c * i| ≤ K) :
    NearOriginLimsup x Afun c := by
  unfold NearOriginLimsup
  have key : ∀ ε : ℝ, 0 < ε → limsup (nearOriginMaximum x Afun c ε) atTop = 0 := by
    intro ε hε
    have hle : ∀ n, nearOriginMaximum x Afun c ε n ≤ K * (Afun n)⁻¹ := by
      intro n
      have hB : 0 ≤ K * (Afun n)⁻¹ := mul_nonneg hK (inv_pos.mpr (Afun_pos n)).le
      unfold nearOriginMaximum
      calc _ ≤ ((K * (Afun n)⁻¹).toNNReal : ℝ) := by
            apply NNReal.coe_le_coe.mpr
            apply Finset.sup_le
            intro i hi
            rw [Real.le_toNNReal_iff_coe_le hB]
            simp only [nearOriginIndices, Finset.mem_filter] at hi
            have hi' : Afun n ≤ (i : ℝ) := hi.2.1
            have hipos : 0 < (i : ℝ) := lt_of_lt_of_le (Afun_pos n) hi'
            show |(activeCount (x n) i : ℝ) / i - c| ≤ K * (Afun n)⁻¹
            have h1 : (activeCount (x n) i : ℝ) / i - c =
                ((activeCount (x n) i : ℝ) - c * i) / i := by field_simp
            rw [h1, abs_div, abs_of_pos hipos, div_le_iff₀ hipos]
            calc |(activeCount (x n) i : ℝ) - c * i| ≤ K := hdev n i
              _ = K * (Afun n)⁻¹ * Afun n := by field_simp [(Afun_pos n).ne']
              _ ≤ K * (Afun n)⁻¹ * i := by
                  apply mul_le_mul_of_nonneg_left hi' hB
        _ = K * (Afun n)⁻¹ := Real.coe_toNNReal _ hB
    have hnn : ∀ n, 0 ≤ nearOriginMaximum x Afun c ε n := fun n => NNReal.coe_nonneg _
    have ht : Tendsto (nearOriginMaximum x Afun c ε) atTop (𝓝 0) := by
      refine squeeze_zero hnn hle ?_
      simpa using (tendsto_inv_atTop_zero.comp Afun_tendsto).const_mul K
    exact ht.limsup_eq
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (key ε hε).symm

theorem bulk_of_linear (x : ℕ → SignSequence) (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K)
    (hdev : ∀ n i, |(activeCount (x n) i : ℝ) - c * i| ≤ K) : BulkLiminf x := by
  intro ε hε hε1
  have hbd : ∀ n : ℕ, bulkMinimum x ε n ≤ c + K + 1 := by
    intro n
    unfold bulkMinimum
    refine (Finset.inf'_le _ (by simp [bulkIndices] : n ∈ bulkIndices ε n)).trans ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp; positivity
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_le_iff₀ hnpos]
      have := (abs_le.mp (hdev n n)).2
      nlinarith
  have hε' : 0 < c * ε / 2 := by positivity
  calc (0 : ℝ) < c * ε / 2 := hε'
    _ ≤ liminf (bulkMinimum x ε) atTop := by
      apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hbd)
      filter_upwards [eventually_ge_atTop (⌈2 * K / (c * ε)⌉₊ + 1)] with n hn
      have hn1 : (2 * K / (c * ε)) ≤ n := by
        have := Nat.le_ceil (2 * K / (c * ε))
        have h2 : ((⌈2 * K / (c * ε)⌉₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
        linarith
      have hnpos : (0 : ℝ) < n := by
        have : (0:ℝ) ≤ 2 * K / (c * ε) := by positivity
        have h2 : ((⌈2 * K / (c * ε)⌉₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
        have := Nat.cast_nonneg (α := ℝ) ⌈2 * K / (c * ε)⌉₊
        linarith
      unfold bulkMinimum
      apply Finset.le_inf'
      intro i hi
      simp only [bulkIndices, Finset.mem_insert, Finset.mem_filter] at hi
      have hi2 : ε * n ≤ (i : ℝ) := by
        rcases hi with rfl | ⟨_, h⟩
        · nlinarith
        · exact h
      have hd := (abs_le.mp (hdev n i)).1
      rw [le_div_iff₀ hnpos]
      have hK2 : K ≤ c * ε * n / 2 := by
        rw [div_le_iff₀ (by positivity)] at hn1
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        nlinarith [hn1]
      nlinarith [mul_le_mul_of_nonneg_left hi2 hc.le]

/-! ### the period-3 schedule +,+,-,+,+,-,... : slope c = 1/3 -/
def pat3 : SignSequence := fun i => decide (i % 3 ≠ 0)

theorem activeCount_succ (x : SignSequence) (i : ℕ) :
    activeCount x (i + 1) = activeCount x i + (if x (i + 1) then 1 else -1) := by
  simp [activeCount, Finset.sum_range_succ]
  ring

theorem activeCount_pat3 (i : ℕ) : activeCount pat3 i = 1 + (i : ℤ) - 2 * ((i / 3 : ℕ) : ℤ) := by
  induction i with
  | zero => simp [activeCount]
  | succ i ih =>
    rw [activeCount_succ, ih]
    by_cases h : (i + 1) % 3 = 0
    · simp [pat3, h]
      omega
    · simp [pat3, h]
      omega

theorem dev_pat3 : ∀ n i : ℕ, |(activeCount ((fun _ => pat3) n) i : ℝ) - (1 / 3 : ℝ) * i| ≤ 3 := by
  intro n i
  show |(activeCount pat3 i : ℝ) - (1 / 3 : ℝ) * i| ≤ 3
  have e : (activeCount pat3 i : ℝ) = 1 + (i : ℝ) - 2 * ((i / 3 : ℕ) : ℝ) := by
    rw [activeCount_pat3]
    simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast,
      Int.cast_ofNat]
  rw [e]
  have h1 : 3 * (i / 3) ≤ i := Nat.mul_div_le i 3
  have h2 : i < 3 * (i / 3) + 3 := by omega
  have h1' : (3 : ℝ) * ((i / 3 : ℕ) : ℝ) ≤ i := by exact_mod_cast h1
  have h2' : (i : ℝ) < 3 * ((i / 3 : ℕ) : ℝ) + 3 := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> nlinarith

theorem hτ_pat3 : ∀ n : ℕ, (n : ℕ∞) < extinctionTime ((fun _ => pat3) n) := by
  intro n
  have : extinctionTime pat3 = ⊤ := by
    unfold extinctionTime
    rw [dif_neg]
    rintro ⟨k, hk⟩
    rw [activeCount_pat3] at hk
    omega
  show (n : ℕ∞) < extinctionTime pat3
  rw [this]
  exact ENat.natCast_lt_top n

/-- all hypotheses of Theorem thm:lineaire hold with c = 1/3 -/
theorem hypotheses_pat3 :
    (0 < (1/3 : ℝ)) ∧ ((1/3 : ℝ) ≤ 1) ∧ (∀ n, 0 < Afun n) ∧ Tendsto Afun atTop atTop ∧
    Tendsto (fun n : ℕ => Afun n / Real.log (n : ℝ)) atTop (𝓝 0) ∧
    (∀ n : ℕ, (n : ℕ∞) < extinctionTime ((fun _ => pat3) n)) ∧
    NearOriginLimsup (fun _ => pat3) Afun (1/3) ∧ BulkLiminf (fun _ => pat3) :=
  ⟨by norm_num, by norm_num, Afun_pos, Afun_tendsto, Afun_small, hτ_pat3,
    nearOrigin_of_linear _ _ 3 (by norm_num) dev_pat3,
    bulk_of_linear _ (1/3) 3 (by norm_num) (by norm_num) dev_pat3⟩

end Review
