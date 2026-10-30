module

public import Freezing1.HeightScaleBounds

/-!
# Integer cutoffs for the linear regime

The real lower cutoff is rounded upwards, while the fixed macroscopic upper
cutoff is rounded downwards. The logarithmic span between them is asymptotic
to `log n`, with all rounding errors retained in the proofs.
-/

@[expose] public section

namespace Freezing1

open Filter
open scoped Topology

/-- A fixed positive proportion rounded down still has that asymptotic proportion. -/
theorem tendsto_floor_mul_div_nat {ε : ℝ} (hε : 0 ≤ ε) :
    Tendsto (fun n : ℕ => (Nat.floor (ε * n) : ℝ) / n) atTop (𝓝 ε) := by
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := by
    have hh := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    change Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) at hh
    simpa only [one_div] using hh
  let d (n : ℕ) : ℝ := (ε * n - Nat.floor (ε * n)) / n
  have hd : Tendsto d atTop (𝓝 0) := by
    apply squeeze_zero (fun n => div_nonneg (sub_nonneg.mpr (Nat.floor_le (by positivity))) (by positivity)) ?_ hi
    intro n
    exact div_le_div_of_nonneg_right (by have := Nat.sub_one_lt_floor (ε * (n : ℝ)); linarith) (Nat.cast_nonneg n)
  have hh := (tendsto_const_nhds (x := ε) : Tendsto (fun _ : ℕ => ε) atTop (𝓝 ε)).sub hd
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [d]
  field_simp
  ring

theorem floor_mul_le_self {ε : ℝ} (hε : ε ≤ 1) (n : ℕ) : Nat.floor (ε * n) ≤ n := by
  apply Nat.floor_le_of_le
  have hh := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [one_mul] using hh

/-- Any sublogarithmic natural lower cutoff is eventually separated from a fixed-proportion cutoff. -/
theorem eventually_two_mul_cutoff_lt_floor {a : ℕ → ℕ}
    (hsmall : Tendsto (fun n : ℕ => (a n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 2 * a n < Nat.floor (ε * n) := by
  have hfloor := tendsto_floor_mul_div_nat hε.le
  have ha := (tendsto_natCutoff_div_nat_zero_of_sublog hsmall).const_mul 2
  have hd := hfloor.sub ha
  simp only [mul_zero, sub_zero] at hd
  filter_upwards [eventually_ge_atTop 1, hd.eventually (lt_mem_nhds hε)] with n hn hdiff
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh : (2 * a n : ℝ) < Nat.floor (ε * n) := by
    have he : (Nat.floor (ε * n) : ℝ) / n - 2 * ((a n : ℝ) / n) =
        ((Nat.floor (ε * n) : ℝ) - 2 * a n) / n := by ring
    rw [he] at hdiff
    have hc := (lt_div_iff₀ hnR).mp hdiff
    linarith
  exact_mod_cast hh

/-- The logarithm of a positive sublogarithmic natural cutoff is negligible. -/
theorem tendsto_log_natCutoff_div_log_zero {a : ℕ → ℕ}
    (ha : ∀ᶠ n in atTop, 1 ≤ a n)
    (hsmall : Tendsto (fun n : ℕ => (a n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (a n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' ?_ ?_ hsmall
  · filter_upwards [ha, hlog.eventually_gt_atTop 0] with n hn hln
    apply div_nonneg _ hln.le
    exact Real.log_nonneg (by exact_mod_cast hn)
  · filter_upwards [hlog.eventually_gt_atTop 0] with n hln
    exact div_le_div_of_nonneg_right (Real.log_le_self (Nat.cast_nonneg _)) hln.le

/-- The logarithm of the upper cutoff is asymptotic to `log n`. -/
theorem tendsto_log_floor_mul_div_log {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.log (Nat.floor (ε * n) : ℝ) / Real.log (n : ℝ)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := tendsto_floor_mul_div_nat hε.le
  have hlogratio := (Real.continuousAt_log hε.ne').tendsto.comp hratio
  have hsmall : Tendsto (fun n : ℕ =>
      Real.log ((Nat.floor (ε * n) : ℝ) / n) / Real.log (n : ℝ)) atTop (𝓝 0) :=
    hlogratio.div_atTop hlog
  have hh := (tendsto_const_nhds (x := (1 : ℝ)) : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hsmall
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1, hlog.eventually_gt_atTop 0,
    hratio.eventually (lt_mem_nhds hε)] with n hn hln hpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb : (0 : ℝ) < Nat.floor (ε * n) := by
    have := (lt_div_iff₀ hnR).mp hpos
    simpa only [zero_mul] using this
  rw [Real.log_div hb.ne' hnR.ne']
  field_simp
  ring

/-- The central block has the full logarithmic span. -/
theorem tendsto_log_floor_div_cutoff_div_log {a : ℕ → ℕ}
    (ha : ∀ᶠ n in atTop, 1 ≤ a n)
    (hsmall : Tendsto (fun n : ℕ => (a n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      Real.log ((Nat.floor (ε * n) : ℝ) / a n) / Real.log (n : ℝ)) atTop (𝓝 1) := by
  have hh := (tendsto_log_floor_mul_div_log hε).sub
    (tendsto_log_natCutoff_div_log_zero ha hsmall)
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [ha, eventually_two_mul_cutoff_lt_floor hsmall hε] with n hn hlt
  have haR : (0 : ℝ) < a n := by exact_mod_cast (show 0 < a n by omega)
  have hbR : (0 : ℝ) < Nat.floor (ε * n) := by exact_mod_cast (show 0 < Nat.floor (ε * n) by omega)
  rw [Real.log_div hbR.ne' haR.ne', sub_div]

/-- All index bounds for the ceiling/floor cutoffs used in the source proof. -/
theorem eventually_ceil_floor_cutoff_bounds {A : ℕ → ℝ}
    (hA : ∀ n, 0 < A n)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ Nat.ceil (A n) ∧
      Nat.ceil (A n) ≤ Nat.floor (ε * n) ∧ Nat.ceil (A n) < Nat.floor (ε * n) ∧
      2 * Nat.ceil (A n) < Nat.floor (ε * n) ∧ Nat.floor (ε * n) ≤ n := by
  have hc := tendsto_ceil_div_log_zero (Eventually.of_forall fun n => (hA n).le) hsmall
  filter_upwards [eventually_two_mul_cutoff_lt_floor hc hε] with n hn
  have hap := Nat.one_le_ceil_iff.mpr (hA n)
  exact ⟨hap, by omega, by omega, hn, floor_mul_le_self hε1.le n⟩

/-- Scalar logarithmic normalization for the source's real lower cutoff. -/
theorem tendsto_log_floor_div_ceil_div_log {A : ℕ → ℝ}
    (hA : ∀ n, 0 < A n)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.log ((Nat.floor (ε * n) : ℝ) / Nat.ceil (A n)) /
      Real.log (n : ℝ)) atTop (𝓝 1) :=
  tendsto_log_floor_div_cutoff_div_log
    (Eventually.of_forall fun n => Nat.one_le_ceil_iff.mpr (hA n))
    (tendsto_ceil_div_log_zero (Eventually.of_forall fun n => (hA n).le) hsmall) hε

end Freezing1
