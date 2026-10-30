module

public import Freezing1.LinearRegimeCutoffs

/-!
# The exact geometric indices in the height chaining argument

The first index is the ceiling of `log A/log C`; the last is the floor of
`log(ε*n/C)/log C`. Rounding retains the full logarithmic number of blocks.
-/

@[expose] public section

namespace Freezing1

open Filter
open scoped Topology

noncomputable def chainLowerIndex (C : ℕ) (A : ℕ → ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (Real.log (A n) / Real.log (C : ℝ))

noncomputable def chainUpperIndex (C : ℕ) (ε : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (Real.log (ε * n / C) / Real.log (C : ℝ))

theorem chainLowerIndex_tendsto_atTop (C : ℕ) (hC : 1 < C)
    {A : ℕ → ℝ} (hA : Tendsto A atTop atTop) :
    Tendsto (chainLowerIndex C A) atTop atTop := by
  have hc : 0 < Real.log (C : ℝ) := Real.log_pos (by exact_mod_cast hC)
  exact tendsto_nat_ceil_atTop.comp ((Real.tendsto_log_atTop.comp hA).atTop_div_const hc)

theorem chainLowerIndex_pow_lower (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ) (n : ℕ)
    (hA : 0 < A n) : A n ≤ ((C ^ chainLowerIndex C A n : ℕ) : ℝ) := by
  have hc : 0 < Real.log (C : ℝ) := Real.log_pos (by exact_mod_cast hC)
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hlog := (div_le_iff₀ hc).mp (Nat.le_ceil (Real.log (A n) / Real.log (C : ℝ)))
  have hh := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hA, Real.exp_nat_mul, Real.exp_log hC0] at hh
  simpa only [chainLowerIndex, Nat.cast_pow] using hh

theorem chainUpperIndex_pow_upper (C : ℕ) (hC : 1 < C) (ε : ℝ) (n : ℕ)
    (hsize : 1 ≤ ε * n / C) :
    ((C ^ chainUpperIndex C ε n : ℕ) : ℝ) ≤ ε * n / C := by
  have hc : 0 < Real.log (C : ℝ) := Real.log_pos (by exact_mod_cast hC)
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have harg : 0 < ε * n / C := lt_of_lt_of_le zero_lt_one hsize
  have hfrac : 0 ≤ Real.log (ε * n / C) / Real.log (C : ℝ) :=
    div_nonneg (Real.log_nonneg hsize) hc.le
  have hlog := (le_div_iff₀ hc).mp (Nat.floor_le hfrac)
  have hh := Real.exp_le_exp.mpr hlog
  rw [Real.exp_nat_mul, Real.exp_log hC0, Real.exp_log harg] at hh
  simpa only [chainUpperIndex, Nat.cast_pow] using hh

theorem tendsto_log_realCutoff_div_log_zero {A : ℕ → ℝ}
    (hA : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (A n) / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' ?_ ?_ hsmall
  · filter_upwards [hA.eventually_ge_atTop 1, hlog.eventually_gt_atTop 0] with n hn hln
    exact div_nonneg (Real.log_nonneg hn) hln.le
  · filter_upwards [hA.eventually_ge_atTop 0, hlog.eventually_gt_atTop 0] with n hn hln
    exact div_le_div_of_nonneg_right (Real.log_le_self hn) hln.le

theorem chainLowerIndex_div_log_tendsto_zero (C : ℕ) (hC : 1 < C)
    {A : ℕ → ℝ} (hA : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (chainLowerIndex C A n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hc : 0 < Real.log (C : ℝ) := Real.log_pos (by exact_mod_cast hC)
  apply tendsto_ceil_div_log_zero
  · filter_upwards [hA.eventually_ge_atTop 1] with n hn
    exact div_nonneg (Real.log_nonneg hn) hc.le
  · have hh := (tendsto_log_realCutoff_div_log_zero hA hsmall).div_const (Real.log (C : ℝ))
    simp only [zero_div] at hh
    convert hh using 1
    funext n
    ring

theorem chainUpperArgument_tendsto_atTop (C : ℕ) (hC : 1 < C)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.log (ε * n / C) / Real.log (C : ℝ)) atTop atTop := by
  have hc : 0 < Real.log (C : ℝ) := Real.log_pos (by exact_mod_cast hC)
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  exact (Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop.const_mul_atTop hε).atTop_div_const hC0)).atTop_div_const hc

theorem chainUpperArgument_div_log_tendsto (C : ℕ) (hC : 1 < C)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Real.log (ε * n / C) / Real.log (C : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 (1 / Real.log (C : ℝ))) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hh := ((tendsto_const_nhds (x := (1 : ℝ))).add
    ((tendsto_const_nhds (x := Real.log ε - Real.log (C : ℝ))).div_atTop hlog)).div_const (Real.log (C : ℝ))
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1, hlog.eventually_gt_atTop 0] with n hn hln
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.log_div (mul_pos hε hn0).ne' hC0.ne', Real.log_mul hε.ne' hn0.ne']
  field_simp
  ring

theorem chainUpperIndex_div_log_tendsto (C : ℕ) (hC : 1 < C)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (chainUpperIndex C ε n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (1 / Real.log (C : ℝ))) := by
  let f : ℕ → ℝ := fun n => Real.log (ε * n / C) / Real.log (C : ℝ)
  have hf : Tendsto f atTop atTop := chainUpperArgument_tendsto_atTop C hC hε
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hlog
  let e : ℕ → ℝ := fun n => (f n - Nat.floor (f n)) / Real.log (n : ℝ)
  have he : Tendsto e atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hinv
    · filter_upwards [hf.eventually_ge_atTop 0, hlog.eventually_gt_atTop 0] with n hn hln
      exact div_nonneg (sub_nonneg.mpr (Nat.floor_le hn)) hln.le
    · filter_upwards [hlog.eventually_gt_atTop 0] with n hln
      apply div_le_div_of_nonneg_right _ hln.le
      have := Nat.sub_one_lt_floor (f n)
      linarith
  have hh := (chainUpperArgument_div_log_tendsto C hC hε).sub he
  simp only [sub_zero] at hh
  convert hh using 1
  funext n
  dsimp [chainUpperIndex, e, f]
  ring

/-- The first admissible geometric block eventually lies strictly before the
last; in particular the natural subtraction below is an ordinary difference. -/
theorem eventually_chain_indices_lt (C : ℕ) (hC : 1 < C)
    {A : ℕ → ℝ} (hA : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, chainLowerIndex C A n < chainUpperIndex C ε n := by
  have hc : 0 < Real.log (C : ℝ) := Real.log_pos (by exact_mod_cast hC)
  have hh := (chainUpperIndex_div_log_tendsto C hC hε).sub
    (chainLowerIndex_div_log_tendsto_zero C hC hA hsmall)
  simp only [sub_zero] at hh
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hh.eventually (lt_mem_nhds (one_div_pos.mpr hc)),
    hlog.eventually_gt_atTop 0] with n hn hln
  have hlt : (chainLowerIndex C A n : ℝ) < chainUpperIndex C ε n :=
    (div_lt_div_iff_of_pos_right hln).mp (by linarith)
  exact_mod_cast hlt

/-- Exact endpoint and intermediate-window bounds for the source's chain. -/
theorem eventually_chain_cutoff_bounds (C : ℕ) (hC : 1 < C)
    {A : ℕ → ℝ} (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n in atTop,
      1 ≤ chainLowerIndex C A n ∧ chainLowerIndex C A n ≤ chainUpperIndex C ε n ∧
      A n ≤ ((C ^ chainLowerIndex C A n : ℕ) : ℝ) ∧
      ((C ^ chainUpperIndex C ε n : ℕ) : ℝ) ≤ ε * n / C ∧
      ∀ k : ℕ, chainLowerIndex C A n ≤ k → k ≤ chainUpperIndex C ε n →
        A n ≤ ((C ^ k : ℕ) : ℝ) ∧ ((C ^ k : ℕ) : ℝ) ≤ ε * n / C ∧ C ^ k * C ≤ n := by
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hscale : Tendsto (fun n : ℕ => ε * n / C) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hε).atTop_div_const hC0
  filter_upwards [(chainLowerIndex_tendsto_atTop C hC hAinf).eventually_ge_atTop 1,
    eventually_chain_indices_lt C hC hAinf hsmall hε, hscale.eventually_ge_atTop 1]
    with n hn hlt hsize
  have hlo := chainLowerIndex_pow_lower C hC A n (hA n)
  have hup := chainUpperIndex_pow_upper C hC ε n hsize
  refine ⟨hn, hlt.le, hlo, hup, ?_⟩
  intro k hk0 hkK
  have hlow : A n ≤ ((C ^ k : ℕ) : ℝ) := hlo.trans (by
    simpa only [Nat.cast_pow] using pow_le_pow_right₀
      (by exact_mod_cast hC.le : (1 : ℝ) ≤ C) hk0)
  have hhigh : ((C ^ k : ℕ) : ℝ) ≤ ε * n / C := (show
      ((C ^ k : ℕ) : ℝ) ≤ ((C ^ chainUpperIndex C ε n : ℕ) : ℝ) by
        simpa only [Nat.cast_pow] using pow_le_pow_right₀
          (by exact_mod_cast hC.le : (1 : ℝ) ≤ C) hkK).trans hup
  refine ⟨hlow, hhigh, ?_⟩
  have hm := (le_div_iff₀ hC0).mp hhigh
  have hnR : ε * (n : ℝ) ≤ n := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hprod : (((C ^ k : ℕ) : ℝ) * C) ≤ n := hm.trans hnR
  exact_mod_cast hprod

/-- The exact number of blocks used by the source has logarithmic span one.
The natural subtraction handles every finite initial index, and agrees with
the real difference throughout the eventual admissible window. -/
theorem chain_log_span_tendsto_one (C : ℕ) (hC : 1 < C)
    {A : ℕ → ℝ} (hA : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ((chainUpperIndex C ε n - chainLowerIndex C A n : ℕ) : ℝ) *
        Real.log (C : ℝ) / Real.log (n : ℝ)) atTop (𝓝 1) := by
  have hc : 0 < Real.log (C : ℝ) := Real.log_pos (by exact_mod_cast hC)
  have hh := ((chainUpperIndex_div_log_tendsto C hC hε).sub
    (chainLowerIndex_div_log_tendsto_zero C hC hA hsmall)).mul_const (Real.log (C : ℝ))
  simp only [sub_zero, div_mul_cancel₀ 1 hc.ne'] at hh
  apply hh.congr'
  filter_upwards [eventually_chain_indices_lt C hC hA hsmall hε] with n hn
  rw [Nat.cast_sub hn.le]
  ring

end Freezing1
