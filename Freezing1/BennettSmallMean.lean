module

public import Freezing1.RateFunctionAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! Scalar consequences of the exact Bennett-rate asymptotic. -/

@[expose] public section

namespace Freezing1

open Filter
open scoped Topology

theorem bennettRate_div_self_tendsto_atTop :
    Tendsto (fun u : ℝ => bennettRate u / u) atTop atTop := by
  have h := bennettRate_div_mul_log_tendsto_one.pos_mul_atTop
    zero_lt_one Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  have hu0 : u ≠ 0 := by linarith
  have hl : Real.log u ≠ 0 := (Real.log_pos hu).ne'
  field_simp

theorem smallMean_bennettExponent_tendsto_atTop {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun r : ℝ => r * bennettRate (ε / r)) (𝓝[>] 0) atTop := by
  have hx : Tendsto (fun r : ℝ => ε / r) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using
      (tendsto_inv_nhdsGT_zero : Tendsto (fun r : ℝ => r⁻¹) (𝓝[>] 0) atTop).const_mul_atTop hε
  have h := (bennettRate_div_self_tendsto_atTop.comp hx).const_mul_atTop hε
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := (show 0 < r from hr).ne'
  dsimp only [Function.comp_def]
  field_simp [hε.ne', hr0]

/-- The scalar union bound tends to zero whenever its positive mean is
negligible compared with the logarithmic threshold. This does not assume
or assert a stochastic domination for any epidemic process. -/
theorem bennett_unionBound_tendsto_zero (m : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hmpos : ∀ᶠ n in atTop, 0 < m n)
    (hm : Tendsto (fun n : ℕ => m n / Real.log n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      Real.exp (-m n * bennettRate (ε * Real.log n / m n))) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => m n / Real.log n) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hm, ?_⟩
    filter_upwards [hmpos, eventually_gt_atTop (1 : ℕ)] with n hn hn1
    exact div_pos hn (Real.log_pos (by exact_mod_cast hn1))
  have hexp := (smallMean_bennettExponent_tendsto_atTop hε).comp hr
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hinv
  filter_upwards [hexp.eventually_ge_atTop 2, hmpos,
    eventually_gt_atTop (1 : ℕ)] with n hn hm0 hn1
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  have heq : (m n / Real.log n) * bennettRate (ε / (m n / Real.log n)) =
      m n * bennettRate (ε * Real.log n / m n) / Real.log n := by
    rw [div_div_eq_mul_div]
    ring
  change 2 ≤ (m n / Real.log n) * bennettRate (ε / (m n / Real.log n)) at hn
  rw [heq] at hn
  have hbound := (le_div_iff₀ hlog).mp hn
  calc
    _ ≤ (n : ℝ) * Real.exp (-(2 * Real.log n)) := by
      gcongr
      linarith only [hbound]
    _ = Real.exp (Real.log n) * Real.exp (-(2 * Real.log n)) := by
      rw [Real.exp_log hnp]
    _ = Real.exp (-Real.log n) := by rw [← Real.exp_add]; congr 1; ring
    _ = (n : ℝ)⁻¹ := by rw [Real.exp_neg, Real.exp_log hnp]

end Freezing1
