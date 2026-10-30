module

public import Freezing1.RateFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! The exact rate asymptotic used in the late SIR height argument. -/

@[expose] public section

namespace Freezing1

open Filter Asymptotics
open scoped Topology

theorem bennettRate_div_mul_log_tendsto_one :
    Tendsto (fun u : ℝ => bennettRate u / (u * Real.log u)) atTop (𝓝 1) := by
  have hi : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hl : Tendsto (fun u : ℝ => (Real.log u)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have ha : Tendsto (fun u : ℝ => 1 + u⁻¹) atTop (𝓝 1) := by
    simpa using hi.const_add (1 : ℝ)
  have hs : Tendsto (fun u : ℝ => Real.log (1 + u⁻¹)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp ha
  have hlim : Tendsto (fun u : ℝ =>
      (1 + u⁻¹) * (1 + Real.log (1 + u⁻¹) * (Real.log u)⁻¹) - (Real.log u)⁻¹)
      atTop (𝓝 1) := by
    simpa using (ha.mul ((hs.mul hl).const_add (1 : ℝ))).sub hl
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hlu : 0 < Real.log u := Real.log_pos hu
  have hfactor : 1 + u = u * (1 + u⁻¹) := by field_simp; ring
  have hlog : Real.log (1 + u) = Real.log u + Real.log (1 + u⁻¹) := by
    rw [hfactor, Real.log_mul hu0.ne' (by positivity : (1 + u⁻¹ : ℝ) ≠ 0)]
  rw [bennettRate, hlog]
  field_simp [hu0.ne', hlu.ne']
  ring

theorem bennettRate_isEquivalent_mul_log :
    bennettRate ~[atTop] (fun u : ℝ => u * Real.log u) := by
  apply (isEquivalent_iff_tendsto_one ?_).mpr bennettRate_div_mul_log_tendsto_one
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  exact mul_ne_zero (by linarith : u ≠ 0) (Real.log_pos hu).ne'

end Freezing1
