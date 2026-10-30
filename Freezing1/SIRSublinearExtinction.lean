module

public import Freezing1.SIREarlyExtinction
public import Freezing1.SIRStartup

/-!
# Extinction at any diverging sublinear observation time

The extinction event belongs to the actual stopped SIR chain. Its probability
converges to the geometric Bienaymé extinction probability without an iterated
limit in the observation fraction.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false

theorem sublinear_cutoff_eventually_le (cutoff : ℕ → ℕ)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, cutoff n ≤ n := by
  filter_upwards [hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hh := (div_lt_one hn0).mp hn
  exact_mod_cast hh.le

theorem susceptible_gap_pressure_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    (cutoff : ℕ → ℕ)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (rate n : ℝ) * (n - cutoff n : ℕ)) atTop (𝓝 (lam : ℝ)) := by
  have hh := hscaled.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hsmall)
  simp only [sub_zero, mul_one] at hh
  apply hh.congr'
  filter_upwards [sublinear_cutoff_eventually_le cutoff hsmall,
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Nat.cast_sub hn]
  field_simp

theorem countsFullLaw_sublinear_extinction_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | (H (cutoff n)).infectious = 0}) atTop (𝓝 (1 / (lam : ℝ))) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let b : ℝ := (a + 1 / (lam : ℝ)) / 2
    have hab : a < b := by dsimp [b]; linarith
    have hbr : b < 1 / (lam : ℝ) := by dsimp [b]; linarith
    obtain ⟨k, hk⟩ := ((biasedWalk_sir_extinction_tendsto lam hlam).eventually
      (Ioi_mem_nhds hbr)).exists
    filter_upwards [(countsFullLaw_fixed_extinction_tendsto rate lam hscaled k).eventually
      (Ioi_mem_nhds (hab.trans hk)), hcutoff.eventually_ge_atTop k] with n hn hkn
    exact hn.trans_le (countsFullLaw_extinction_probability_mono (rate n) n hkn)
  · intro a ha
    have hl0 : (lam : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hlam)
    have hp := susceptible_gap_pressure_tendsto rate lam hscaled cutoff hsmall
    have hinv := hp.inv₀ hl0
    simp only [one_div] at ha
    filter_upwards [hp.eventually (Ioi_mem_nhds hlam),
      hinv.eventually (Iio_mem_nhds ha)] with n hn hna
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (countsFullLaw_early_absorption_inv_le (rate n) n (cutoff n) hn.le)
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (by linarith))] at hb
    exact hb.trans_lt hna

end Freezing1.SIR
