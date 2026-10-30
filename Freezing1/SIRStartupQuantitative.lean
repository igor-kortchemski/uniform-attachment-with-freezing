module

public import Freezing1.SIRStartup

/-!
# The source's matching early-window and error parameter

The window is exactly `eps * n` and the allowed relative error is exactly
`2 * eps`. The strict margin comes from the finite limiting infection
probability being less than one. General varying per-pair rates are kept.
-/

@[expose] public section

namespace Freezing1.SIR.Susceptible

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem infectionProbability_linear_window_sandwich (rate : ℝ≥0) {n : ℕ} {H : ℕ → ℕ}
    (hbounds : ∀ i, n - i ≤ H i ∧ H i ≤ n) {eps : ℝ} (_heps : 0 ≤ eps)
    {i : ℕ} (hi : (i : ℝ) ≤ eps * n) :
    (1 - eps) * (infectionProbability rate n : ℝ) ≤ infectionProbability rate (H i) ∧
      infectionProbability rate (H i) ≤ infectionProbability rate n := by
  refine ⟨?_, infectionProbability_mono_susceptible rate (hbounds i).2⟩
  by_cases heps1 : 1 ≤ eps
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (infectionProbability rate n).property.1).trans (infectionProbability rate (H i)).property.1
  · have hinR : (i : ℝ) ≤ n := by
      have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hin : i ≤ n := by exact_mod_cast hinR
    have hgap : (1 - eps) * (n : ℝ) ≤ ((n - i : ℕ) : ℝ) := by
      rw [Nat.cast_sub hin]
      nlinarith
    have hnum : (1 - eps) * ((rate : ℝ) * n) ≤ (rate : ℝ) * (n - i : ℕ) := by
      have hh := mul_le_mul_of_nonneg_left hgap rate.coe_nonneg
      nlinarith
    have hfrac := div_le_div_of_nonneg_right hnum
      (show 0 ≤ 1 + (rate : ℝ) * n by positivity)
    have he : (1 - eps) * (infectionProbability rate n : ℝ) =
        ((1 - eps) * ((rate : ℝ) * n)) / (1 + (rate : ℝ) * n) := by
      rw [infectionProbability_coe]
      ring
    rw [he]
    exact hfrac.trans (infectionProbability_prefix_lower_bound rate (hbounds i).1 (hbounds i).2)

theorem infectionProbability_linear_window_error (rate : ℝ≥0) {n : ℕ} {H : ℕ → ℕ}
    (hbounds : ∀ i, n - i ≤ H i ∧ H i ≤ n) {eps : ℝ} (heps : 0 ≤ eps)
    {i : ℕ} (hi : (i : ℝ) ≤ eps * n) (p : ℝ) :
    |(infectionProbability rate (H i) : ℝ) - p| ≤
      eps * (infectionProbability rate n : ℝ) + |(infectionProbability rate n : ℝ) - p| := by
  obtain ⟨hlo, hhi⟩ := infectionProbability_linear_window_sandwich rate hbounds heps hi
  have hhiR : (infectionProbability rate (H i) : ℝ) ≤ infectionProbability rate n := hhi
  rw [abs_le]
  have hprod : 0 ≤ eps * (infectionProbability rate n : ℝ) :=
    mul_nonneg heps (infectionProbability rate n).property.1
  constructor <;> nlinarith [le_abs_self ((infectionProbability rate n : ℝ) - p),
    neg_abs_le ((infectionProbability rate n : ℝ) - p)]

/-- This is the auxiliary displayed startup assertion with exactly the
same `eps` in the linear horizon and the bound `2 * eps`. -/
theorem relative_startup_same_epsilon_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop) {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => fullLaw (rate n) n
      {H | ∃ k ≥ cutoff n, (k : ℝ) ≤ eps * n ∧
        2 * eps ≤ |infectiousRatio n H k - ((lam : ℝ) - 1) / ((lam : ℝ) + 1)|})
      atTop (nhds 0) := by
  let p : ℝ := infectionProbability lam 1
  let gap : ℝ := eps * (1 - p)
  let eta : ℝ := gap / (4 * (eps + 1))
  let a : ℝ := eps * p + gap / 4
  have hp1 : p < 1 := infectionProbability_lt_one lam 1
  have hg : 0 < gap := by dsimp [gap]; positivity
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hmargin : 2 * a + gap ≤ 2 * eps := by
    dsimp [a, gap]
    nlinarith
  have hp := infectionProbability_scaled_tendsto rate lam hscaled
  have hp_event : ∀ᶠ n in atTop, |(infectionProbability (rate n) n : ℝ) - p| < eta := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hp) eta heta
    filter_upwards [eventually_ge_atTop N] with n hn
    have hh := hN n hn
    rw [Real.dist_eq] at hh
    exact hh
  have hc : Tendsto (fun n => (cutoff n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcutoff
  have hbound : ∀ᶠ n in atTop, fullLaw (rate n) n
      {H | ∃ k ≥ cutoff n, (k : ℝ) ≤ eps * n ∧
        2 * eps ≤ |infectiousRatio n H k - ((lam : ℝ) - 1) / ((lam : ℝ) + 1)|} ≤
      fullLaw (rate n) n {H | ∃ k ≥ cutoff n, (gap / 8) * (k : ℝ) ≤ |noise (rate n) n H k|} := by
    filter_upwards [hp_event, hc.eventually (eventually_gt_atTop (4 / gap))] with n hp_close hcut
    apply measure_mono_ae
    filter_upwards [fullLaw_bounds (rate n) n] with H hb
    rintro ⟨k, hk, htime, hbad⟩
    refine ⟨k, hk, ?_⟩
    have hkR : (cutoff n : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := (div_pos (by norm_num) hg).trans (hcut.trans_le hkR)
    have hone : 1 < gap / 4 * k := by
      have hh := (div_lt_iff₀ hg).mp (hcut.trans_le hkR)
      nlinarith
    have hdrift : ∀ i < k, |(infectionProbability (rate n) (H i) : ℝ) - p| ≤ a := by
      intro i hi
      have hiR : (i : ℝ) ≤ k := by exact_mod_cast hi.le
      have hh := infectionProbability_linear_window_error (rate n) hb heps.le (hiR.trans htime) p
      have habs := le_abs_self ((infectionProbability (rate n) n : ℝ) - p)
      have h_eta : (eps + 1) * eta = gap / 4 := by
        dsimp [eta]
        field_simp
      dsimp [a]
      nlinarith
    rw [← startupSlope_eq] at hbad
    change 2 * eps ≤ |infectiousRatio n H k - (2 * p - 1)| at hbad
    have he : infectiousRatio n H k - (2 * p - 1) =
        ((infectious n k H : ℝ) - (2 * p - 1) * k) / k := by
      unfold infectiousRatio
      field_simp
    rw [he, abs_div, abs_of_pos hkpos] at hbad
    have hbad' := (le_div_iff₀ hkpos).mp hbad
    have hd := infectious_relative_drift_error (rate n) n k H p a hdrift
    have hmargin' := mul_le_mul_of_nonneg_right hmargin hkpos.le
    by_contra hnot
    have hsmall := lt_of_not_ge hnot
    nlinarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (noise_relative_tendsto rate cutoff hcutoff (by positivity : 0 < gap / 8))
    (Eventually.of_forall fun _ => bot_le) hbound

theorem logLog_startup_same_epsilon_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => fullLaw (rate n) n
      {H | ∃ k : ℕ, Real.log (Real.log (n : ℝ)) ≤ (k : ℝ) ∧ (k : ℝ) ≤ eps * n ∧
        2 * eps ≤ |infectiousRatio n H k - ((lam : ℝ) - 1) / ((lam : ℝ) + 1)|})
      atTop (nhds 0) := by
  simpa only [ge_iff_le, logLogStartupCutoff_le] using
    relative_startup_same_epsilon_tendsto rate lam hscaled
      logLogStartupCutoff logLogStartupCutoff_tendsto heps

end Freezing1.SIR.Susceptible
