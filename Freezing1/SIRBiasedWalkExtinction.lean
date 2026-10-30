module

public import Freezing1.SIRBiasedWalk

/-!
# Exact limiting extinction probability of the biased walk

A contracting masked exponential makes the positive contribution to a
harmonic exponential vanish. This proves the true absorbed-walk probability,
without an optional-stopping theorem or a conditional survival argument.
-/

@[expose] public section

namespace Freezing1.SIR.BiasedWalk

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical

theorem fullLaw_positivePower_tendsto_zero (p : unitInterval) {q rho : ℝ}
    (hq : 0 < q) (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (he : (p : ℝ) * q + (1 - (p : ℝ)) / q = rho) :
    Tendsto (fun k : ℕ => ∫⁻ H, ENNReal.ofReal (positivePower q (H k)) ∂fullLaw p)
      atTop (𝓝 0) := by
  have hh : Tendsto (fun k : ℕ => rho ^ k * q) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hrho hrho1).mul_const q)
  have hb : Tendsto (fun k : ℕ => ENNReal.ofReal (rho ^ k * q)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.tendsto 0 |>.comp hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => bot_le) (fullLaw_positivePower_le p hq hrho he)

theorem power_decomposition (p : unitInterval) (r : ℝ) (k : ℕ) :
    (∫⁻ H, ENNReal.ofReal (r ^ H k) ∂fullLaw p) =
      fullLaw p {H | H k = 0} +
        ∫⁻ H, ENNReal.ofReal (positivePower r (H k)) ∂fullLaw p := by
  have hm : MeasurableSet {H : ℕ → ℕ | H k = 0} :=
    (measurableSet_singleton 0).preimage (measurable_pi_apply k)
  calc
    _ = ∫⁻ H, ({H : ℕ → ℕ | H k = 0}.indicator (fun _ => 1)) H +
        ENNReal.ofReal (positivePower r (H k)) ∂fullLaw p := by
      apply lintegral_congr
      intro H
      by_cases hz : H k = 0 <;> simp [positivePower, hz]
    _ = _ := by
      rw [lintegral_add_left (measurable_const.indicator hm)]
      change (∫⁻ H, {H : ℕ → ℕ | H k = 0}.indicator 1 H ∂fullLaw p) + _ = _
      rw [lintegral_indicator_one hm]

theorem zero_probability_tendsto_of_parameters (p : unitInterval) {r q rho : ℝ}
    (hr : 0 ≤ r) (hrq : r ≤ q) (hq : 0 < q) (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hodds : (p : ℝ) * r = 1 - (p : ℝ))
    (he : (p : ℝ) * q + (1 - (p : ℝ)) / q = rho) :
    Tendsto (fun k : ℕ => fullLaw p {H | H k = 0}) atTop (𝓝 (ENNReal.ofReal r)) := by
  have hpos (k : ℕ) :
      (∫⁻ H, ENNReal.ofReal (positivePower r (H k)) ∂fullLaw p) ≤
        ∫⁻ H, ENNReal.ofReal (positivePower q (H k)) ∂fullLaw p := by
    apply lintegral_mono
    intro H
    apply ENNReal.ofReal_le_ofReal
    unfold positivePower
    split_ifs
    · exact le_rfl
    · exact pow_le_pow_left₀ hr hrq _
  have hdecomp (k : ℕ) := (power_decomposition p r k).symm.trans
    (fullLaw_power_harmonic p hr hodds k)
  have hnoise := fullLaw_positivePower_tendsto_zero p hq hrho hrho1 he
  have hlower : Tendsto (fun k : ℕ => ENNReal.ofReal r -
      ∫⁻ H, ENNReal.ofReal (positivePower q (H k)) ∂fullLaw p) atTop
      (𝓝 (ENNReal.ofReal r)) := by
    simpa only [Function.comp_def, tsub_zero] using
      (ENNReal.tendsto_sub (Or.inl ENNReal.ofReal_ne_top)).comp
      (tendsto_const_nhds.prodMk_nhds hnoise)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · intro k
    apply tsub_le_iff_right.mpr
    rw [← hdecomp k]
    exact add_le_add le_rfl (hpos k)
  · intro k
    rw [← hdecomp k]
    exact le_add_right le_rfl

theorem zero_probability_tendsto (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    Tendsto (fun k : ℕ => fullLaw p {H | H k = 0}) atTop
      (𝓝 (ENNReal.ofReal ((1 - (p : ℝ)) / (p : ℝ)))) := by
  let r : ℝ := (1 - (p : ℝ)) / (p : ℝ)
  let q : ℝ := (1 + r) / 2
  let rho : ℝ := (p : ℝ) * q + (1 - (p : ℝ)) / q
  have hp0 : 0 < (p : ℝ) := by linarith
  have hr0 : 0 ≤ r := div_nonneg (unitInterval.one_sub_nonneg _) hp0.le
  have hr1 : r < 1 := by
    dsimp [r]
    exact (div_lt_one hp0).mpr (by linarith)
  have hqr : r < q := by dsimp [q]; linarith
  have hq0 : 0 < q := hr0.trans_lt hqr
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hodds : (p : ℝ) * r = 1 - (p : ℝ) := by dsimp [r]; field_simp
  have hrho0 : 0 ≤ rho := by
    dsimp [rho]
    exact add_nonneg (mul_nonneg p.property.1 hq0.le)
      (div_nonneg (unitInterval.one_sub_nonneg _) hq0.le)
  have hrho1 : rho < 1 := by
    have hfac : (q - 1) * ((p : ℝ) * q - (1 - (p : ℝ))) < 0 := by
      apply mul_neg_of_neg_of_pos (by linarith)
      rw [← hodds]
      exact sub_pos.mpr (mul_lt_mul_of_pos_left hqr hp0)
    have hid : (rho - 1) * q = (q - 1) * ((p : ℝ) * q - (1 - (p : ℝ))) := by
      dsimp [rho]
      field_simp
      ring
    nlinarith
  exact zero_probability_tendsto_of_parameters p hr0 hqr.le hq0 hrho0 hrho1 hodds rfl

end Freezing1.SIR.BiasedWalk
