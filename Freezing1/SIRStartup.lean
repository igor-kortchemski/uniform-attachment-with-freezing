module

public import Freezing1.SIRRelativeNoise
public import Freezing1.SIRStoppedCoupling
public import Freezing1.SIRStrongCounts
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Relative early slopes for genuine SIR populations

The relative error is controlled after any cutoff tending to infinity.
The probability estimates use the actual centered susceptible-chain noise;
no law of large numbers or startup estimate is assumed.
-/

@[expose] public section

namespace Freezing1.SIR.Susceptible

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def infectiousRatio (n : ℕ) (H : ℕ → ℕ) (k : ℕ) : ℝ :=
  (infectious n k H : ℝ) / k

@[fun_prop] theorem infectiousRatio_measurable (n k : ℕ) :
    Measurable (fun H : ℕ → ℕ => infectiousRatio n H k) := by
  unfold infectiousRatio infectious
  fun_prop

theorem infectious_noise_center (rate : ℝ≥0) (n k : ℕ) (H : ℕ → ℕ) (p : ℝ) :
    (infectious n k H : ℝ) - (2 * p - 1) * k =
      1 - 2 * noise rate n H k +
        2 * ∑ i ∈ Finset.range k, ((infectionProbability rate (H i) : ℝ) - p) := by
  unfold infectious noise
  push_cast
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem infectious_relative_drift_error (rate : ℝ≥0) (n k : ℕ) (H : ℕ → ℕ)
    (p a : ℝ) (hdrift : ∀ i < k, |(infectionProbability rate (H i) : ℝ) - p| ≤ a) :
    |(infectious n k H : ℝ) - (2 * p - 1) * k| ≤
      1 + 2 * |noise rate n H k| + 2 * k * a := by
  have hsum : |∑ i ∈ Finset.range k, ((infectionProbability rate (H i) : ℝ) - p)| ≤ k * a := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, |(infectionProbability rate (H i) : ℝ) - p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range k, a :=
        Finset.sum_le_sum fun i hi => hdrift i (Finset.mem_range.mp hi)
      _ = _ := by simp
  rw [infectious_noise_center rate n k H p, abs_le]
  constructor <;> nlinarith [le_abs_self (noise rate n H k), neg_abs_le (noise rate n H k),
    le_abs_self (∑ i ∈ Finset.range k, ((infectionProbability rate (H i) : ℝ) - p)),
    neg_abs_le (∑ i ∈ Finset.range k, ((infectionProbability rate (H i) : ℝ) - p))]

theorem infectionProbability_early_error (rate : ℝ≥0) {n : ℕ} {H : ℕ → ℕ}
    (hbounds : ∀ i, n - i ≤ H i ∧ H i ≤ n) (i : ℕ) (p : ℝ) :
    |(infectionProbability rate (H i) : ℝ) - p| ≤
      (rate : ℝ) * i + |(infectionProbability rate n : ℝ) - p| := by
  have hh := infectionProbability_abs_sub_le rate (hbounds i).2
  have hdiff : n - H i ≤ i := by have := (hbounds i).1; omega
  have hmul := mul_le_mul_of_nonneg_left
    (show ((n - H i : ℕ) : ℝ) ≤ i by exact_mod_cast hdiff) rate.coe_nonneg
  exact (abs_sub_le _ _ _).trans (add_le_add (hh.trans hmul) (le_refl _))

/-- A deterministic drift approximation and the proved relative-noise
bound together imply a relative startup estimate. -/
theorem relative_startup_of_drift (rate : ℕ → ℝ≥0) (cutoff : ℕ → ℕ)
    (hcutoff : Tendsto cutoff atTop atTop) (p : ℝ) (window : ℕ → ℕ → Prop)
    {eps : ℝ} (heps : 0 < eps)
    (hdrift : ∀ᶠ n in atTop, ∀ᵐ H ∂fullLaw (rate n) n,
      ∀ k, window n k → ∀ i < k,
        |(infectionProbability (rate n) (H i) : ℝ) - p| ≤ eps / 8) :
    Tendsto (fun n => fullLaw (rate n) n
      {H | ∃ k ≥ cutoff n, window n k ∧ eps ≤ |infectiousRatio n H k - (2 * p - 1)|})
      atTop (nhds 0) := by
  have hc : Tendsto (fun n => (cutoff n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcutoff
  have hbound : ∀ᶠ n in atTop, fullLaw (rate n) n
      {H | ∃ k ≥ cutoff n, window n k ∧ eps ≤ |infectiousRatio n H k - (2 * p - 1)|} ≤
      fullLaw (rate n) n {H | ∃ k ≥ cutoff n, (eps / 8) * (k : ℝ) ≤ |noise (rate n) n H k|} := by
    filter_upwards [hdrift, hc.eventually (eventually_gt_atTop (4 / eps))] with n hn hcn
    apply measure_mono_ae
    filter_upwards [hn] with H hH
    rintro ⟨k, hk, hwindow, hbad⟩
    refine ⟨k, hk, ?_⟩
    have hkR : (cutoff n : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := (div_pos (by norm_num) heps).trans (hcn.trans_le hkR)
    have hone : 1 < eps / 4 * k := by
      have hh : 4 / eps < (k : ℝ) := hcn.trans_le hkR
      have hh' := (div_lt_iff₀ heps).mp hh
      nlinarith
    have he : infectiousRatio n H k - (2 * p - 1) =
        ((infectious n k H : ℝ) - (2 * p - 1) * k) / k := by
      unfold infectiousRatio
      field_simp
    rw [he, abs_div, abs_of_pos hkpos] at hbad
    have hbad' := (le_div_iff₀ hkpos).mp hbad
    have hd := infectious_relative_drift_error (rate n) n k H p (eps / 8) (hH k hwindow)
    by_contra hnot
    have hsmall := lt_of_not_ge hnot
    nlinarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (noise_relative_tendsto rate cutoff hcutoff (by positivity : 0 < eps / 8))
    (Eventually.of_forall fun _ => bot_le) hbound

theorem infectionProbability_scaled_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ))) :
    Tendsto (fun n => (infectionProbability (rate n) n : ℝ)) atTop
      (nhds (infectionProbability lam 1 : ℝ)) := by
  have hh := infectionProbability_full_tendsto rate lam.coe_nonneg hscaled
  convert hh using 1
  rw [infectionProbability_coe]
  simp

theorem startupSlope_eq (lam : ℝ≥0) :
    2 * (infectionProbability lam 1 : ℝ) - 1 = ((lam : ℝ) - 1) / ((lam : ℝ) + 1) := by
  rw [infectionProbability_coe]
  simp only [Nat.cast_one, mul_one]
  field_simp
  ring

/-- For each desired error one sufficiently small early linear window
works, uniformly after any diverging cutoff. -/
theorem relative_startup_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta ∈ Ioc (0 : ℝ) delta0,
      Tendsto (fun n => fullLaw (rate n) n
        {H | ∃ k ≥ cutoff n, (k : ℝ) ≤ delta * n ∧
          eps ≤ |infectiousRatio n H k - ((lam : ℝ) - 1) / ((lam : ℝ) + 1)|})
        atTop (nhds 0) := by
  let delta0 : ℝ := eps / (16 * ((lam : ℝ) + 1))
  have hd0 : 0 < delta0 := by dsimp [delta0]; positivity
  refine ⟨delta0, hd0, ?_⟩
  intro delta hdelta
  rw [← startupSlope_eq]
  apply relative_startup_of_drift rate cutoff hcutoff _ _ heps
  have hp := infectionProbability_scaled_tendsto rate lam hscaled
  have hevent : ∀ᶠ n in atTop,
      |(infectionProbability (rate n) n : ℝ) - (infectionProbability lam 1 : ℝ)| < eps / 16 := by
    have hh := (Metric.tendsto_atTop.mp hp) (eps / 16) (by positivity)
    exact eventually_atTop.mpr ⟨hh.choose, fun n hn => by
      have hh' := hh.choose_spec n hn
      rw [Real.dist_eq] at hh'
      exact hh'⟩
  filter_upwards [hscaled.eventually (eventually_lt_nhds
      (show (lam : ℝ) < (lam : ℝ) + 1 by linarith)), hevent] with n hrate hp
  filter_upwards [fullLaw_bounds (rate n) n] with H hb
  intro k hk i hi
  have hiR : (i : ℝ) ≤ k := by exact_mod_cast hi.le
  have hmul := mul_le_mul_of_nonneg_left (hiR.trans hk) (rate n).coe_nonneg
  have hdle : delta * ((lam : ℝ) + 1) ≤ eps / 16 := by
    have hh := mul_le_mul_of_nonneg_right hdelta.2 (show 0 ≤ (lam : ℝ) + 1 by positivity)
    dsimp [delta0] at hh
    field_simp at hh
    nlinarith
  have hpressure := mul_lt_mul_of_pos_left hrate hdelta.1
  have hbound := infectionProbability_early_error (rate n) hb i (infectionProbability lam 1 : ℝ)
  nlinarith

/-- Under strong infection, the unstopped relative slope is uniformly one
up to every fixed fraction strictly below population time. -/
theorem relative_startup_strong_tendsto (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    {delta eps : ℝ} (hdelta : 0 < delta) (heps : 0 < eps) :
    Tendsto (fun n => fullLaw (rate n) n
      {H | ∃ k ≥ cutoff n, (k : ℝ) ≤ (1 - delta) * n ∧
        eps ≤ |infectiousRatio n H k - 1|}) atTop (nhds 0) := by
  have hcenter : 2 * (1 : ℝ) - 1 = 1 := by norm_num
  rw [← hcenter]
  apply relative_startup_of_drift rate cutoff hcutoff 1 _ heps
  let x : ℕ → ℝ := fun n => delta * ((n : ℝ) * rate n)
  have hx : Tendsto x atTop atTop := hstrong.const_mul_atTop hdelta
  have hq : Tendsto (fun n => 1 / (1 + x n)) atTop (nhds 0) := by
    convert tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_left atTop 1 hx) using 1
    funext n
    rw [Function.comp_apply, one_div]
  have hqevent : ∀ᶠ n in atTop, 1 / (1 + x n) < eps / 8 :=
    hq.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < eps / 8))
  filter_upwards [hqevent] with n hqn
  filter_upwards [fullLaw_bounds (rate n) n] with H hb
  intro k hk i hi
  have hiR : (i : ℝ) ≤ k := by exact_mod_cast hi.le
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hinR : (i : ℝ) ≤ n := by nlinarith
  have hin : i ≤ n := by exact_mod_cast hinR
  have huR : (n : ℝ) - i ≤ H i := by
    have hh : ((n - i : ℕ) : ℝ) ≤ H i := by exact_mod_cast (hb i).1
    rwa [Nat.cast_sub hin] at hh
  have hdeltaU : delta * (n : ℝ) ≤ H i := by nlinarith
  have hpressure : x n ≤ (rate n : ℝ) * H i := by
    have hh := mul_le_mul_of_nonneg_left hdeltaU (rate n).coe_nonneg
    dsimp [x]
    nlinarith
  rw [abs_of_nonpos (sub_nonpos.mpr (infectionProbability (rate n) (H i)).property.2)]
  have hcomp := infectionProbability_complement (rate n) (H i)
  have hrec : 1 / (1 + (rate n : ℝ) * H i) ≤ 1 / (1 + x n) := by
    apply one_div_le_one_div_of_le (by dsimp [x]; positivity)
    linarith
  linarith

end Freezing1.SIR.Susceptible

namespace Freezing1.SIR.StoppedCoupling

open MeasureTheory
open scoped Classical

set_option backward.isDefEq.respectTransparency false

theorem fullLaw_agree_at_alive (rate : NNReal) (n : ℕ) :
    ∀ᵐ H ∂fullLaw rate n, ∀ k, 0 < (H k).1.infectious →
      ((H k).1.infectious : ℤ) = Susceptible.infectious n k (fun j => (H j).2) := by
  filter_upwards [fullLaw_agree_until_extinction rate n, fullLaw_counts_legal rate n]
    with H hagree hlegal
  intro k hk
  apply (hagree k ?_).2
  intro j hj
  by_contra hn
  have hz : (H j).1.infectious = 0 := by omega
  have he := legalHistory_absorbed_persists hlegal hz k hj.le
  have : (H k).1.infectious = 0 := by rw [he]; exact hz
  omega

end Freezing1.SIR.StoppedCoupling

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- At each currently alive time the actual stopped count agrees with the
genuinely coupled auxiliary population. No survival premise is imposed on
the measure itself. -/
theorem countsFullLaw_alive_startup_event_le_unstopped (rate : ℝ≥0) (n L : ℕ)
    (window : ℕ → Prop) (center eps : ℝ) :
    countsFullLaw rate n {H | ∃ k ≥ L, window k ∧ 0 < (H k).infectious ∧
      eps ≤ |((H k).infectious : ℝ) / k - center|} ≤
    Susceptible.fullLaw rate n {H | ∃ k ≥ L, window k ∧
      eps ≤ |Susceptible.infectiousRatio n H k - center|} := by
  rw [← StoppedCoupling.map_fullLaw_counts, ← StoppedCoupling.map_fullLaw_unstopped,
    Measure.map_apply (by fun_prop) (by measurability),
    Measure.map_apply (by fun_prop) (by measurability)]
  apply measure_mono_ae
  filter_upwards [StoppedCoupling.fullLaw_agree_at_alive rate n] with H hagree
  rintro ⟨k, hk, hwindow, halive, hbad⟩
  refine ⟨k, hk, hwindow, ?_⟩
  have heR : ((H k).1.infectious : ℝ) =
      (Susceptible.infectious n k (fun j => (H j).2) : ℝ) := by
    exact_mod_cast hagree k halive
  unfold Susceptible.infectiousRatio
  rw [← heR]
  exact hbad

/-- The source's finite-parameter startup estimate, on every currently
alive time. A later-survival gate is consequently also covered. -/
theorem countsFullLaw_alive_relative_startup_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta ∈ Ioc (0 : ℝ) delta0,
      Tendsto (fun n => countsFullLaw (rate n) n
        {H | ∃ k ≥ cutoff n, (k : ℝ) ≤ delta * n ∧ 0 < (H k).infectious ∧
          eps ≤ |((H k).infectious : ℝ) / k - ((lam : ℝ) - 1) / ((lam : ℝ) + 1)|})
        atTop (nhds 0) := by
  obtain ⟨delta0, hd0, hstart⟩ :=
    Susceptible.relative_startup_tendsto rate lam hscaled cutoff hcutoff heps
  refine ⟨delta0, hd0, ?_⟩
  intro delta hd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hstart delta hd)
    (fun _ => bot_le) (fun n => countsFullLaw_alive_startup_event_le_unstopped
      (rate n) n (cutoff n) (fun k => (k : ℝ) ≤ delta * n) _ eps)

theorem countsFullLaw_strong_fraction_extinction_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    Tendsto (fun n => countsFullLaw (rate n) n
      {H | (H ⌊(1 - delta) * n⌋₊).infectious = 0}) atTop (nhds 0) := by
  have hpressure : Tendsto (fun n : ℕ => (rate n : ℝ) *
      (n - ⌊(1 - delta) * n⌋₊ : ℕ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ (hstrong.const_mul_atTop hd0)
    apply Eventually.of_forall
    intro n
    have hm : ⌊(1 - delta) * (n : ℝ)⌋₊ ≤ n := Nat.floor_le_of_le (by nlinarith)
    have hfloor := Nat.floor_le (mul_nonneg (sub_nonneg.mpr hd1) (Nat.cast_nonneg n))
    have hgap : delta * (n : ℝ) ≤ ((n - ⌊(1 - delta) * n⌋₊ : ℕ) : ℝ) := by
      rw [Nat.cast_sub hm]
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hgap (rate n).coe_nonneg
    nlinarith
  have hreal := countsFullLaw_early_absorption_tendsto_zero rate
    (fun n => ⌊(1 - delta) * n⌋₊) hpressure
  exact (ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top _ _)).mp hreal

/-- The actual stopped chain has relative slope one uniformly up to every
fixed fraction below time `n`, with early extinction included in the error. -/
theorem countsFullLaw_strong_relative_startup_tendsto (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    {delta eps : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) (heps : 0 < eps) :
    Tendsto (fun n => countsFullLaw (rate n) n
      {H | ∃ k ≥ cutoff n, (k : ℝ) ≤ (1 - delta) * n ∧
        eps ≤ |((H k).infectious : ℝ) / k - 1|}) atTop (nhds 0) := by
  have hbound (n : ℕ) : countsFullLaw (rate n) n
      {H | ∃ k ≥ cutoff n, (k : ℝ) ≤ (1 - delta) * n ∧
        eps ≤ |((H k).infectious : ℝ) / k - 1|} ≤
      Susceptible.fullLaw (rate n) n
        {H | ∃ k ≥ cutoff n, (k : ℝ) ≤ (1 - delta) * n ∧
          eps ≤ |Susceptible.infectiousRatio n H k - 1|} +
      countsFullLaw (rate n) n {H | (H ⌊(1 - delta) * n⌋₊).infectious = 0} := by
    have hsub : countsFullLaw (rate n) n
        {H | ∃ k ≥ cutoff n, (k : ℝ) ≤ (1 - delta) * n ∧
          eps ≤ |((H k).infectious : ℝ) / k - 1|} ≤
        countsFullLaw (rate n) n
          ({H | ∃ k ≥ cutoff n, (k : ℝ) ≤ (1 - delta) * n ∧ 0 < (H k).infectious ∧
            eps ≤ |((H k).infectious : ℝ) / k - 1|} ∪
          {H | (H ⌊(1 - delta) * n⌋₊).infectious = 0}) := by
      apply measure_mono_ae
      filter_upwards [countsFullLaw_legal (rate n) n] with H hl
      rintro ⟨k, hk, htime, hbad⟩
      by_cases hz : (H k).infectious = 0
      · right
        change (H ⌊(1 - delta) * (n : ℝ)⌋₊).infectious = 0
        have hkm : k ≤ ⌊(1 - delta) * (n : ℝ)⌋₊ :=
          (Nat.le_floor_iff (mul_nonneg (sub_nonneg.mpr hd1) (Nat.cast_nonneg n))).mpr htime
        rw [legalHistory_absorbed_persists hl hz _ hkm]
        exact hz
      · left
        exact ⟨k, hk, htime, by omega, hbad⟩
    exact hsub.trans ((measure_union_le _ _).trans (add_le_add
      (countsFullLaw_alive_startup_event_le_unstopped (rate n) n (cutoff n)
        (fun k => (k : ℝ) ≤ (1 - delta) * n) 1 eps) (le_refl _)))
  have hsum := (Susceptible.relative_startup_strong_tendsto rate hstrong cutoff hcutoff hd0 heps).add
    (countsFullLaw_strong_fraction_extinction_tendsto_zero rate hstrong hd0 hd1)
  simp only [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) hbound

/-- The relative strong-regime startup estimate extends all the way to
time `n`. The late half of the interval uses the proved triangular fluid
limit, while the early half retains relative-noise control. -/
theorem countsFullLaw_strong_relative_until_n_tendsto (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop) {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => countsFullLaw (rate n) n
      {H | ∃ k ≥ cutoff n, k ≤ n ∧ eps ≤ |((H k).infectious : ℝ) / k - 1|})
      atTop (nhds 0) := by
  have hgrid : Tendsto (fun n => countsFullLaw (rate n) n
      {H | ∃ k ≤ 2 * n, (eps / 2) * n ≤
        |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|}) atTop (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top _ _)).mp
      (countsFullLaw_triangle_tendsto_zero rate hstrong (by positivity : 0 < eps / 2))
  have hbound (n : ℕ) : countsFullLaw (rate n) n
      {H | ∃ k ≥ cutoff n, k ≤ n ∧ eps ≤ |((H k).infectious : ℝ) / k - 1|} ≤
      countsFullLaw (rate n) n
        {H | ∃ k ≥ cutoff n, (k : ℝ) ≤ (1 - (1 / 2 : ℝ)) * n ∧
          eps ≤ |((H k).infectious : ℝ) / k - 1|} +
      countsFullLaw (rate n) n
        {H | ∃ k ≤ 2 * n, (eps / 2) * n ≤
          |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|} := by
    apply le_trans ?_ (measure_union_le _ _)
    apply measure_mono
    rintro H ⟨k, hk, hkn, hbad⟩
    by_cases hearly : (k : ℝ) ≤ (1 - (1 / 2 : ℝ)) * n
    · left
      exact ⟨k, hk, hearly, hbad⟩
    · right
      refine ⟨k, by omega, ?_⟩
      have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hkpos : (0 : ℝ) < k := by linarith
      have hmin : min k (2 * n - k) = k := Nat.min_eq_left (by omega)
      rw [hmin]
      have he : ((H k).infectious : ℝ) / k - 1 =
          (((H k).infectious : ℝ) - k) / k := by field_simp
      rw [he, abs_div, abs_of_pos hkpos] at hbad
      have hbad' := (le_div_iff₀ hkpos).mp hbad
      have hlate : (n : ℝ) / 2 < k := by linarith
      nlinarith
  have hearly := countsFullLaw_strong_relative_startup_tendsto rate hstrong cutoff hcutoff
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) heps
  have hsum := hearly.add hgrid
  simp only [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) hbound

/-- Rounding upwards gives exactly the paper's real lower bound on an
integer observation time. -/
noncomputable def logLogStartupCutoff (n : ℕ) : ℕ := ⌈Real.log (Real.log (n : ℝ))⌉₊

theorem logLogStartupCutoff_le (n k : ℕ) :
    logLogStartupCutoff n ≤ k ↔ Real.log (Real.log (n : ℝ)) ≤ (k : ℝ) := Nat.ceil_le

theorem logLogStartupCutoff_tendsto : Tendsto logLogStartupCutoff atTop atTop :=
  tendsto_nat_ceil_atTop.comp
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

theorem countsFullLaw_alive_logLog_startup_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta ∈ Ioc (0 : ℝ) delta0,
      Tendsto (fun n => countsFullLaw (rate n) n
        {H | ∃ k : ℕ, Real.log (Real.log (n : ℝ)) ≤ (k : ℝ) ∧ (k : ℝ) ≤ delta * n ∧
          0 < (H k).infectious ∧ eps ≤
            |((H k).infectious : ℝ) / k - ((lam : ℝ) - 1) / ((lam : ℝ) + 1)|})
        atTop (nhds 0) := by
  simpa only [ge_iff_le, logLogStartupCutoff_le] using
    countsFullLaw_alive_relative_startup_tendsto rate lam hscaled
      logLogStartupCutoff logLogStartupCutoff_tendsto heps

theorem countsFullLaw_strong_logLog_until_n_tendsto (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => countsFullLaw (rate n) n
      {H | ∃ k : ℕ, Real.log (Real.log (n : ℝ)) ≤ (k : ℝ) ∧ k ≤ n ∧
        eps ≤ |((H k).infectious : ℝ) / k - 1|}) atTop (nhds 0) := by
  simpa only [ge_iff_le, logLogStartupCutoff_le] using
    countsFullLaw_strong_relative_until_n_tendsto rate hstrong
      logLogStartupCutoff logLogStartupCutoff_tendsto heps

end Freezing1.SIR
