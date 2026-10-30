module

public import Freezing1.SIRPathSpace
public import Freezing1.SIRStoppedFluidTransfer
public import Freezing1.SIREarlyExtinction
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The embedded SIR weak fluid path-law mixture

The genuine stopped path measures converge for the topology of uniform
convergence on compact time intervals. One actual early-survival indicator
controls the entire path, and its weight is derived from the stopped law.
The independent continuous-time epidemic identification remains separate.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology UniformConvergence BoundedContinuousFunction

set_option backward.isDefEq.respectTransparency false

noncomputable def coupledPopulationPath (n : ℕ) (H : ℕ → StoppedCoupling.State) : PopulationPath :=
  scaledPopulationPath n (fun k => (H k).1)

theorem measurable_coupledPopulationPath (n : ℕ) : Measurable (coupledPopulationPath n) :=
  (measurable_scaledPopulationPath n).comp
    (measurable_pi_iff.mpr fun k => measurable_fst.comp (measurable_pi_apply k))

theorem coupledPopulationPath_ae (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂StoppedCoupling.fullLaw rate n, ∀ t : ℝ≥0,
      UniformOnFun.toFun timeWindows (coupledPopulationPath n H) t =
        (((H ⌊(n : ℝ) * (t : ℝ)⌋₊).1.infectious : ℝ) / n) := by
  have hh := scaledPopulationPath_ae rate n
  rw [← StoppedCoupling.map_fullLaw_counts rate n] at hh
  exact ae_of_ae_map (show Measurable (fun H : ℕ → StoppedCoupling.State => fun k => (H k).1) from
    measurable_pi_iff.mpr fun k => measurable_fst.comp (measurable_pi_apply k)).aemeasurable hh

theorem integral_populationPathLaw_joint (rate : ℝ≥0) (n : ℕ) (F : PopulationPath →ᵇ ℝ) :
    (∫ f, F f ∂(populationPathLaw rate n : Measure PopulationPath)) =
      ∫ H, F (coupledPopulationPath n H) ∂StoppedCoupling.fullLaw rate n := by
  change (∫ f, F f ∂(countsFullLaw rate n).map (scaledPopulationPath n)) = _
  rw [integral_map (measurable_scaledPopulationPath n).aemeasurable
    F.continuous.measurable.aestronglyMeasurable]
  rw [← StoppedCoupling.map_fullLaw_counts rate n]
  have hm : Measurable (fun H : ℕ → StoppedCoupling.State => fun k => (H k).1) :=
    measurable_pi_iff.mpr fun k => measurable_fst.comp (measurable_pi_apply k)
  have hF : AEStronglyMeasurable (fun H : ℕ → Counts => F (scaledPopulationPath n H))
      ((StoppedCoupling.fullLaw rate n).map (fun H k => (H k).1)) :=
    (show Measurable (fun H : ℕ → Counts => F (scaledPopulationPath n H)) from
      F.continuous.measurable.comp (measurable_scaledPopulationPath n)).aestronglyMeasurable
  exact integral_map hm.aemeasurable hF

theorem integral_fluidMixtureLaw (lam : ℝ≥0) (F : PopulationPath →ᵇ ℝ) :
    (∫ f, F f ∂(fluidMixtureLaw lam : Measure PopulationPath)) =
      (sirSurvivalParameter lam : ℝ) * (F (positiveProfilePath lam) - F zeroPopulationPath) +
        F zeroPopulationPath := by
  change (∫ f, F f ∂(bernoulliMeasure true false (sirSurvivalParameter lam)).map
    (fun b : Bool => if b then positiveProfilePath lam else zeroPopulationPath)) = _
  rw [integral_map (measurable_of_countable _).aemeasurable
    F.continuous.measurable.aestronglyMeasurable, integral_bernoulliMeasure]
  change (sirSurvivalParameter lam : ℝ) * F (positiveProfilePath lam) +
    (1 - (sirSurvivalParameter lam : ℝ)) * F zeroPopulationPath = _
  ring

theorem joint_gate_probability_eq (rate : ℝ≥0) (n a : ℕ) :
    (StoppedCoupling.fullLaw rate n).real {H | 0 < (H a).1.infectious} =
      (countsFullLaw rate n).real {H | 0 < (H a).infectious} := by
  unfold Measure.real
  congr 1
  rw [← StoppedCoupling.map_fullLaw_counts rate n]
  have hm : Measurable (fun H : ℕ → StoppedCoupling.State => fun k => (H k).1) :=
    measurable_pi_iff.mpr fun k => measurable_fst.comp (measurable_pi_apply k)
  rw [Measure.map_apply hm (by measurability)]
  rfl

/-- A bounded test-function comparison, paying for one measurable bad event. -/
theorem integral_test_bad_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) (s : Set Ω) (hs : MeasurableSet s)
    {e C : ℝ} (he : 0 ≤ e)
    (hbound : ∀ᵐ x ∂μ, |X x - Y x| ≤ C)
    (hgood : ∀ᵐ x ∂μ, x ∉ s → |X x - Y x| ≤ e) :
    |(∫ x, X x ∂μ) - ∫ x, Y x ∂μ| ≤ e + C * μ.real s := by
  let g : Ω → ℝ := fun x => e + s.indicator (fun _ => C) x
  have hg : Integrable g μ := (integrable_const e).add ((integrable_const C).indicator hs)
  have hh : ∀ᵐ x ∂μ, ‖X x - Y x‖ ≤ g x := by
    filter_upwards [hbound, hgood] with x hb hG
    dsimp [g]
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]
      linarith
    · rw [indicator_of_notMem hx]
      simpa only [add_zero] using hG hx
  have h := norm_integral_le_of_norm_le hg hh
  rw [integral_sub hX hY, Real.norm_eq_abs] at h
  have hgint : (∫ x, g x ∂μ) = e + C * μ.real s := by
    change (∫ x, e + s.indicator (fun _ => C) x ∂μ) = _
    rw [integral_add (integrable_const e) ((integrable_const C).indicator hs),
      integral_indicator_const C hs]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  exact h.trans_eq hgint

/-- Continuity at the two fixed candidate paths needs only one common
compact window and one positive path tolerance. -/
theorem test_two_path_control (F : PopulationPath →ᵇ ℝ) (lam : ℝ≥0) {e : ℝ} (he : 0 < e) :
    ∃ m : ℕ, ∃ eta : ℝ, 0 < eta ∧ ∀ (f : PopulationPath) (b : Bool),
      (∀ t ∈ timeWindow m, |UniformOnFun.toFun timeWindows f t -
        (if b then max (infectiousProfile lam (t : ℝ)) 0 else 0)| < eta) →
      |F f - (if b then F (positiveProfilePath lam) else F zeroPopulationPath)| < e := by
  have hU (f : PopulationPath) : {g : PopulationPath | |F g - F f| < e} ∈ 𝓝 f := by
    have hh := F.continuous.continuousAt (Metric.ball_mem_nhds (F f) he)
    change {g : PopulationPath | dist (F g) (F f) < e} ∈ 𝓝 f at hh
    simpa only [Real.dist_eq] using hh
  obtain ⟨m0, e0, he0, h0⟩ := populationPath_nhds_control zeroPopulationPath (hU _)
  obtain ⟨m1, e1, he1, h1⟩ := populationPath_nhds_control (positiveProfilePath lam) (hU _)
  refine ⟨max m0 m1, min e0 e1, lt_min he0 he1, ?_⟩
  intro f b hf
  cases b
  · apply h0
    intro t ht
    exact (hf t (timeWindow_mono (le_max_left _ _) ht)).trans_le (min_le_left _ _)
  · apply h1
    intro t ht
    exact (hf t (timeWindow_mono (le_max_right _ _) ht)).trans_le (min_le_right _ _)

noncomputable def gatedTestValue (F : PopulationPath →ᵇ ℝ) (lam : ℝ≥0) (a : ℕ)
    (H : ℕ → StoppedCoupling.State) : ℝ :=
  if 0 < (H a).1.infectious then F (positiveProfilePath lam) else F zeroPopulationPath

theorem measurable_gatedTestValue (F : PopulationPath →ᵇ ℝ) (lam : ℝ≥0) (a : ℕ) :
    Measurable (gatedTestValue F lam a) :=
  (measurable_of_countable (fun z : StoppedCoupling.State =>
    if 0 < z.1.infectious then F (positiveProfilePath lam) else F zeroPopulationPath)).comp
      (measurable_pi_apply a)

theorem integral_gatedTestValue (rate : ℝ≥0) (n : ℕ) (F : PopulationPath →ᵇ ℝ)
    (lam : ℝ≥0) (a : ℕ) :
    (∫ H, gatedTestValue F lam a H ∂StoppedCoupling.fullLaw rate n) =
      (StoppedCoupling.fullLaw rate n).real {H | 0 < (H a).1.infectious} *
        (F (positiveProfilePath lam) - F zeroPopulationPath) + F zeroPopulationPath := by
  let s : Set (ℕ → StoppedCoupling.State) := {H | 0 < (H a).1.infectious}
  have hs : MeasurableSet s :=
    (Set.to_countable {z : StoppedCoupling.State | 0 < z.1.infectious}).measurableSet.preimage
      (measurable_pi_apply a)
  have he : gatedTestValue F lam a = fun H =>
      s.indicator (fun _ => F (positiveProfilePath lam) - F zeroPopulationPath) H +
        F zeroPopulationPath := by
    funext H
    by_cases hH : 0 < (H a).1.infectious
    · have hsH : H ∈ s := hH
      simp only [gatedTestValue, ite_eq_left hH, indicator_of_mem hsH]
      ring
    · have hsH : H ∉ s := hH
      simp only [gatedTestValue, ite_eq_right hH, indicator_of_notMem hsH, zero_add]
  rw [he, integral_add ((integrable_const _).indicator hs) (integrable_const _),
    integral_indicator_const _ hs]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rfl

theorem gated_test_integral_error_le (rate : ℝ≥0) (n : ℕ) (F : PopulationPath →ᵇ ℝ)
    (lam : ℝ≥0) (delta : ℝ) {e eta : ℝ} (he : 0 ≤ e) (m : ℕ)
    (hcontrol : ∀ (f : PopulationPath) (b : Bool),
      (∀ t ∈ timeWindow m, |UniformOnFun.toFun timeWindows f t -
        (if b then max (infectiousProfile lam (t : ℝ)) 0 else 0)| < eta) →
      |F f - (if b then F (positiveProfilePath lam) else F zeroPopulationPath)| < e) :
    |(∫ f, F f ∂(populationPathLaw rate n : Measure PopulationPath)) -
      ∫ H, gatedTestValue F lam ⌊delta * n⌋₊ H ∂StoppedCoupling.fullLaw rate n| ≤
      e + 2 * ‖F‖ * (StoppedCoupling.fullLaw rate n).real
        {H | ∃ t ∈ Icc (0 : ℝ) (m : ℝ),
          eta ≤ |((H ⌊(n : ℝ) * t⌋₊).1.infectious : ℝ) / n -
            (if 0 < (H ⌊delta * n⌋₊).1.infectious then max (infectiousProfile lam t) 0 else 0)|} := by
  rw [integral_populationPathLaw_joint]
  have hX : Integrable (fun H => F (coupledPopulationPath n H)) (StoppedCoupling.fullLaw rate n) :=
    (integrable_const ‖F‖).mono'
      ((F.continuous.measurable.comp (measurable_coupledPopulationPath n)).aestronglyMeasurable)
      (Eventually.of_forall fun H => F.norm_coe_le_norm _)
  have hY : Integrable (gatedTestValue F lam ⌊delta * n⌋₊) (StoppedCoupling.fullLaw rate n) := by
    apply (integrable_const ‖F‖).mono'
      (measurable_gatedTestValue F lam ⌊delta * n⌋₊).aestronglyMeasurable
    apply Eventually.of_forall
    intro H
    unfold gatedTestValue
    split_ifs <;> exact F.norm_coe_le_norm _
  apply integral_test_bad_event_bound (StoppedCoupling.fullLaw rate n) hX hY _
    (StoppedCoupling.measurableSet_gated_real_error lam eta delta n m) he
  · apply Eventually.of_forall
    intro H
    have hx := F.norm_coe_le_norm (coupledPopulationPath n H)
    have hy : |gatedTestValue F lam ⌊delta * n⌋₊ H| ≤ ‖F‖ := by
      unfold gatedTestValue
      split_ifs <;> exact F.norm_coe_le_norm _
    have hh := abs_sub (F (coupledPopulationPath n H)) (gatedTestValue F lam ⌊delta * n⌋₊ H)
    simp only [Real.norm_eq_abs] at hx
    linarith
  · filter_upwards [coupledPopulationPath_ae rate n] with H hH
    intro hgood
    simp only [not_exists, not_and, not_le] at hgood
    by_cases hgate : 0 < (H ⌊delta * n⌋₊).1.infectious
    · have hh := hcontrol (coupledPopulationPath n H) true (by
        intro t ht
        rw [hH t]
        have htR : (t : ℝ) ∈ Icc (0 : ℝ) (m : ℝ) :=
          ⟨t.coe_nonneg, by exact_mod_cast ht.2⟩
        simpa only [ite_eq_left hgate, ite_true] using hgood (t : ℝ) htR)
      simpa only [gatedTestValue, ite_eq_left hgate, ite_true] using hh.le
    · have hh := hcontrol (coupledPopulationPath n H) false (by
        intro t ht
        rw [hH t]
        have htR : (t : ℝ) ∈ Icc (0 : ℝ) (m : ℝ) :=
          ⟨t.coe_nonneg, by exact_mod_cast ht.2⟩
        simpa only [ite_eq_right hgate, Bool.false_eq_true, ite_false] using hgood (t : ℝ) htR)
      simpa only [gatedTestValue, ite_eq_right hgate, Bool.false_eq_true, ite_false] using hh.le

/-- The actual embedded stopped path laws converge in the topology of
uniform convergence on compact time intervals to the derived two-path
mixture. The survival probability is a conclusion of the construction. -/
theorem embedded_sir_fluid_mixture_limit (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ))) :
    Tendsto (fun n : ℕ => populationPathLaw (rate n) n) atTop (𝓝 (fluidMixtureLaw lam)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  let C : ℝ := 2 * ‖F‖
  let tol : ℝ := eps / (4 * (C + 1))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have htol : 0 < tol := by dsimp [tol]; positivity
  have hbudget : C * tol ≤ eps / 4 := by
    have he : (C + 1) * tol = eps / 4 := by
      dsimp [tol]
      field_simp
    nlinarith
  have hl0 : 0 < (lam : ℝ) := by linarith
  obtain ⟨m, eta, heta, hcontrol⟩ := test_two_path_control F lam (by positivity : 0 < eps / 4)
  have hfluid := StoppedCoupling.gated_stopped_real_fluid_two_stage rate hl0 hscaled m heta
  have hgate := countsFullLaw_early_survival_eventually rate lam hlam hscaled htol
  obtain ⟨delta, hdeltafluid, hdeltagate⟩ := (hfluid.and hgate).exists
  have hbad : Tendsto (fun n : ℕ => (StoppedCoupling.fullLaw (rate n) n).real
      {H | ∃ t ∈ Icc (0 : ℝ) (m : ℝ), eta ≤
        |((H ⌊(n : ℝ) * t⌋₊).1.infectious : ℝ) / n -
          (if 0 < (H ⌊delta * n⌋₊).1.infectious then max (infectiousProfile lam t) 0 else 0)|})
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Measure.real, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hdeltafluid
  filter_upwards [hbad.eventually (Iio_mem_nhds htol), hdeltagate] with n hn hg
  rw [Real.dist_eq]
  have hcompare := gated_test_integral_error_le (rate n) n F lam delta
    (by positivity : 0 ≤ eps / 4) m hcontrol
  have hcompare' :
      |(∫ f, F f ∂(populationPathLaw (rate n) n : Measure PopulationPath)) -
        ∫ H, gatedTestValue F lam ⌊delta * n⌋₊ H ∂StoppedCoupling.fullLaw (rate n) n| ≤
      eps / 4 + C * tol := by
    apply hcompare.trans
    dsimp only [C]
    have hh := mul_le_mul_of_nonneg_left hn.le (show 0 ≤ 2 * ‖F‖ by positivity)
    linarith
  have hq : |(StoppedCoupling.fullLaw (rate n) n).real
      {H | 0 < (H ⌊delta * n⌋₊).1.infectious} - (sirSurvivalParameter lam : ℝ)| < tol := by
    rw [joint_gate_probability_eq, sirSurvivalParameter_coe hlam]
    exact hg
  have hv : |F (positiveProfilePath lam) - F zeroPopulationPath| ≤ C := by
    have hh := abs_sub (F (positiveProfilePath lam)) (F zeroPopulationPath)
    have h1 := F.norm_coe_le_norm (positiveProfilePath lam)
    have h0 := F.norm_coe_le_norm zeroPopulationPath
    dsimp only [C]
    simp only [Real.norm_eq_abs] at h1 h0
    linarith
  have hmix : |(∫ H, gatedTestValue F lam ⌊delta * n⌋₊ H ∂StoppedCoupling.fullLaw (rate n) n) -
      ∫ f, F f ∂(fluidMixtureLaw lam : Measure PopulationPath)| ≤ C * tol := by
    rw [integral_gatedTestValue, integral_fluidMixtureLaw]
    have he :
        (StoppedCoupling.fullLaw (rate n) n).real {H | 0 < (H ⌊delta * n⌋₊).1.infectious} *
            (F (positiveProfilePath lam) - F zeroPopulationPath) + F zeroPopulationPath -
          ((sirSurvivalParameter lam : ℝ) * (F (positiveProfilePath lam) - F zeroPopulationPath) +
            F zeroPopulationPath) =
        ((StoppedCoupling.fullLaw (rate n) n).real {H | 0 < (H ⌊delta * n⌋₊).1.infectious} -
          (sirSurvivalParameter lam : ℝ)) * (F (positiveProfilePath lam) - F zeroPopulationPath) := by ring
    rw [he, abs_mul]
    exact (mul_le_mul hq.le hv (abs_nonneg _) htol.le).trans_eq (mul_comm tol C)
  have hh := abs_sub_le
    (∫ f, F f ∂(populationPathLaw (rate n) n : Measure PopulationPath))
    (∫ H, gatedTestValue F lam ⌊delta * n⌋₊ H ∂StoppedCoupling.fullLaw (rate n) n)
    (∫ f, F f ∂(fluidMixtureLaw lam : Measure PopulationPath))
  linarith

/-- The same weak path-law limit with the source's literal asymptotic ratio. -/
theorem embedded_sir_fluid_mixture_limit_of_source_ratio (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => populationPathLaw (rate n) n) atTop (𝓝 (fluidMixtureLaw lam)) := by
  apply embedded_sir_fluid_mixture_limit rate lam hlam
  have hh := hratio.mul_const (lam : ℝ)
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hl0 : (lam : ℝ) ≠ 0 := by linarith
  field_simp

end Freezing1.SIR
