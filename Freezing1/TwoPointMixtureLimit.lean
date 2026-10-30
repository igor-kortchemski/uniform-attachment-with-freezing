module

public import Freezing1.MainSIRFluidMixture

/-!
# A shared Bernoulli gate and a scalar two-point weak limit

Joint concentration is imposed on the actual joint law of the gate and the
observation. Separate marginal limits are not used to create a coupling.
-/

@[expose] public section

namespace Freezing1.TwoPointMixture

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology BoundedContinuousFunction

set_option backward.isDefEq.respectTransparency false

def gatedValue (c : ℝ) (z : Bool × ℝ) : ℝ := if z.1 then c else 0

theorem measurable_gatedValue (c : ℝ) : Measurable (gatedValue c) :=
  (measurable_of_countable (fun b : Bool => if b then c else 0)).comp measurable_fst

noncomputable def law (p : unitInterval) (c : ℝ) : ProbabilityMeasure ℝ :=
  ⟨bernoulliMeasure c 0 p, inferInstance⟩

theorem integral_law (p : unitInterval) (c : ℝ) (F : ℝ →ᵇ ℝ) :
    (∫ x, F x ∂(law p c : Measure ℝ)) = (p : ℝ) * (F c - F 0) + F 0 := by
  change (∫ x, F x ∂bernoulliMeasure c 0 p) = _
  rw [integral_bernoulliMeasure]
  simp only [smul_eq_mul]
  ring

theorem integral_gated_test (mu : Measure (Bool × ℝ)) [IsProbabilityMeasure mu]
    (c : ℝ) (F : ℝ →ᵇ ℝ) :
    (∫ z, F (gatedValue c z) ∂mu) =
      mu.real {z | z.1 = true} * (F c - F 0) + F 0 := by
  let G : Set (Bool × ℝ) := {z | z.1 = true}
  have hG : MeasurableSet G := by measurability
  have he : (fun z => F (gatedValue c z)) =
      fun z => G.indicator (fun _ => F c - F 0) z + F 0 := by
    funext z
    rcases z with ⟨b, x⟩
    cases b <;> simp [gatedValue, G]
  rw [he, integral_add ((integrable_const _).indicator hG) (integrable_const _),
    integral_indicator_const _ hG]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

theorem test_control (F : ℝ →ᵇ ℝ) (c : ℝ) {e : ℝ} (he : 0 < e) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ z : Bool × ℝ,
      |z.2 - gatedValue c z| < delta → |F z.2 - F (gatedValue c z)| < e := by
  obtain ⟨d0, hd0, h0⟩ := Metric.continuousAt_iff.mp
    (F.continuous.continuousAt : ContinuousAt F 0) e he
  obtain ⟨d1, hd1, h1⟩ := Metric.continuousAt_iff.mp
    (F.continuous.continuousAt : ContinuousAt F c) e he
  refine ⟨min d0 d1, lt_min hd0 hd1, ?_⟩
  rintro ⟨b, x⟩ hx
  cases b
  · have hx' : dist x 0 < d0 := by
      simpa only [Real.dist_eq, gatedValue, Bool.false_eq_true, ite_false] using
        hx.trans_le (min_le_left _ _)
    simpa only [Real.dist_eq, gatedValue, Bool.false_eq_true, ite_false] using h0 hx'
  · have hx' : dist x c < d1 := by
      simpa only [Real.dist_eq, gatedValue, ite_true] using
        hx.trans_le (min_le_right _ _)
    simpa only [Real.dist_eq, gatedValue, ite_true] using h1 hx'

theorem integral_error_bound (mu : Measure (Bool × ℝ)) [IsProbabilityMeasure mu]
    (c : ℝ) (F : ℝ →ᵇ ℝ) {e delta : ℝ} (he : 0 ≤ e)
    (hcontrol : ∀ z : Bool × ℝ, |z.2 - gatedValue c z| < delta →
      |F z.2 - F (gatedValue c z)| < e) :
    |(∫ z, F z.2 ∂mu) - ∫ z, F (gatedValue c z) ∂mu| ≤
      e + 2 * ‖F‖ * mu.real {z | delta ≤ |z.2 - gatedValue c z|} := by
  have hX : Integrable (fun z : Bool × ℝ => F z.2) mu :=
    (integrable_const ‖F‖).mono'
      (F.continuous.measurable.comp measurable_snd).aestronglyMeasurable
      (Eventually.of_forall fun z => F.norm_coe_le_norm _)
  have hY : Integrable (fun z => F (gatedValue c z)) mu :=
    (integrable_const ‖F‖).mono'
      (F.continuous.measurable.comp (measurable_gatedValue c)).aestronglyMeasurable
      (Eventually.of_forall fun z => F.norm_coe_le_norm _)
  have herror : Measurable (fun z : Bool × ℝ => |z.2 - gatedValue c z|) := by
    simpa only [Real.norm_eq_abs, Function.comp_def, Pi.sub_apply] using
      continuous_norm.measurable.comp (measurable_snd.sub (measurable_gatedValue c))
  apply SIR.integral_test_bad_event_bound mu hX hY _
    (measurableSet_le measurable_const herror) he
  · apply Eventually.of_forall
    intro z
    have h1 := F.norm_coe_le_norm z.2
    have h2 := F.norm_coe_le_norm (gatedValue c z)
    have hh := abs_sub (F z.2) (F (gatedValue c z))
    simp only [Real.norm_eq_abs] at h1 h2
    linarith
  · exact Eventually.of_forall fun z hz => (hcontrol z (lt_of_not_ge hz)).le

/-- Joint concentration around a shared Boolean gate and convergence of
that gate's probability imply the corresponding scalar weak limit. -/
theorem marginal_tendsto (nu : ℕ → ProbabilityMeasure (Bool × ℝ))
    (p : unitInterval) (c : ℝ)
    (hgate : Tendsto (fun n => (nu n : Measure (Bool × ℝ)).real {z | z.1 = true})
      atTop (𝓝 (p : ℝ)))
    (hconcentration : ∀ eps > 0, Tendsto (fun n =>
      (nu n : Measure (Bool × ℝ)).real {z | eps ≤ |z.2 - gatedValue c z|}) atTop (𝓝 0)) :
    Tendsto (fun n => (nu n).map Prod.snd) atTop (𝓝 (law p c)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  have htarget : Tendsto (fun n => ∫ z, F (gatedValue c z) ∂(nu n : Measure (Bool × ℝ)))
      atTop (𝓝 (∫ x, F x ∂(law p c : Measure ℝ))) := by
    simp_rw [integral_gated_test, integral_law]
    exact (hgate.mul_const (F c - F 0)).add_const (F 0)
  have herr : Tendsto (fun n =>
      (∫ z, F z.2 ∂(nu n : Measure (Bool × ℝ))) -
        ∫ z, F (gatedValue c z) ∂(nu n : Measure (Bool × ℝ))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    obtain ⟨delta, hd, hcontrol⟩ := test_control F c (half_pos heps)
    have hb := (hconcentration delta hd).const_mul (2 * ‖F‖)
    simp only [mul_zero] at hb
    filter_upwards [hb.eventually (Iio_mem_nhds (half_pos heps))] with n hn
    rw [Real.dist_eq, sub_zero]
    exact (integral_error_bound _ c F (half_pos heps).le hcontrol).trans_lt (by linarith)
  have hh := herr.add htarget
  simp only [zero_add] at hh
  convert hh using 1
  funext n
  change (∫ x, F x ∂(nu n : Measure (Bool × ℝ)).map Prod.snd) = _
  rw [integral_map measurable_snd.aemeasurable F.continuous.measurable.aestronglyMeasurable]
  ring

end Freezing1.TwoPointMixture
