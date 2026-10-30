module

public import Freezing1.IidScheduleDrift
public import Freezing1.BernoulliConcentration
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Uniform control of the entire auxiliary iid walk above the half-slope
line as its negative-step probability tends to zero. This does not assert
a coupling with an epidemic read backwards from extinction. -/

@[expose] public section

namespace Freezing1.ForwardAnnealed.HalfSlope

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal Classical

noncomputable def failures (i : ℕ) (x : SignSequence) : ℝ :=
  if x (i + 1) then 0 else 1

theorem measurable_failures (i : ℕ) : Measurable (failures i) :=
  (measurable_of_countable (fun b : Bool => if b then (0 : ℝ) else 1)).comp
    (measurable_pi_apply (i + 1))

theorem failures_independent (p : unitInterval) : iIndepFun failures (iidSignLaw p) :=
  ((iidSignLaw_independent p).precomp Nat.succ_injective).comp
    (fun _ b => if b then (0 : ℝ) else 1) (fun _ => measurable_of_countable _)

theorem failures_hasLaw (p : unitInterval) (i : ℕ) :
    HasLaw (failures i) (bernoulliMeasure (1 : ℝ) 0 (unitInterval.symm p)) (iidSignLaw p) := by
  have hm : (signLaw p).map (fun b : Bool => if b then (0 : ℝ) else 1) =
      bernoulliMeasure (1 : ℝ) 0 (unitInterval.symm p) := by
    rw [signLaw, map_bernoulliMeasure' true false (measurable_of_countable _) p]
    simp [bernoulliMeasure_def, add_comm]
  rw [← hm]
  exact (hasLaw_map (X := fun b : Bool => if b then (0 : ℝ) else 1)
    (measurable_of_countable _).aemeasurable).comp
    (iidSignLaw_coordinate p (i + 1))

theorem signed_sum_eq (x : SignSequence) (n : ℕ) :
    (∑ i ∈ Finset.range n, if x (i + 1) then (1 : ℝ) else -1) =
      (n : ℝ) - 2 * ∑ i ∈ Finset.range n, failures i x := by
  calc
    _ = ∑ i ∈ Finset.range n, (1 - 2 * failures i x) := by
      apply Finset.sum_congr rfl
      intro i _
      cases hx : x (i + 1) <;> norm_num [failures, hx]
    _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, ← Finset.mul_sum]

def good : Set SignSequence := {x | ∀ n : ℕ,
  (n : ℝ) / 2 ≤ ∑ i ∈ Finset.range n, if x (i + 1) then (1 : ℝ) else -1}

theorem measurableSet_good : MeasurableSet good := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.forall
  intro n
  apply measurableSet_setOfPred.mp
  exact measurableSet_le measurable_const (Finset.measurable_sum _ (fun i _ =>
    (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else -1)).comp
      (measurable_pi_apply (i + 1))))

theorem failure_tail (p : unitInterval) {θ : ℝ} (hθ : 0 < θ)
    (hp : (1 - (p : ℝ)) * (Real.exp θ - 1) ≤ θ / 8) (n : ℕ) :
    (iidSignLaw p).real {x | (n : ℝ) / 2 >
      ∑ i ∈ Finset.range n, if x (i + 1) then (1 : ℝ) else -1} ≤
      Real.exp (-θ / 8 * n) := by
  have he : {x : SignSequence | (n : ℝ) / 2 >
      ∑ i ∈ Finset.range n, if x (i + 1) then (1 : ℝ) else -1} =
      {x | (n : ℝ) / 4 < ∑ i ∈ Finset.range n, failures i x} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [signed_sum_eq]
    constructor <;> intro h <;> linarith
  rw [he]
  have hind := failures_independent p
  have hint : Integrable (fun x => Real.exp (θ * (∑ i ∈ Finset.range n, failures i) x))
      (iidSignLaw p) := hind.integrable_exp_mul_sum measurable_failures
        (fun i _ => integrable_exp_mul_bernoulli (failures_hasLaw p i) θ)
  calc
    _ ≤ (iidSignLaw p).real {x | (n : ℝ) / 4 ≤ (∑ i ∈ Finset.range n, failures i) x} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro x hx
      change (n : ℝ) / 4 < ∑ i ∈ Finset.range n, failures i x at hx
      change (n : ℝ) / 4 ≤ (∑ i ∈ Finset.range n, failures i) x
      simpa only [Finset.sum_apply] using hx.le
    _ ≤ Real.exp (-θ * ((n : ℝ) / 4)) * mgf (∑ i ∈ Finset.range n, failures i) (iidSignLaw p) θ :=
      measure_ge_le_exp_mul_mgf _ hθ.le hint
    _ ≤ Real.exp (-θ * ((n : ℝ) / 4)) *
        Real.exp ((n : ℝ) * (1 - (p : ℝ)) * (Real.exp θ - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [unitInterval.coe_symm_eq, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
        mgf_sum_bernoulli_le measurable_failures hind (failures_hasLaw p) (Finset.range n) θ
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem bad_event_union : goodᶜ = ⋃ j : ℕ, {x : SignSequence |
    ((j + 1 : ℕ) : ℝ) / 2 >
      ∑ i ∈ Finset.range (j + 1), if x (i + 1) then (1 : ℝ) else -1} := by
  ext x
  simp only [good, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hx
    push Not at hx
    obtain ⟨n, hn⟩ := hx
    have hn0 : n ≠ 0 := by intro he; subst n; simp at hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    exact ⟨j, hn⟩
  · rintro ⟨j, hj⟩ h
    exact not_le_of_gt hj (h (j + 1))

theorem whole_time_failure_bound (p : unitInterval) {θ : ℝ} (hθ : 0 < θ)
    (hp : (1 - (p : ℝ)) * (Real.exp θ - 1) ≤ θ / 8) :
    (iidSignLaw p) goodᶜ ≤
      ENNReal.ofReal (Real.exp (-θ / 8)) *
        (1 - ENNReal.ofReal (Real.exp (-θ / 8)))⁻¹ := by
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-θ / 8))
  have htail (n : ℕ) : (iidSignLaw p) {x : SignSequence | (n : ℝ) / 2 >
      ∑ i ∈ Finset.range n, if x (i + 1) then (1 : ℝ) else -1} ≤ q ^ n := by
    rw [← ofReal_measureReal]
    have hh := ENNReal.ofReal_le_ofReal (failure_tail p hθ hp n)
    convert hh using 1
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [bad_event_union]
  calc
    _ ≤ ∑' j : ℕ, (iidSignLaw p) {x : SignSequence | ((j + 1 : ℕ) : ℝ) / 2 >
        ∑ i ∈ Finset.range (j + 1), if x (i + 1) then (1 : ℝ) else -1} := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, q ^ (j + 1) := ENNReal.tsum_le_tsum (fun j => htail (j + 1))
    _ = _ := by
      simp_rw [pow_succ, mul_comm (_ ^ _) q]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

theorem whole_time_failure_small {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p : unitInterval, 1 - (p : ℝ) ≤ ε₀ →
      (iidSignLaw p).real goodᶜ ≤ δ := by
  have hsmall : 0 < min (1 / 2 : ℝ) (δ / 2) := lt_min (by norm_num) (half_pos hδ)
  obtain ⟨R, hR, hqsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hsmall))).exists
  have hexp : 0 < Real.exp (8 * R) - 1 := by
    have := Real.one_lt_exp_iff.mpr (by linarith : 0 < 8 * R)
    linarith
  refine ⟨R / (Real.exp (8 * R) - 1), div_pos hR hexp, fun p hp => ?_⟩
  have hcoef : (1 - (p : ℝ)) * (Real.exp (8 * R) - 1) ≤ (8 * R) / 8 := by
    have hm := mul_le_mul_of_nonneg_right hp hexp.le
    rw [div_mul_cancel₀ _ hexp.ne'] at hm
    linarith
  have hb := whole_time_failure_bound p (by linarith : 0 < 8 * R) hcoef
  have heq : -(8 * R) / 8 = -R := by ring
  rw [heq] at hb
  let q : ℝ := Real.exp (-R)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hqhalf : q < 1 / 2 := hqsmall.trans_le (min_le_left _ _)
  have hqδ : q < δ / 2 := hqsmall.trans_le (min_le_right _ _)
  have hq1 : q < 1 := by linarith
  have hENN : (1 : ℝ≥0∞) - ENNReal.ofReal q = ENNReal.ofReal (1 - q) := by
    rw [ENNReal.ofReal_sub 1 hq0, ENNReal.ofReal_one]
  change (iidSignLaw p) goodᶜ ≤ ENNReal.ofReal q * (1 - ENNReal.ofReal q)⁻¹ at hb
  rw [hENN, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (sub_pos.mpr hq1)] at hb
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (div_nonneg hq0 (sub_pos.mpr hq1).le)] at hr
  apply hr.trans
  apply (div_le_iff₀ (sub_pos.mpr hq1)).mpr
  nlinarith

theorem whole_time_good_small_error {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p : unitInterval, 1 - (p : ℝ) ≤ ε₀ →
      1 - δ ≤ (iidSignLaw p).real good := by
  obtain ⟨ε₀, hε₀, hbound⟩ := whole_time_failure_small hδ
  refine ⟨ε₀, hε₀, fun p hp => ?_⟩
  have hc := measureReal_compl (μ := iidSignLaw p) measurableSet_good
  have hh := hbound p hp
  rw [hc] at hh
  simp only [probReal_univ] at hh
  linarith

theorem whole_time_good_tendsto_one :
    Tendsto (fun p : unitInterval => (iidSignLaw p).real good)
      (𝓝 (1 : unitInterval)) (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨ε₀, hε₀, hε⟩ := whole_time_good_small_error (half_pos hδ)
  have hl : Tendsto (fun p : unitInterval => 1 - (p : ℝ))
      (𝓝 (1 : unitInterval)) (𝓝 0) := by
    have hf : Continuous (fun p : unitInterval => (1 : ℝ) - (p : ℝ)) :=
      continuous_const.sub continuous_subtype_val
    simpa using hf.tendsto (1 : unitInterval)
  filter_upwards [hl.eventually (gt_mem_nhds hε₀)] with p hp
  rw [Real.dist_eq]
  apply abs_lt.mpr
  have hlo := hε p hp.le
  have hhi : (iidSignLaw p).real good ≤ 1 := measureReal_le_one
  constructor <;> linarith

/-- The literal small-negative-probability parametrization of the source
auxiliary iid walk. All times, including zero, are controlled at once. -/
theorem auxiliary_halfSlope_probability_tendsto_one :
    Tendsto (fun ε : unitInterval => (iidSignLaw (unitInterval.symm ε)).real
      {x | ∀ n : ℕ, (n : ℝ) / 2 ≤
        ∑ i ∈ Finset.range n, if x (i + 1) then (1 : ℝ) else -1})
      (𝓝 (0 : unitInterval)) (𝓝 1) := by
  have hs : Tendsto unitInterval.symm (𝓝 (0 : unitInterval)) (𝓝 (1 : unitInterval)) := by
    simpa using unitInterval.continuous_symm.tendsto (0 : unitInterval)
  exact whole_time_good_tendsto_one.comp hs

theorem failures_mean (p : unitInterval) (i : ℕ) :
    (∫ x, failures i x ∂iidSignLaw p) = 1 - (p : ℝ) := by
  rw [(failures_hasLaw p i).integral_eq, integral_bernoulliMeasure]
  simp

theorem integrable_failures (p : unitInterval) (i : ℕ) :
    Integrable (failures i) (iidSignLaw p) :=
  (failures_hasLaw p i).integrable
    (integrable_bernoulliMeasure 1 0 (unitInterval.symm p) id)

/-- The source harmonic expectation uses only the genuine iid marginals;
it is separate from any localization or reverse-time coupling. -/
theorem expected_harmonic_failures (p : unitInterval) (m : ℕ) :
    (∫ x, (∑ i ∈ Finset.range m, 2 / ((i : ℝ) + 1) * failures i x) ∂iidSignLaw p) =
      2 * (1 - (p : ℝ)) * ∑ i ∈ Finset.range m, 1 / ((i : ℝ) + 1) := by
  rw [integral_finsetSum _ (fun i _ => (integrable_failures p i).const_mul _)]
  simp_rw [integral_const_mul, failures_mean]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem expected_auxiliary_harmonic_failures (ε : unitInterval) (m : ℕ) :
    (∫ x, (∑ i ∈ Finset.range m, 2 / ((i : ℝ) + 1) * failures i x)
      ∂iidSignLaw (unitInterval.symm ε)) =
      2 * (ε : ℝ) * ∑ i ∈ Finset.range m, 1 / ((i : ℝ) + 1) := by
  simpa only [unitInterval.coe_symm_eq, sub_sub_cancel] using
    expected_harmonic_failures (unitInterval.symm ε) m

end Freezing1.ForwardAnnealed.HalfSlope
