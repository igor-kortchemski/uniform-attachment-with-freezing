module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Tactic

/-!
# Genuine independent exponential races for the SIR embedded kernel

The two-clock result is computed from the product of the actual exponential
measures. The proof uses their survival functions and density normalization;
the infection/recovery probability is not assumed as a race-law hypothesis.
The bridge from every individual Poisson/recovery clock remains separate.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

theorem expMeasure_Ioi_of_nonneg {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    expMeasure r (Ioi x) = ENNReal.ofReal (Real.exp (-(r * x))) := by
  haveI := isProbabilityMeasure_expMeasure hr
  have hsub : 0 ≤ 1 - Real.exp (-(r * x)) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    nlinarith
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
    ← ofReal_cdf, cdf_expMeasure_eq hr, ite_eq_left hx,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hsub]
  congr 1
  ring

theorem measurable_exponentialPDF (r : ℝ) : Measurable (exponentialPDF r) :=
  (measurable_exponentialPDFReal r).ennreal_ofReal

theorem exponentialPDF_mul_tail {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    exponentialPDF a x * expMeasure b (Ioi x) =
      ENNReal.ofReal (a / (a + b)) * exponentialPDF (a + b) x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, expMeasure_Ioi_of_nonneg hb hx,
      exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (mul_nonneg ha.le (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (div_nonneg ha.le (by positivity))]
    congr 1
    have hab : a + b ≠ 0 := by positivity
    rw [show -((a + b) * x) = -(a * x) + -(b * x) by ring, Real.exp_add]
    field_simp [hab]
  · have hn : x < 0 := by linarith
    rw [exponentialPDF_of_neg hn, exponentialPDF_of_neg hn, zero_mul, mul_zero]

theorem lintegral_exponential_tail {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ x, expMeasure b (Ioi x) ∂expMeasure a = ENNReal.ofReal (a / (a + b)) := by
  haveI := isProbabilityMeasure_expMeasure hb
  have hg : Measurable (fun x : ℝ => expMeasure b (Ioi x)) :=
    measurable_measure_prodMk_left (measurableSet_lt measurable_fst measurable_snd)
  change ∫⁻ x, expMeasure b (Ioi x) ∂volume.withDensity (exponentialPDF a) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (measurable_exponentialPDF a) hg]
  simp only [Pi.mul_apply, exponentialPDF_mul_tail ha hb]
  rw [lintegral_const_mul _ (measurable_exponentialPDF (a + b)),
    lintegral_exponentialPDF_eq_one (by positivity), mul_one]

theorem exponential_race_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((expMeasure a).prod (expMeasure b)) {z | z.1 < z.2} =
      ENNReal.ofReal (a / (a + b)) := by
  haveI := isProbabilityMeasure_expMeasure hb
  rw [Measure.prod_apply (measurableSet_lt measurable_fst measurable_snd)]
  exact lintegral_exponential_tail ha hb

theorem exponential_race_right {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((expMeasure a).prod (expMeasure b)) {z | z.2 < z.1} =
      ENNReal.ofReal (b / (a + b)) := by
  haveI := isProbabilityMeasure_expMeasure ha
  haveI := isProbabilityMeasure_expMeasure hb
  rw [Measure.prod_apply_symm (measurableSet_lt measurable_snd measurable_fst)]
  change (∫⁻ y, expMeasure a (Ioi y) ∂expMeasure b) = _
  simpa only [add_comm] using lintegral_exponential_tail hb ha

theorem expMeasure_Ioi_of_neg {r x : ℝ} (hr : 0 < r) (hx : x < 0) :
    expMeasure r (Ioi x) = 1 := by
  haveI := isProbabilityMeasure_expMeasure hr
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
    ← ofReal_cdf, cdf_expMeasure_eq hr, ite_eq_right (not_le_of_gt hx)]
  simp

theorem independent_exponential_all_later {ι : Type*} [Fintype ι]
    (rate : ι → ℝ) (hr : ∀ i, 0 < rate i) (x : ℝ) (hx : 0 ≤ x) :
    (Measure.pi (fun i => expMeasure (rate i))) {t | ∀ i, x < t i} =
      ENNReal.ofReal (Real.exp (-((∑ i, rate i) * x))) := by
  haveI : ∀ i, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  have he : {t : ι → ℝ | ∀ i, x < t i} = Set.pi Set.univ (fun _ => Ioi x) := by
    ext t
    simp [Set.mem_pi]
  rw [he, Measure.pi_pi]
  simp_rw [expMeasure_Ioi_of_nonneg (hr _) hx]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
    ← Real.exp_sum]
  congr 2
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul]

noncomputable def earliestClock {ι : Type*} [Fintype ι] [Nonempty ι] (t : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty t

theorem measurable_earliestClock {ι : Type*} [Fintype ι] [Nonempty ι] :
    Measurable (earliestClock : (ι → ℝ) → ℝ) := by
  apply measurable_of_Ioi
  intro x
  have he : earliestClock ⁻¹' Ioi x = ⋂ i : ι, {t : ι → ℝ | x < t i} := by
    ext t
    simp [earliestClock, Finset.lt_inf'_iff]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_lt measurable_const (measurable_pi_apply i))

theorem earliestClock_law {ι : Type*} [Fintype ι] [Nonempty ι]
    (rate : ι → ℝ) (hr : ∀ i, 0 < rate i) :
    (Measure.pi (fun i => expMeasure (rate i))).map earliestClock = expMeasure (∑ i, rate i) := by
  haveI : ∀ i, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  have hsum : 0 < ∑ i, rate i := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  haveI := isProbabilityMeasure_expMeasure hsum
  have htail : ∀ x : ℝ,
      ((Measure.pi (fun i => expMeasure (rate i))).map earliestClock) (Ioi x) =
        expMeasure (∑ i, rate i) (Ioi x) := by
    intro x
    rw [Measure.map_apply measurable_earliestClock measurableSet_Ioi]
    have he : earliestClock ⁻¹' Ioi x = {t : ι → ℝ | ∀ i, x < t i} := by
      ext t
      simp [earliestClock, Finset.lt_inf'_iff]
    rw [he]
    by_cases hx : 0 ≤ x
    · rw [independent_exponential_all_later rate hr x hx, expMeasure_Ioi_of_nonneg hsum hx]
    · have hn : x < 0 := by linarith
      rw [expMeasure_Ioi_of_neg hsum hn]
      have hpi : {t : ι → ℝ | ∀ i, x < t i} = Set.pi Set.univ (fun _ => Ioi x) := by
        ext t
        simp [Set.mem_pi]
      rw [hpi, Measure.pi_pi]
      simp_rw [expMeasure_Ioi_of_neg (hr _) hn]
      simp
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, cdf_eq_real]
  apply congrArg ENNReal.toReal
  rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _),
    measure_compl measurableSet_Ioi (measure_ne_top _ _), measure_univ, measure_univ, htail]

/-- When the aggregate infection and recovery clocks have their actual
rates r*U*I and I, cancellation gives the SIR event probabilities. -/
theorem sir_aggregate_race {r : ℝ} {u i : ℕ} (hr : 0 < r) (hu : 0 < u) (hi : 0 < i) :
    (((expMeasure (r * u * i)).prod (expMeasure (i : ℝ))) {z | z.1 < z.2} =
      ENNReal.ofReal (r * u / (1 + r * u))) ∧
    (((expMeasure (r * u * i)).prod (expMeasure (i : ℝ))) {z | z.2 < z.1} =
      ENNReal.ofReal (1 / (1 + r * u))) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hrace := exponential_race_left (mul_pos (mul_pos hr huR) hiR) hiR
  have hrec := exponential_race_right (mul_pos (mul_pos hr huR) hiR) hiR
  have hleft : r * u * i / (r * u * i + i) = r * u / (1 + r * u) := by
    field_simp
    <;> ring
  have hright : (i : ℝ) / (r * u * i + i) = 1 / (1 + r * u) := by
    field_simp
    <;> ring
  exact ⟨hrace.trans (congrArg ENNReal.ofReal hleft),
    hrec.trans (congrArg ENNReal.ofReal hright)⟩

noncomputable def individualClockLaw (r : ℝ) (i u : ℕ) :
    Measure (((Fin i × Fin u) → ℝ) × (Fin i → ℝ)) :=
  (Measure.pi (fun _ : Fin i × Fin u => expMeasure r)).prod
    (Measure.pi (fun _ : Fin i => expMeasure 1))

theorem individualClock_minima_law {r : ℝ} (hr : 0 < r) (i u : ℕ)
    [NeZero i] [NeZero u] :
    (individualClockLaw r i u).map (Prod.map earliestClock earliestClock) =
      (expMeasure (r * u * i)).prod (expMeasure (i : ℝ)) := by
  haveI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) := isProbabilityMeasure_expMeasure (by norm_num)
  have hc := earliestClock_law (fun _ : Fin i × Fin u => r) (fun _ => hr)
  have hr' := earliestClock_law (fun _ : Fin i => (1 : ℝ)) (fun _ => by norm_num)
  have hsum : (∑ _ : Fin i × Fin u, r) = r * u * i := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    ring
  rw [hsum] at hc
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hr'
  rw [individualClockLaw, ← Measure.map_prod_map _ _ measurable_earliestClock measurable_earliestClock,
    hc, hr']

/-- The event-type law follows from the actual independent clocks of every
infectious/susceptible pair and every infectious individual's recovery. -/
theorem individualClock_race {r : ℝ} (hr : 0 < r) (i u : ℕ) [NeZero i] [NeZero u] :
    (individualClockLaw r i u) {z | earliestClock z.1 < earliestClock z.2} =
      ENNReal.ofReal (r * u / (1 + r * u)) ∧
    (individualClockLaw r i u) {z | earliestClock z.2 < earliestClock z.1} =
      ENNReal.ofReal (1 / (1 + r * u)) := by
  have hm : Measurable (Prod.map (earliestClock : ((Fin i × Fin u) → ℝ) → ℝ)
      (earliestClock : (Fin i → ℝ) → ℝ)) :=
    measurable_earliestClock.prodMap measurable_earliestClock
  have hlaw := individualClock_minima_law hr i u
  have hprob := sir_aggregate_race hr (Nat.pos_of_ne_zero (NeZero.ne u))
    (Nat.pos_of_ne_zero (NeZero.ne i))
  constructor
  · calc
      _ = ((individualClockLaw r i u).map (Prod.map earliestClock earliestClock))
          {z | z.1 < z.2} := by
            rw [Measure.map_apply hm (measurableSet_lt measurable_fst measurable_snd)]
            rfl
      _ = _ := by rw [hlaw]; exact hprob.1
  · calc
      _ = ((individualClockLaw r i u).map (Prod.map earliestClock earliestClock))
          {z | z.2 < z.1} := by
            rw [Measure.map_apply hm (measurableSet_lt measurable_snd measurable_fst)]
            rfl
      _ = _ := by rw [hlaw]; exact hprob.2

end Freezing1.SIR
