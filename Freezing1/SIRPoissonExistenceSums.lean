module

public import Freezing1.SIRExponentialRace
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Partial sums of independent exponential waiting times

For a rate `r > 0`, let `E 0, E 1, ...` be independent exponential waiting
times, realised as the coordinates of an infinite product measure. The law of
the partial sum `S k E = E 0 + ... + E (k - 1)` is computed by induction on
`k`, from the independence of `S k` and `E k` and an explicit convolution
integral: `P(S k ≤ u)` is the Poisson tail series
`∑ j ≥ k, exp (-(r u)) (r u) ^ j / j !` for `u ≥ 0`. In particular the partial
sums are almost surely unbounded.
-/

@[expose] public section

namespace Freezing1.SIR.PoissonExistence

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false

/-- The Poisson mass `exp (-(r u)) (r u)^j / j!`. -/
noncomputable def pmass (r : ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-(r * u)) * (r * u) ^ j / (j.factorial : ℝ)

theorem pmass_nonneg {r : ℝ} (hr : 0 ≤ r) (j : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ pmass r j u := by
  unfold pmass
  have := mul_nonneg hr hu
  positivity

theorem measurable_pmass (r : ℝ) (j : ℕ) : Measurable (pmass r j) := by
  unfold pmass
  fun_prop

theorem lintegral_exp_convolve {r : ℝ} (hr : 0 < r) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s, (if 0 ≤ t - s then ENNReal.ofReal (pmass r j (t - s)) else 0) ∂(expMeasure r) =
      ENNReal.ofReal (pmass r (j + 1) t) := by
  have hm : Measurable (fun s : ℝ => if 0 ≤ t - s then ENNReal.ofReal (pmass r j (t - s)) else 0) :=
    Measurable.ite (measurableSet_le measurable_const (by fun_prop))
      (((measurable_pmass r j).comp (by fun_prop : Measurable fun s : ℝ => t - s)).ennreal_ofReal)
      measurable_const
  change ∫⁻ s, _ ∂(volume.withDensity (exponentialPDF r)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (measurable_exponentialPDF r) hm]
  have hc : ∀ s : ℝ, (exponentialPDF r * (fun s : ℝ => if 0 ≤ t - s then
      ENNReal.ofReal (pmass r j (t - s)) else 0)) s = (Icc 0 t).indicator
        (fun s => ENNReal.ofReal (r ^ (j + 1) * Real.exp (-(r * t)) / (j.factorial : ℝ) *
          (t - s) ^ j)) s := by
    intro s
    by_cases hs0 : 0 ≤ s
    · by_cases hst : s ≤ t
      · rw [Pi.mul_apply, ite_eq_left (by linarith), exponentialPDF_of_nonneg hs0,
          indicator_of_mem (show s ∈ Icc 0 t from ⟨hs0, hst⟩), ← ENNReal.ofReal_mul
            (mul_nonneg hr.le (Real.exp_pos _).le)]
        congr 1
        unfold pmass
        have : Real.exp (-(r * (t - s))) * Real.exp (-(r * s)) = Real.exp (-(r * t)) := by
          rw [← Real.exp_add]; congr 1; ring
        calc _ = (Real.exp (-(r * (t - s))) * Real.exp (-(r * s))) * (r * (t - s)) ^ j * r /
              (j.factorial : ℝ) := by ring
          _ = _ := by rw [this, mul_pow]; ring
      · rw [Pi.mul_apply, ite_eq_right (by linarith), mul_zero,
          indicator_of_notMem (show s ∉ Icc 0 t from fun h => hst h.2)]
    · rw [Pi.mul_apply, exponentialPDF_of_neg (not_le.mp hs0), zero_mul,
        indicator_of_notMem (show s ∉ Icc 0 t from fun h => hs0 h.1)]
  rw [lintegral_congr hc, lintegral_indicator measurableSet_Icc]
  set c : ℝ := r ^ (j + 1) * Real.exp (-(r * t)) / (j.factorial : ℝ) with hcdef
  have hcnn : 0 ≤ c := by positivity
  have hcont : Continuous (fun s : ℝ => c * (t - s) ^ j) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
    ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun s hs =>
      mul_nonneg hcnn (pow_nonneg (by linarith [hs.2]) _)))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ j) t, integral_pow]
  unfold pmass
  rw [hcdef]
  simp only [sub_self, sub_zero, zero_pow (Nat.succ_ne_zero j)]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- `P(sum of the first `k` waiting times ≤ u)`, as a Poisson tail series. -/
noncomputable def tail (r : ℝ) (k : ℕ) (u : ℝ) : ℝ≥0∞ :=
  if 0 ≤ u then ∑' j, ENNReal.ofReal (pmass r (j + k) u) else 0

theorem tail_of_neg (r : ℝ) (k : ℕ) {u : ℝ} (hu : u < 0) : tail r k u = 0 :=
  ite_eq_right (not_le.mpr hu)

theorem tail_of_nonneg (r : ℝ) (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    tail r k u = ∑' j, ENNReal.ofReal (pmass r (j + k) u) :=
  ite_eq_left hu

theorem measurable_tail (r : ℝ) (k : ℕ) : Measurable (tail r k) := by
  unfold tail
  refine Measurable.ite (measurableSet_le measurable_const measurable_id) ?_ measurable_const
  exact Measurable.tsum fun j => ((measurable_pmass r _)).ennreal_ofReal

theorem lintegral_tail_convolve {r : ℝ} (hr : 0 < r) (k : ℕ) (t : ℝ) :
    ∫⁻ s, tail r k (t - s) ∂(expMeasure r) = tail r (k + 1) t := by
  by_cases ht : 0 ≤ t
  · have hpt : ∀ s : ℝ, tail r k (t - s) = ∑' j, (if 0 ≤ t - s then
        ENNReal.ofReal (pmass r (j + k) (t - s)) else 0) := by
      intro s
      by_cases hs : 0 ≤ t - s
      · simp only [tail_of_nonneg r k hs, hs, ite_true]
      · simp only [tail_of_neg r k (not_le.mp hs), hs, ite_false, tsum_zero]
    simp_rw [hpt]
    rw [lintegral_tsum]
    · rw [tail_of_nonneg r (k + 1) ht]
      refine tsum_congr fun j => ?_
      rw [lintegral_exp_convolve hr (j + k) ht, add_assoc]
    · intro j
      exact (Measurable.ite (measurableSet_le measurable_const (by fun_prop))
        (((measurable_pmass r _).comp (by fun_prop : Measurable fun s : ℝ => t - s)).ennreal_ofReal)
        measurable_const).aemeasurable
  · have ht' : t < 0 := not_le.mp ht
    rw [tail_of_neg r (k + 1) ht']
    have hnn : ∀ᵐ s ∂expMeasure r, 0 ≤ s := by
      have := isProbabilityMeasure_expMeasure hr
      have ht0 : ∀ᵐ s ∂expMeasure r, 0 < s := by
        apply (mem_ae_iff_prob_eq_one measurableSet_Ioi).mpr
        simpa using expMeasure_Ioi_of_nonneg hr (show (0 : ℝ) ≤ 0 by rfl)
      exact ht0.mono fun _ hs => hs.le
    rw [lintegral_congr_ae (g := fun _ => 0)]
    · simp
    · exact hnn.mono fun s hs => tail_of_neg r k (by linarith)

/-- The law of the independent exponential waiting times. -/
noncomputable abbrev waiting (r : ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => expMeasure r)

/-- Sum of the first `k` waiting times. -/
def S (k : ℕ) (E : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range k, E i

theorem measurable_S (k : ℕ) : Measurable (S k) := by
  unfold S
  fun_prop

theorem S_succ (k : ℕ) (E : ℕ → ℝ) : S (k + 1) E = S k E + E k := by
  simp only [S, Finset.sum_range_succ]

theorem isProbabilityMeasure_waiting {r : ℝ} (hr : 0 < r) : IsProbabilityMeasure (waiting r) := by
  have := isProbabilityMeasure_expMeasure hr
  infer_instance

theorem iIndepFun_waiting {r : ℝ} (hr : 0 < r) :
    iIndepFun (fun (i : ℕ) (E : ℕ → ℝ) => E i) (waiting r) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun i => measurable_pi_apply i)]
  simp only [Measure.infinitePi_map_eval]
  exact Measure.map_id

theorem waiting_sum_le_succ {r : ℝ} (hr : 0 < r) (k : ℕ) (t : ℝ) :
    waiting r {E | S (k + 1) E ≤ t} =
      ∫⁻ s, waiting r {E | S k E ≤ t - s} ∂(expMeasure r) := by
  have := isProbabilityMeasure_expMeasure hr
  have := isProbabilityMeasure_waiting hr
  have hind := (iIndepFun_waiting hr).indepFun_sum_range_succ (fun i => measurable_pi_apply i) k
  have hS : (∑ j ∈ Finset.range k, fun E : ℕ → ℝ => E j) = S k := by
    ext E
    simp only [S, Finset.sum_apply]
  rw [hS] at hind
  have hmap := hind.map_prod_eq_prod_map_map (measurable_S k).aemeasurable
    (measurable_pi_apply k).aemeasurable
  rw [Measure.infinitePi_map_eval] at hmap
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ≤ t} :=
    measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  have h1 : waiting r {E | S (k + 1) E ≤ t} =
      (waiting r).map (fun E => (S k E, E k)) {p : ℝ × ℝ | p.1 + p.2 ≤ t} := by
    rw [Measure.map_apply ((measurable_S k).prodMk (measurable_pi_apply k)) hset]
    simp only [S_succ]
    rfl
  rw [h1, hmap, Measure.prod_apply_symm hset]
  refine lintegral_congr fun s => ?_
  have hm : MeasurableSet ((fun x : ℝ => (x, s)) ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ≤ t}) :=
    hset.preimage (by fun_prop)
  rw [Measure.map_apply (measurable_S k) hm]
  congr 1
  ext E
  simp only [mem_preimage, mem_ofPred_eq, le_sub_iff_add_le]

theorem waiting_sum_le_eq_tail {r : ℝ} (hr : 0 < r) (k : ℕ) (t : ℝ) :
    waiting r {E | S k E ≤ t} = tail r k t := by
  induction k generalizing t with
  | zero =>
    have := isProbabilityMeasure_waiting hr
    by_cases ht : 0 ≤ t
    · have hset : {E : ℕ → ℝ | S 0 E ≤ t} = univ := by
        ext E
        simp [S, ht]
      rw [hset, measure_univ, tail_of_nonneg r 0 ht]
      have hsum : HasSum (fun j : ℕ => pmass r j t) 1 := by
        convert hasSum_one_poissonMeasure ⟨r * t, mul_nonneg hr.le ht⟩ using 1
        funext j
        simp only [pmass]
        rfl
      simp only [add_zero]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => pmass_nonneg hr.le j ht) hsum.summable,
        hsum.tsum_eq, ENNReal.ofReal_one]
    · have hset : {E : ℕ → ℝ | S 0 E ≤ t} = ∅ := by
        ext E
        simp [S, ht]
      rw [hset, measure_empty, tail_of_neg r 0 (not_le.mp ht)]
  | succ k ih =>
    rw [waiting_sum_le_succ hr k t]
    simp_rw [ih]
    exact lintegral_tail_convolve hr k t

theorem tail_eq_add {r : ℝ} (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    tail r k u = ENNReal.ofReal (pmass r k u) + tail r (k + 1) u := by
  rw [tail_of_nonneg r k hu, tail_of_nonneg r (k + 1) hu,
    tsum_eq_zero_add' ENNReal.summable]
  congr 1
  · simp
  · exact tsum_congr fun j => by rw [show j + 1 + k = j + (k + 1) by omega]

theorem tendsto_tail_zero {r : ℝ} (hr : 0 < r) {M : ℝ} (hM : 0 ≤ M) :
    Tendsto (fun k => tail r k M) atTop (𝓝 0) := by
  have hfin : ∑' j, ENNReal.ofReal (pmass r j M) ≠ ∞ := by
    have := isProbabilityMeasure_waiting hr
    have h0 := waiting_sum_le_eq_tail hr 0 M
    rw [tail_of_nonneg r 0 hM] at h0
    simp only [add_zero] at h0
    rw [← h0]
    exact measure_ne_top _ _
  simp_rw [tail_of_nonneg r _ hM]
  exact ENNReal.tendsto_sum_nat_add (fun j => ENNReal.ofReal (pmass r j M)) hfin

/-- The partial sums of the waiting times exceed any given bound, almost surely. -/
theorem waiting_ae_exists_gt {r : ℝ} (hr : 0 < r) (M : ℝ) :
    ∀ᵐ E ∂waiting r, ∃ k, M < S k E := by
  by_cases hM : 0 ≤ M
  · have h0 : waiting r {E | ∀ k, S k E ≤ M} = 0 := by
      refine le_antisymm (ge_of_tendsto' (tendsto_tail_zero hr hM) fun k => ?_) bot_le
      rw [← waiting_sum_le_eq_tail hr k M]
      exact measure_mono fun E hE => hE k
    have := (measure_eq_zero_iff_ae_notMem.1 h0)
    refine this.mono fun E hE => ?_
    simpa only [mem_ofPred_eq, not_forall, not_le] using hE
  · have hM' : M < 0 := not_le.mp hM
    exact ae_of_all _ fun E => ⟨0, by simpa only [S, Finset.range_zero, Finset.sum_empty] using hM'⟩

/-- Each waiting time is almost surely positive. -/
theorem waiting_ae_pos {r : ℝ} (hr : 0 < r) (i : ℕ) : ∀ᵐ E ∂waiting r, 0 < E i := by
  have := isProbabilityMeasure_expMeasure hr
  have ht0 : ∀ᵐ s ∂expMeasure r, 0 < s := by
    apply (mem_ae_iff_prob_eq_one measurableSet_Ioi).mpr
    simpa using expMeasure_Ioi_of_nonneg hr (show (0 : ℝ) ≤ 0 by rfl)
  refine ae_of_ae_map (measurable_pi_apply i).aemeasurable ?_
  rw [Measure.infinitePi_map_eval]
  exact ht0

end Freezing1.SIR.PoissonExistence
