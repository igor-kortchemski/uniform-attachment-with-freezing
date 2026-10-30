module

public import Freezing1.SIRSusceptibleLaw
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Uniform noise bounds for the unstopped susceptible chain

The exponential moment estimate comes from the actual Markov law. A finite
union bound gives uniform control on every finite fluid time interval; it does
not assume independence of the increments or a martingale convergence theorem.
-/

@[expose] public section

namespace Freezing1.SIR.Susceptible

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical Topology

set_option backward.isDefEq.respectTransparency false

@[fun_prop]
theorem noise_measurable (rate : ℝ≥0) (n k : ℕ) :
    Measurable (fun H : ℕ → ℕ => noise rate n H k) := by
  unfold noise
  apply Measurable.add
  · exact ((measurable_of_countable (fun u : ℕ => (u : ℝ))).comp (measurable_pi_apply k)).sub_const _
  · exact Finset.measurable_sum _ (fun i _ =>
      (measurable_of_countable (fun u : ℕ => (infectionProbability rate u : ℝ))).comp
        (measurable_pi_apply i))

theorem noise_linear_tail (rate : ℝ≥0) (n k : ℕ) (theta t : ℝ) :
    fullLaw rate n {H | theta * t ≤ theta * noise rate n H k} ≤
      ENNReal.ofReal (Real.exp ((k : ℝ) * theta ^ 2 / 2 - theta * t)) := by
  have hm : Measurable (fun H : ℕ → ℕ =>
      ENNReal.ofReal (Real.exp (theta * noise rate n H k))) := by
    fun_prop
  have he : {H : ℕ → ℕ | theta * t ≤ theta * noise rate n H k} =
      {H | ENNReal.ofReal (Real.exp (theta * t)) ≤
        ENNReal.ofReal (Real.exp (theta * noise rate n H k))} := by
    ext H
    simp only [mem_ofPred_eq, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
      Real.exp_le_exp]
  rw [he]
  calc
    _ ≤ (∫⁻ H, ENNReal.ofReal (Real.exp (theta * noise rate n H k)) ∂fullLaw rate n) /
        ENNReal.ofReal (Real.exp (theta * t)) :=
      meas_ge_le_lintegral_div hm.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * theta ^ 2 / 2)) /
        ENNReal.ofReal (Real.exp (theta * t)) :=
      ENNReal.div_le_div_right (noise_lintegral_exp_le rate n k theta) _
    _ = _ := by rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]

theorem noise_abs_tail (rate : ℝ≥0) (n k : ℕ) {theta : ℝ} (htheta : 0 < theta) (t : ℝ) :
    fullLaw rate n {H | t ≤ |noise rate n H k|} ≤
      2 * ENNReal.ofReal (Real.exp ((k : ℝ) * theta ^ 2 / 2 - theta * t)) := by
  have hu := noise_linear_tail rate n k theta t
  have hl := noise_linear_tail rate n k (-theta) (-t)
  have he : {H : ℕ → ℕ | t ≤ |noise rate n H k|} =
      {H | theta * t ≤ theta * noise rate n H k} ∪
      {H | (-theta) * (-t) ≤ (-theta) * noise rate n H k} := by
    ext H
    simp only [mem_ofPred_eq, mem_union, le_abs]
    rw [mul_le_mul_iff_right₀ htheta]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        nlinarith
    · rintro (h | h)
      · exact Or.inl h
      · right
        nlinarith
  rw [he]
  calc
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * theta ^ 2 / 2 - theta * t)) +
        ENNReal.ofReal (Real.exp ((k : ℝ) * (-theta) ^ 2 / 2 - (-theta) * (-t))) := add_le_add hu hl
    _ = _ := by ring_nf

theorem noise_uniform_tail (rate : ℝ≥0) (n N : ℕ) {theta : ℝ} (htheta : 0 < theta) (t : ℝ) :
    fullLaw rate n {H | ∃ k ≤ N, t ≤ |noise rate n H k|} ≤
      (N + 1 : ℝ≥0∞) * 2 * ENNReal.ofReal (Real.exp ((N : ℝ) * theta ^ 2 / 2 - theta * t)) := by
  have he : {H : ℕ → ℕ | ∃ k ≤ N, t ≤ |noise rate n H k|} =
      ⋃ k ∈ Finset.range (N + 1), {H | t ≤ |noise rate n H k|} := by
    ext H
    simp
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1), fullLaw rate n {H | t ≤ |noise rate n H k|} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range (N + 1),
        2 * ENNReal.ofReal (Real.exp ((N : ℝ) * theta ^ 2 / 2 - theta * t)) := by
      apply Finset.sum_le_sum
      intro k hk
      refine (noise_abs_tail rate n k htheta t).trans ?_
      gcongr
      exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = _ := by simp [mul_assoc]

/-- Exponential decay dominates the linear size of the observation horizon. -/
theorem linear_exp_decay {c : ℝ} (hc : 0 < c) (m : ℝ) :
    Tendsto (fun n : ℕ => 2 * ((n : ℝ) * m + 1) * Real.exp (-c * n)) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hx
  convert ((h1.const_mul (m / c)).add h0).const_mul 2 using 1
  · funext n
    simp only [Function.comp_def, pow_one, pow_zero, one_mul]
    field_simp [hc.ne']
  · simp

/-- The accumulated centered noise, divided by the population size, vanishes
uniformly up to time `n * m`, under the actual varying Markov laws. -/
theorem noise_uniform_div_population_tendsto (rate : ℕ → ℝ≥0) (m : ℕ)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => fullLaw (rate n) n
      {H | ∃ k ≤ n * m, eps * n ≤ |noise (rate n) n H k|}) atTop (𝓝 0) := by
  let theta : ℝ := eps / ((m : ℝ) + 1)
  have hd : 0 < (m : ℝ) + 1 := by positivity
  have ht : 0 < theta := div_pos heps hd
  have htm : (m : ℝ) * theta ≤ eps := by
    dsimp [theta]
    rw [← mul_div_assoc, div_le_iff₀ hd]
    nlinarith
  let c : ℝ := theta * eps / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hbound (n : ℕ) : fullLaw (rate n) n
      {H | ∃ k ≤ n * m, eps * n ≤ |noise (rate n) n H k|} ≤
      ENNReal.ofReal (2 * ((n : ℝ) * m + 1) * Real.exp (-c * n)) := by
    refine (noise_uniform_tail (rate n) n (n * m) ht (eps * n)).trans ?_
    have he : ((n * m : ℕ) : ℝ) * theta ^ 2 / 2 - theta * (eps * n) ≤ -c * n := by
      have hh := mul_le_mul_of_nonneg_left htm ht.le
      have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      dsimp [c]
      push_cast
      nlinarith
    calc
      _ ≤ ((n * m : ℝ≥0∞) + 1) * 2 * ENNReal.ofReal (Real.exp (-c * n)) := by
        push_cast
        gcongr
        simpa only [Nat.cast_mul] using he
      _ = _ := by
        have hfac : ENNReal.ofReal (2 * ((n : ℝ) * m + 1)) =
            ((n * m : ℝ≥0∞) + 1) * 2 := by
          rw [ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_add (by positivity) (by norm_num),
            ENNReal.ofReal_mul (Nat.cast_nonneg n)]
          simp
          ring
        rw [ENNReal.ofReal_mul (by positivity), hfac]
  have hlim : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (2 * ((n : ℝ) * m + 1) * Real.exp (-c * n))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (linear_exp_decay hc m)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hbound

end Freezing1.SIR.Susceptible
