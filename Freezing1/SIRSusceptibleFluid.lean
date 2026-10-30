module

public import Freezing1.SIRSusceptibleConcentration
public import Freezing1.SIRFluidApproximation

/-!
# The uniform fluid limit for the actual unstopped susceptible process

The infection rate is allowed to vary with the population size. Its exact
scaled value `n * rate n` enters the drift comparison before taking its limit.
-/

@[expose] public section

namespace Freezing1.SIR.Susceptible

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical Topology

set_option backward.isDefEq.respectTransparency false

/-- Pathwise transfer of accumulated noise control to profile control. -/
theorem normalized_path_fluid_bound (rate : ℝ≥0) {n : ℕ} (hn : 0 < n)
    {lam B : ℝ} (hlam : 0 < lam) (hB : 0 ≤ B) (m : ℕ)
    (H : ℕ → ℕ) (h0 : H 0 = n) (hb : ∀ k, H k ≤ n)
    (hnoise : ∀ k ≤ n * m, |noise rate n H k| ≤ B * n) :
    ∀ k ≤ n * m, |(H k : ℝ) / n - fluidProfile lam ((k : ℝ) / n)| ≤
      (B + (m : ℝ) * |(n : ℝ) * rate - lam| + (m : ℝ) * lam ^ 2 / n) *
        Real.exp (lam * m) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he := susceptible_fluid_error_bound_on_time_interval hlam
    (show 0 ≤ (n : ℝ) * rate by positivity) (show 0 ≤ 1 / (n : ℝ) by positivity)
    hB (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    (fun k => (H k : ℝ) / n) (fun k => noise rate n H k / n) (n * m)
    (by push_cast; field_simp; exact le_rfl)
    (by
      intro k _
      constructor
      · positivity
      · exact (div_le_one hnR).mpr (by exact_mod_cast hb k))
    (by
      intro k hk
      rw [abs_div, abs_of_pos hnR, div_le_iff₀ hnR]
      exact hnoise k hk)
    (by
      intro k _
      rw [h0, div_self hnR.ne']
      have hd := susceptible_noise_decomposition rate hn H k
      rw [show (∑ i ∈ Finset.range k, infectionFraction ((n : ℝ) * rate * ((H i : ℝ) / n))) =
          ∑ i ∈ Finset.range k, (infectionProbability rate (H i) : ℝ) by
        apply Finset.sum_congr rfl
        intro i _
        rw [infectionProbability_coe]
        congr 1
        field_simp]
      exact hd)
  intro k hk
  simpa [h0, hnR.ne', div_eq_mul_inv, mul_assoc] using he k hk

/-- Uniform convergence in probability on every fixed natural fluid horizon,
under the genuine varying unstopped Markov laws. -/
theorem uniform_fluid_tendsto (rate : ℕ → ℝ≥0) {lam : ℝ} (hlam : 0 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (m : ℕ) {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => fullLaw (rate n) n
      {H | ∃ k ≤ n * m,
        eps ≤ |(H k : ℝ) / n - fluidProfile lam ((k : ℝ) / n)|}) atTop (𝓝 0) := by
  let delta : ℝ := eps / (4 * Real.exp (lam * m))
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hdelta : (delta + delta) * Real.exp (lam * m) < eps := by
    dsimp [delta]
    field_simp
    nlinarith [Real.exp_pos (lam * m)]
  have hbias : Tendsto (fun n : ℕ =>
      (m : ℝ) * |(n : ℝ) * rate n - lam| + (m : ℝ) * lam ^ 2 / n) atTop (𝓝 0) := by
    have h1 := ((hrate.sub_const lam).abs).const_mul (m : ℝ)
    have h2 := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
      ((m : ℝ) * lam ^ 2)
    simpa [div_eq_mul_inv] using h1.add h2
  have heventually : ∀ᶠ n : ℕ in atTop,
      fullLaw (rate n) n {H | ∃ k ≤ n * m,
        eps ≤ |(H k : ℝ) / n - fluidProfile lam ((k : ℝ) / n)|} ≤
      fullLaw (rate n) n {H | ∃ k ≤ n * m, delta * n ≤ |noise (rate n) n H k|} := by
    filter_upwards [eventually_gt_atTop 0, hbias.eventually (gt_mem_nhds hd)] with n hn hsmall
    apply measure_mono_ae
    filter_upwards [fullLaw_initial (rate n) n, fullLaw_bounds (rate n) n] with H h0 hb
    intro hbad
    by_contra hnoise
    simp only [not_exists, not_and, not_le] at hnoise
    have hh := normalized_path_fluid_bound (rate n) hn hlam hd.le m H h0
      (fun k => (hb k).2) (fun k hk => (hnoise k hk).le)
    rcases hbad with ⟨k, hk, he⟩
    have hbound := hh k hk
    have hnon : 0 ≤ Real.exp (lam * m) := (Real.exp_pos _).le
    have hcomp :
        (delta + (m : ℝ) * |(n : ℝ) * rate n - lam| + (m : ℝ) * lam ^ 2 / n) *
          Real.exp (lam * m) ≤ (delta + delta) * Real.exp (lam * m) := by
      apply mul_le_mul_of_nonneg_right _ hnon
      linarith
    exact (not_lt_of_ge he) (hbound.trans_lt (hcomp.trans_lt hdelta))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (noise_uniform_div_population_tendsto rate m hd) (Eventually.of_forall fun _ => bot_le)
    heventually

/-- The same convergence on an arbitrary bounded real time interval. -/
theorem uniform_fluid_on_time_interval_tendsto (rate : ℕ → ℝ≥0)
    {lam : ℝ} (hlam : 0 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (T : ℝ) {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => fullLaw (rate n) n
      {H | ∃ k : ℕ, (k : ℝ) / n ≤ T ∧
        eps ≤ |(H k : ℝ) / n - fluidProfile lam ((k : ℝ) / n)|}) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      fullLaw (rate n) n {H | ∃ k : ℕ, (k : ℝ) / n ≤ T ∧
        eps ≤ |(H k : ℝ) / n - fluidProfile lam ((k : ℝ) / n)|} ≤
      fullLaw (rate n) n {H | ∃ k ≤ n * ⌈T⌉₊,
        eps ≤ |(H k : ℝ) / n - fluidProfile lam ((k : ℝ) / n)|} := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    apply measure_mono
    rintro H ⟨k, hk, he⟩
    refine ⟨k, ?_, he⟩
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hh := (div_le_iff₀ hnR).mp (hk.trans (Nat.le_ceil T))
    exact_mod_cast (by simpa only [mul_comm] using hh : (k : ℝ) ≤ (n : ℝ) * ⌈T⌉₊)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (uniform_fluid_tendsto rate hlam hrate ⌈T⌉₊ heps)
    (Eventually.of_forall fun _ => bot_le) hbound

/-- The unrestricted integer infectious coordinate inherits the susceptible
profile, including after it has become negative. -/
theorem normalized_infectious_error {n : ℕ} (hn : 0 < n) (k : ℕ)
    (H : ℕ → ℕ) (lam : ℝ) :
    |(infectious n k H : ℝ) / n - infectiousProfile lam ((k : ℝ) / n)| ≤
      2 * |(H k : ℝ) / n - fluidProfile lam ((k : ℝ) / n)| + 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (infectious n k H : ℝ) / n - infectiousProfile lam ((k : ℝ) / n) =
      -2 * ((H k : ℝ) / n - fluidProfile lam ((k : ℝ) / n)) + 1 / n := by
    simp only [infectious, infectiousProfile, Int.cast_add, Int.cast_sub,
      Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    field_simp [hnR.ne']
    ring
  rw [he]
  simpa only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / n)]
    using abs_add_le (-2 * ((H k : ℝ) / n - fluidProfile lam ((k : ℝ) / n))) (1 / n)

theorem uniform_infectious_fluid_tendsto (rate : ℕ → ℝ≥0) {lam : ℝ} (hlam : 0 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (m : ℕ) {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => fullLaw (rate n) n
      {H | ∃ k ≤ n * m,
        eps ≤ |(infectious n k H : ℝ) / n - infectiousProfile lam ((k : ℝ) / n)|})
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound : ∀ᶠ n : ℕ in atTop,
      fullLaw (rate n) n {H | ∃ k ≤ n * m,
        eps ≤ |(infectious n k H : ℝ) / n - infectiousProfile lam ((k : ℝ) / n)|} ≤
      fullLaw (rate n) n {H | ∃ k ≤ n * m,
        eps / 4 ≤ |(H k : ℝ) / n - fluidProfile lam ((k : ℝ) / n)|} := by
    filter_upwards [eventually_gt_atTop 0,
      hinv.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < eps / 2))] with n hn hsmall
    apply measure_mono
    rintro H ⟨k, hk, he⟩
    refine ⟨k, hk, ?_⟩
    have hh := normalized_infectious_error hn k H lam
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (uniform_fluid_tendsto rate hlam hrate m (by positivity : 0 < eps / 4))
    (Eventually.of_forall fun _ => bot_le) hbound

end Freezing1.SIR.Susceptible
