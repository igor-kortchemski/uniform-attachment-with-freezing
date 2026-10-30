module

public import Freezing1.SIRStrongCounts
public import Freezing1.SIRStoppedCoupling
public import Freezing1.SIRSusceptibleConcentration

/-!
# Late infection probabilities vanish in the strong-infection regime

The argument uses the true stopped/unstopped coupling and its actual noise.
It does not condition a reversed path or assume a reverse-time coupling.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology BigOperators

set_option backward.isDefEq.respectTransparency false

def lateIndex (n : ℕ) : ℕ := n + n / 2

theorem lateIndex_bounds (n : ℕ) : n ≤ lateIndex n ∧ lateIndex n ≤ 2 * n := by
  unfold lateIndex
  omega

theorem countsFullLaw_susceptible_at_population_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | eps * n ≤ (H n).susceptible}) atTop (𝓝 0) := by
  have hscale : Tendsto (fun n : ℕ => eps * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop heps tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ n : ℕ in atTop,
      (countsFullLaw (rate n) n).real {H | eps * n ≤ (H n).susceptible} ≤
      (countsFullLaw (rate n) n).real {H | ∃ k ≤ 2 * n,
        (eps / 2) * n ≤ |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|} := by
    filter_upwards [hscale.eventually_ge_atTop 2] with n hn
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [countsFullLaw_valid (rate n) n] with H hv hbad
    have hh : ((H n).susceptible : ℝ) + (H n).infectious ≤ (n : ℝ) + 1 := by
      exact_mod_cast hv n
    refine ⟨n, by omega, ?_⟩
    rw [show 2 * n - n = n by omega, min_self]
    have ha := neg_le_abs (((H n).infectious : ℝ) - n)
    nlinarith
  exact squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound
    (countsFullLaw_triangle_tendsto_zero rate hstrong (by positivity : 0 < eps / 2))

theorem countsFullLaw_late_extinction_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | (H (lateIndex n)).infectious = 0}) atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      (countsFullLaw (rate n) n).real {H | (H (lateIndex n)).infectious = 0} ≤
      (countsFullLaw (rate n) n).real {H | ∃ k ≤ 2 * n,
        ((1 : ℝ) / 4) * n ≤ |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    rintro H hH
    change (H (lateIndex n)).infectious = 0 at hH
    refine ⟨lateIndex n, (lateIndex_bounds n).2, ?_⟩
    have htri : n ≤ 2 * min (lateIndex n) (2 * n - lateIndex n) := by
      unfold lateIndex
      omega
    have htriR : (n : ℝ) ≤ 2 * (min (lateIndex n) (2 * n - lateIndex n) : ℕ) := by
      exact_mod_cast htri
    simp only [hH, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ (min (lateIndex n) (2 * n - lateIndex n) : ℕ) by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound
    (countsFullLaw_triangle_tendsto_zero rate hstrong (by norm_num : (0 : ℝ) < 1 / 4))

/-- On a decreasing susceptible history, a large late infection probability
forces a large consumption over the whole preceding interval. -/
theorem susceptible_interval_pressure_bound (rate : ℝ≥0) (n a b : ℕ) (hab : a ≤ b)
    (U : ℕ → ℕ) (hmono : Antitone U) {eps : ℝ}
    (hprob : eps ≤ (infectionProbability rate (U b) : ℝ)) :
    (b - a : ℕ) * eps ≤ (U a : ℝ) +
      |Susceptible.noise rate n U b| + |Susceptible.noise rate n U a| := by
  let f : ℕ → ℝ := fun i => (infectionProbability rate (U i) : ℝ)
  have hsum : (b - a : ℕ) * eps ≤ ∑ i ∈ Finset.Ico a b, f i := by
    calc
      _ = ∑ _i ∈ Finset.Ico a b, eps := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hib : i ≤ b := (Finset.mem_Ico.mp hi).2.le
        exact hprob.trans (by exact_mod_cast infectionProbability_mono_susceptible rate (hmono hib))
  have hsplit : (∑ i ∈ Finset.range b, f i) =
      (∑ i ∈ Finset.range a, f i) + ∑ i ∈ Finset.Ico a b, f i := by
    exact (Finset.sum_range_add_sum_Ico f hab).symm
  have he : (∑ i ∈ Finset.Ico a b, f i) =
      (U a : ℝ) - U b + Susceptible.noise rate n U b - Susceptible.noise rate n U a := by
    unfold Susceptible.noise
    change _ = (U a : ℝ) - U b + ((U b : ℝ) - n + ∑ i ∈ Finset.range b, f i) -
      ((U a : ℝ) - n + ∑ i ∈ Finset.range a, f i)
    rw [hsplit]
    ring
  rw [he] at hsum
  have hb0 : (0 : ℝ) ≤ U b := by positivity
  have hMb := le_abs_self (Susceptible.noise rate n U b)
  have hMa := neg_le_abs (Susceptible.noise rate n U a)
  linarith

theorem coupled_counts_event_real (rate : ℝ≥0) (n : ℕ) (A : Set (ℕ → Counts))
    (hA : MeasurableSet A) :
    (StoppedCoupling.fullLaw rate n).real {H | (fun k => (H k).1) ∈ A} =
      (countsFullLaw rate n).real A := by
  unfold Measure.real
  congr 1
  rw [← StoppedCoupling.map_fullLaw_counts rate n]
  have hm : Measurable (fun H : ℕ → StoppedCoupling.State => fun k => (H k).1) :=
    measurable_pi_iff.mpr fun k => measurable_fst.comp (measurable_pi_apply k)
  rw [Measure.map_apply hm hA]
  rfl

theorem coupled_unstopped_event_real (rate : ℝ≥0) (n : ℕ) (A : Set (ℕ → ℕ))
    (hA : MeasurableSet A) :
    (StoppedCoupling.fullLaw rate n).real {H | (fun k => (H k).2) ∈ A} =
      (Susceptible.fullLaw rate n).real A := by
  unfold Measure.real
  congr 1
  rw [← StoppedCoupling.map_fullLaw_unstopped rate n]
  have hm : Measurable (fun H : ℕ → StoppedCoupling.State => fun k => (H k).2) :=
    measurable_pi_iff.mpr fun k => measurable_snd.comp (measurable_pi_apply k)
  rw [Measure.map_apply hm hA]
  rfl

theorem coupled_unstopped_antitone (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂StoppedCoupling.fullLaw rate n, Antitone (fun k => (H k).2) := by
  have hh := Susceptible.fullLaw_antitone rate n
  rw [← StoppedCoupling.map_fullLaw_unstopped rate n] at hh
  have hm : Measurable (fun H : ℕ → StoppedCoupling.State => fun k => (H k).2) :=
    measurable_pi_iff.mpr fun k => measurable_snd.comp (measurable_pi_apply k)
  exact ae_of_ae_map hm.aemeasurable hh

/-- A quantitative event inclusion under the actual coupling. A large late
infection probability forces either a large remaining susceptible count at
population time, early extinction, or a large actual centered noise. -/
theorem coupled_late_probability_bound (rate : ℝ≥0) {n : ℕ} (hn : 2 ≤ n)
    {eps : ℝ} (heps : 0 < eps) :
    (StoppedCoupling.fullLaw rate n).real
      {H | eps ≤ (infectionProbability rate (H (lateIndex n)).1.susceptible : ℝ)} ≤
      (countsFullLaw rate n).real {H | (eps / 16) * n ≤ (H n).susceptible} +
      (countsFullLaw rate n).real {H | (H (lateIndex n)).infectious = 0} +
      (Susceptible.fullLaw rate n).real {U | ∃ k ≤ 2 * n,
        (eps / 16) * n ≤ |Susceptible.noise rate n U k|} := by
  let A : Set (ℕ → StoppedCoupling.State) := {H | (eps / 16) * n ≤ (H n).1.susceptible}
  let B : Set (ℕ → StoppedCoupling.State) := {H | (H (lateIndex n)).1.infectious = 0}
  let C : Set (ℕ → StoppedCoupling.State) := {H | ∃ k ≤ 2 * n,
    (eps / 16) * n ≤ |Susceptible.noise rate n (fun j => (H j).2) k|}
  have hsub :
      (StoppedCoupling.fullLaw rate n).real
        {H | eps ≤ (infectionProbability rate (H (lateIndex n)).1.susceptible : ℝ)} ≤
      (StoppedCoupling.fullLaw rate n).real (A ∪ B ∪ C) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [StoppedCoupling.fullLaw_counts_legal rate n,
      StoppedCoupling.fullLaw_compatible rate n, coupled_unstopped_antitone rate n] with H hl hc hmono hp
    by_contra hbad
    have hA : ((H n).1.susceptible : ℝ) < (eps / 16) * n := by
      have : H ∉ A := by intro hh; exact hbad (Or.inl (Or.inl hh))
      exact not_le.mp this
    have hB : 0 < (H (lateIndex n)).1.infectious := by
      have : H ∉ B := by intro hh; exact hbad (Or.inl (Or.inr hh))
      change ¬(H (lateIndex n)).1.infectious = 0 at this
      omega
    have hC : ∀ k ≤ 2 * n,
        |Susceptible.noise rate n (fun j => (H j).2) k| < (eps / 16) * n := by
      have : H ∉ C := by intro hh; exact hbad (Or.inr hh)
      simpa only [C, mem_ofPred_eq, not_exists, not_and, not_le] using this
    have hi : 0 < (H n).1.infectious := by
      by_contra hh
      have hz : (H n).1.infectious = 0 := by omega
      have he := legalHistory_absorbed_persists hl hz (lateIndex n) (lateIndex_bounds n).1
      rw [he, hz] at hB
      omega
    have hun : ((H n).2 : ℝ) < (eps / 16) * n := by
      rw [← hc n hi]
      exact hA
    have hprob : eps ≤ (infectionProbability rate (H (lateIndex n)).2 : ℝ) := by
      rw [← hc (lateIndex n) hB]
      exact hp
    have hh := susceptible_interval_pressure_bound rate n n (lateIndex n)
      (lateIndex_bounds n).1 (fun j => (H j).2) hmono hprob
    rw [show lateIndex n - n = n / 2 by unfold lateIndex; omega] at hh
    have hMn := hC n (by omega)
    have hMm := hC (lateIndex n) (lateIndex_bounds n).2
    have hlength : (n : ℝ) ≤ 4 * (n / 2 : ℕ) := by
      exact_mod_cast (show n ≤ 4 * (n / 2) by omega)
    have hlower := mul_le_mul_of_nonneg_right hlength heps.le
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    nlinarith only [hh, hun, hMn, hMm, hlower, mul_pos heps hnR]
  have hAeq : (StoppedCoupling.fullLaw rate n).real A =
      (countsFullLaw rate n).real {H | (eps / 16) * n ≤ (H n).susceptible} :=
    by
      simpa only [A, mem_ofPred_eq] using (coupled_counts_event_real rate n
        {H : ℕ → Counts | (eps / 16) * n ≤ (H n).susceptible}
        ((Set.to_countable {c : Counts | (eps / 16) * n ≤ (c.susceptible : ℝ)}).measurableSet.preimage
          (measurable_pi_apply n)))
  have hBeq : (StoppedCoupling.fullLaw rate n).real B =
      (countsFullLaw rate n).real {H | (H (lateIndex n)).infectious = 0} :=
    by
      simpa only [B, mem_ofPred_eq] using (coupled_counts_event_real rate n
        {H : ℕ → Counts | (H (lateIndex n)).infectious = 0}
        ((Set.to_countable {c : Counts | c.infectious = 0}).measurableSet.preimage
          (measurable_pi_apply (lateIndex n))))
  have hCeq : (StoppedCoupling.fullLaw rate n).real C =
      (Susceptible.fullLaw rate n).real {U | ∃ k ≤ 2 * n,
        (eps / 16) * n ≤ |Susceptible.noise rate n U k|} :=
    by
      simpa only [C, mem_ofPred_eq] using (coupled_unstopped_event_real rate n
        {U : ℕ → ℕ | ∃ k ≤ 2 * n, (eps / 16) * n ≤ |Susceptible.noise rate n U k|}
        (by
          simp only [ofPred_exists]
          apply MeasurableSet.iUnion
          intro k
          by_cases hk : k ≤ 2 * n
          · simp only [hk, true_and]
            exact measurableSet_le measurable_const (continuous_abs.measurable.comp (Susceptible.noise_measurable rate n k))
          · simp only [hk, false_and, ofPred_false]
            exact MeasurableSet.empty))
  calc
    _ ≤ (StoppedCoupling.fullLaw rate n).real (A ∪ B ∪ C) := hsub
    _ ≤ ((StoppedCoupling.fullLaw rate n).real A + (StoppedCoupling.fullLaw rate n).real B) +
        (StoppedCoupling.fullLaw rate n).real C :=
      (measureReal_union_le (A ∪ B) C).trans
        (add_le_add_left (measureReal_union_le A B) _)
    _ = _ := by rw [hAeq, hBeq, hCeq]

/-- Actual late infection probabilities vanish in the strong-infection
regime, without a reverse-time domination assumption. -/
theorem countsFullLaw_late_infection_probability_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | eps ≤ (infectionProbability (rate n) (H (lateIndex n)).susceptible : ℝ)})
      atTop (𝓝 0) := by
  have hnoise : Tendsto (fun n : ℕ => (Susceptible.fullLaw (rate n) n).real
      {U | ∃ k ≤ 2 * n, (eps / 16) * n ≤ |Susceptible.noise (rate n) n U k|})
      atTop (𝓝 0) := by
    have hh := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (Susceptible.noise_uniform_div_population_tendsto rate 2 (by positivity : 0 < eps / 16))
    simpa only [Measure.real, Function.comp_def, ENNReal.toReal_zero, Nat.mul_comm] using hh
  have hsum := ((countsFullLaw_susceptible_at_population_tendsto_zero rate hstrong
    (by positivity : 0 < eps / 16)).add (countsFullLaw_late_extinction_tendsto_zero rate hstrong)).add hnoise
  simp only [add_zero] at hsum
  have hbound : ∀ᶠ n : ℕ in atTop,
      (countsFullLaw (rate n) n).real
        {H | eps ≤ (infectionProbability (rate n) (H (lateIndex n)).susceptible : ℝ)} ≤
      (countsFullLaw (rate n) n).real {H | (eps / 16) * n ≤ (H n).susceptible} +
      (countsFullLaw (rate n) n).real {H | (H (lateIndex n)).infectious = 0} +
      (Susceptible.fullLaw (rate n) n).real {U | ∃ k ≤ 2 * n,
        (eps / 16) * n ≤ |Susceptible.noise (rate n) n U k|} := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have heq : (countsFullLaw (rate n) n).real
        {H | eps ≤ (infectionProbability (rate n) (H (lateIndex n)).susceptible : ℝ)} =
      (StoppedCoupling.fullLaw (rate n) n).real
        {H | eps ≤ (infectionProbability (rate n) (H (lateIndex n)).1.susceptible : ℝ)} := by
      simpa only [mem_ofPred_eq] using (coupled_counts_event_real (rate n) n
        {H : ℕ → Counts | eps ≤ (infectionProbability (rate n) (H (lateIndex n)).susceptible : ℝ)}
        ((Set.to_countable {c : Counts | eps ≤ (infectionProbability (rate n) c.susceptible : ℝ)}).measurableSet.preimage
          (measurable_pi_apply (lateIndex n)))).symm
    rw [heq]
    exact coupled_late_probability_bound (rate n) hn heps
  exact squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound hsum

theorem lateIndex_eq_floor (n : ℕ) : lateIndex n = ⌊((3 : ℝ) / 2) * n⌋₊ := by
  symm
  apply (Nat.floor_eq_iff (by positivity : 0 ≤ ((3 : ℝ) / 2) * n)).mpr
  have hl : 2 * lateIndex n ≤ 3 * n := by unfold lateIndex; omega
  have hr : 3 * n < 2 * (lateIndex n + 1) := by unfold lateIndex; omega
  have hlR : (2 : ℝ) * lateIndex n ≤ 3 * n := by exact_mod_cast hl
  have hrR : (3 : ℝ) * n < 2 * ((lateIndex n : ℝ) + 1) := by exact_mod_cast hr
  constructor <;> linarith

theorem legalHistory_susceptible_antitone {H : ℕ → Counts}
    (hl : ∀ k, (H k).LegalNext (H (k + 1))) : Antitone (fun k => (H k).susceptible) :=
  antitone_nat_of_succ_le fun k => (hl k).susceptible_le

/-- Uniformity over the entire late future follows from the actual
susceptible monotonicity, even after infectious absorption. -/
theorem countsFullLaw_late_infection_uniform_event_eq (rate : ℝ≥0) (n : ℕ) (eps : ℝ) :
    (countsFullLaw rate n).real {H | ∃ k ≥ lateIndex n,
      eps ≤ (infectionProbability rate (H k).susceptible : ℝ)} =
    (countsFullLaw rate n).real {H |
      eps ≤ (infectionProbability rate (H (lateIndex n)).susceptible : ℝ)} := by
  unfold Measure.real
  congr 1
  apply measure_congr
  filter_upwards [countsFullLaw_legal rate n] with H hl
  have hm := legalHistory_susceptible_antitone hl
  apply propext
  constructor
  · rintro ⟨k, hk, he⟩
    exact he.trans (by exact_mod_cast infectionProbability_mono_susceptible rate (hm hk))
  · intro he
    exact ⟨lateIndex n, le_rfl, he⟩

theorem countsFullLaw_late_infection_probability_uniform_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real {H | ∃ k ≥ lateIndex n,
      eps ≤ (infectionProbability (rate n) (H k).susceptible : ℝ)}) atTop (𝓝 0) := by
  apply (countsFullLaw_late_infection_probability_tendsto_zero rate hstrong heps).congr
  intro n
  exact (countsFullLaw_late_infection_uniform_event_eq (rate n) n eps).symm

/-- A83 with the literal real-time floor and rational transition formula. -/
theorem countsFullLaw_infection_pressure_after_three_halves_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real {H |
      ∃ k ≥ ⌊((3 : ℝ) / 2) * n⌋₊,
        eps ≤ (rate n : ℝ) * (H k).susceptible / (1 + (rate n : ℝ) * (H k).susceptible)})
      atTop (𝓝 0) := by
  simpa only [lateIndex_eq_floor, infectionProbability_coe] using
    countsFullLaw_late_infection_probability_uniform_tendsto_zero rate hstrong heps

end Freezing1.SIR
