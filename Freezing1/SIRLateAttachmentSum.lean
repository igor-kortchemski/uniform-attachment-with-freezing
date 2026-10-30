module

public import Freezing1.SIRLateAttachmentBudget
public import Freezing1.SIRLateInfectionProbability
public import Freezing1.CountableMarkovShift

/-!
# Forward late attachment charges after a deterministic observation time

The future is integrated with its proved conditional Markov law. The small
infection event is measured at the starting time, rather than by conditioning
on future events or reversing the history.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology BigOperators

set_option backward.isDefEq.respectTransparency false

theorem countsFullLaw_lintegral_future (rate : ℝ≥0) (n a : ℕ)
    (F : Counts → (ℕ → Counts) → ℝ≥0∞) (hF : Measurable (Function.uncurry F)) :
    (∫⁻ H, F (H a) (CountableMarkovChain.shift a H) ∂countsFullLaw rate n) =
      ∫⁻ H, ∫⁻ U, F (H a) U ∂CountableMarkovChain.fullLaw (countsKernel rate) (H a)
        ∂countsFullLaw rate n := by
  let G : CountableMarkovChain.Prefix (E := Counts) a × (ℕ → Counts) → ℝ≥0∞ := fun q =>
    F (q.1 ⟨a, Finset.mem_Iic.mpr le_rfl⟩) q.2
  have hG : Measurable G := hF.comp
    (((measurable_of_countable (fun P : CountableMarkovChain.Prefix (E := Counts) a =>
      P ⟨a, Finset.mem_Iic.mpr le_rfl⟩)).comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun H : ℕ → Counts =>
      (Preorder.frestrictLe a H, CountableMarkovChain.shift a H)) := by fun_prop
  calc
    _ = ∫⁻ q, G q ∂(countsFullLaw rate n).map
        (fun H => (Preorder.frestrictLe a H, CountableMarkovChain.shift a H)) := by
      rw [lintegral_map hG hm]
      rfl
    _ = ∫⁻ q, G q ∂((countsFullLaw rate n).map (Preorder.frestrictLe a)) ⊗ₘ
        CountableMarkovChain.futureKernel (countsKernel rate) a := by
      rw [countsFullLaw, CountableMarkovChain.map_prefix_shift]
    _ = ∫⁻ P, ∫⁻ U, G (P, U) ∂CountableMarkovChain.futureKernel (countsKernel rate) a P
        ∂(countsFullLaw rate n).map (Preorder.frestrictLe a) := by
      rw [Measure.lintegral_compProd hG]
    _ = _ := by
      let J : Counts → ℝ≥0∞ := fun c =>
        ∫⁻ U, F c U ∂CountableMarkovChain.fullLaw (countsKernel rate) c
      change (∫⁻ P, J (P ⟨a, Finset.mem_Iic.mpr le_rfl⟩)
        ∂(countsFullLaw rate n).map (Preorder.frestrictLe a)) = _
      have hJ : Measurable (fun P : CountableMarkovChain.Prefix (E := Counts) a =>
          J (P ⟨a, Finset.mem_Iic.mpr le_rfl⟩)) :=
        (measurable_of_countable J).comp (by fun_prop)
      exact lintegral_map hJ (show Measurable (Preorder.frestrictLe (π := fun _ : ℕ => Counts) a) by fun_prop)

theorem harmonicPopulation_le_of_infectious_le {c : Counts} {b : ℕ}
    (hcb : c.infectious ≤ b) : harmonicPopulation c ≤ (harmonic b : ℝ) := by
  have hm : Monotone (fun k : ℕ => (harmonic k : ℝ)) := by
    apply monotone_nat_of_le_succ
    intro k
    rw [harmonic_real_succ]
    have hh : 0 ≤ (1 : ℝ) / (k + 1 : ℝ) := by positivity
    linarith
  exact hm hcb

/-- The future attachment budget may be restricted by the actual starting
infection probability. This is a past-measurable restriction. -/
theorem countsFullLaw_masked_future_birth_budget (rate : ℝ≥0) (n a K : ℕ)
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps : eps < 1 / 2) :
    (∫⁻ H, if (infectionProbability rate (H a).susceptible : ℝ) ≤ eps then
      ENNReal.ofReal (birthHistoryCharge (CountableMarkovChain.shift a H) K) else 0
      ∂countsFullLaw rate n) ≤
        ENNReal.ofReal (birthBudgetCoefficient eps * (harmonic (n + 1) : ℝ)) := by
  let F : Counts → (ℕ → Counts) → ℝ≥0∞ := fun c U =>
    if (infectionProbability rate c.susceptible : ℝ) ≤ eps then
      ENNReal.ofReal (birthHistoryCharge U K) else 0
  have hF : Measurable (Function.uncurry F) := by
    apply Measurable.ite
    · exact (Set.to_countable {c : Counts | (infectionProbability rate c.susceptible : ℝ) ≤ eps}).measurableSet.preimage
        measurable_fst
    · exact (measurable_birthHistoryCharge K).ennreal_ofReal.comp measurable_snd
    · exact measurable_const
  change (∫⁻ H, F (H a) (CountableMarkovChain.shift a H) ∂countsFullLaw rate n) ≤ _
  rw [countsFullLaw_lintegral_future rate n a F hF]
  calc
    _ ≤ ∫⁻ _ : ℕ → Counts,
        ENNReal.ofReal (birthBudgetCoefficient eps * (harmonic (n + 1) : ℝ)) ∂countsFullLaw rate n := by
      apply lintegral_mono_ae
      filter_upwards [countsFullLaw_valid rate n] with H hH
      have hI : (H a).infectious ≤ n + 1 := by have hh := hH a; unfold Counts.Valid at hh; omega
      have hpot := harmonicPopulation_le_of_infectious_le hI
      by_cases hp : (infectionProbability rate (H a).susceptible : ℝ) ≤ eps
      · dsimp only [F]
        simp only [ite_eq_left hp]
        exact (countsPath_lintegral_birthHistoryCharge_le rate (H a) heps hp K).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpot
            (birthBudgetCoefficient_nonneg heps0 heps)))
      · simp only [F, ite_eq_right hp, lintegral_zero]
        exact zero_le
    _ = _ := by simp

/-- A finite-horizon future charge tail bound with an explicit price for
large infection probability at the starting time. -/
theorem countsFullLaw_future_birth_tail_bound (rate : ℝ≥0) (n a K : ℕ)
    {eps L : ℝ} (heps0 : 0 ≤ eps) (heps : eps < 1 / 2) (hL : 0 < L) :
    countsFullLaw rate n {H | L ≤ birthHistoryCharge (CountableMarkovChain.shift a H) K} ≤
      countsFullLaw rate n {H | eps ≤ (infectionProbability rate (H a).susceptible : ℝ)} +
        ENNReal.ofReal (birthBudgetCoefficient eps * (harmonic (n + 1) : ℝ)) / ENNReal.ofReal L := by
  let X : (ℕ → Counts) → ℝ≥0∞ := fun H =>
    if (infectionProbability rate (H a).susceptible : ℝ) ≤ eps then
      ENNReal.ofReal (birthHistoryCharge (CountableMarkovChain.shift a H) K) else 0
  have hX : Measurable X := by
    apply Measurable.ite
    · exact (Set.to_countable {c : Counts | (infectionProbability rate c.susceptible : ℝ) ≤ eps}).measurableSet.preimage
        (measurable_pi_apply a)
    · exact ((measurable_birthHistoryCharge K).comp (CountableMarkovChain.measurable_shift a)).ennreal_ofReal
    · exact measurable_const
  have hsub : {H : ℕ → Counts | L ≤ birthHistoryCharge (CountableMarkovChain.shift a H) K} ⊆
      {H | eps ≤ (infectionProbability rate (H a).susceptible : ℝ)} ∪
        {H | ENNReal.ofReal L ≤ X H} := by
    intro H hH
    by_cases hp : eps ≤ (infectionProbability rate (H a).susceptible : ℝ)
    · exact Or.inl hp
    · right
      have hp' : (infectionProbability rate (H a).susceptible : ℝ) ≤ eps := (not_le.mp hp).le
      change ENNReal.ofReal L ≤ X H
      dsimp only [X]
      rw [ite_eq_left hp']
      exact ENNReal.ofReal_le_ofReal hH
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ _ + ((∫⁻ H, X H ∂countsFullLaw rate n) / ENNReal.ofReal L) :=
      add_le_add le_rfl (meas_ge_le_lintegral_div hX.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr hL) ENNReal.ofReal_ne_top)
    _ ≤ _ := add_le_add le_rfl (ENNReal.div_le_div_right
      (countsFullLaw_masked_future_birth_budget rate n a K heps0 heps) _)

theorem countsFullLaw_future_birth_tail_real_bound (rate : ℝ≥0) (n a K : ℕ)
    {eps L : ℝ} (heps0 : 0 ≤ eps) (heps : eps < 1 / 2) (hL : 0 < L) :
    (countsFullLaw rate n).real {H | L ≤ birthHistoryCharge (CountableMarkovChain.shift a H) K} ≤
      (countsFullLaw rate n).real {H | eps ≤ (infectionProbability rate (H a).susceptible : ℝ)} +
        birthBudgetCoefficient eps * (harmonic (n + 1) : ℝ) / L := by
  have hH0 : 0 ≤ (harmonic (n + 1) : ℝ) :=
    harmonicPopulation_nonneg ({susceptible := 0, infectious := n + 1} : Counts)
  have hB0 := mul_nonneg (birthBudgetCoefficient_nonneg heps0 heps) hH0
  have hh := ENNReal.toReal_mono (show
      countsFullLaw rate n {H | eps ≤ (infectionProbability rate (H a).susceptible : ℝ)} +
        ENNReal.ofReal (birthBudgetCoefficient eps * (harmonic (n + 1) : ℝ)) / ENNReal.ofReal L ≠ ∞ by
      finiteness) (countsFullLaw_future_birth_tail_bound rate n a K heps0 heps hL)
  rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness), ENNReal.toReal_div,
    ENNReal.toReal_ofReal hB0, ENNReal.toReal_ofReal hL.le] at hh
  exact hh

theorem eventually_harmonic_succ_le_three_log :
    ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n ∧ (harmonic (n + 1) : ℝ) ≤ 3 * Real.log n := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog.eventually_ge_atTop 1] with n hn hnlog
  change 1 ≤ Real.log (n : ℝ) at hnlog
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh := harmonic_le_one_add_log (n + 1)
  have hlogn : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne'] at hlogn
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  exact ⟨hnlog, by nlinarith⟩

/-- The true attachment charge after `floor(3n/2)`, divided by `log n`,
vanishes in probability for arbitrary choices of the future horizon. -/
theorem countsFullLaw_late_birth_charge_over_log_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop) (K : ℕ → ℕ)
    {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | eta * Real.log n ≤ birthHistoryCharge (CountableMarkovChain.shift (lateIndex n) H) (K n)})
      atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le ENNReal.toReal_nonneg
  · intro b hb
    let eps : ℝ := min (1 / 8) (b * eta / 32)
    have heps0 : 0 < eps := lt_min (by norm_num) (by positivity)
    have heps8 : eps ≤ 1 / 8 := min_le_left _ _
    have heps : eps < 1 / 2 := by linarith
    have hcoef : birthBudgetCoefficient eps ≤ 2 * eps := by
      have hd : 1 / 2 ≤ 1 - 2 * eps := by linarith
      have hh := div_le_div_of_nonneg_left heps0.le (by norm_num : (0 : ℝ) < 1 / 2) hd
      have he : eps / ((1 : ℝ) / 2) = 2 * eps := by ring
      rw [he] at hh
      exact hh
    have hsmall : 6 * eps / eta ≤ b / 2 := by
      apply (div_le_iff₀ heta).mpr
      have hh : eps ≤ b * eta / 32 := min_le_right _ _
      nlinarith [mul_pos hb heta]
    have hbad := countsFullLaw_late_infection_probability_tendsto_zero rate hstrong heps0
    filter_upwards [hbad.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < b / 2)),
      eventually_harmonic_succ_le_three_log] with n hn hH
    have hlog0 : 0 < Real.log n := by linarith [hH.1]
    have hH0 : 0 ≤ (harmonic (n + 1) : ℝ) :=
      harmonicPopulation_nonneg ({susceptible := 0, infectious := n + 1} : Counts)
    have hbudget : birthBudgetCoefficient eps * (harmonic (n + 1) : ℝ) / (eta * Real.log n) ≤ b / 2 := by
      calc
        _ ≤ (2 * eps * (3 * Real.log n)) / (eta * Real.log n) :=
          div_le_div_of_nonneg_right (mul_le_mul hcoef hH.2 hH0 (by positivity)) (by positivity)
        _ = 6 * eps / eta := by
          field_simp
          norm_num
        _ ≤ _ := hsmall
    have hh := countsFullLaw_future_birth_tail_real_bound (rate n) n (lateIndex n) (K n)
      heps0.le heps (mul_pos heta hlog0)
    linarith

/-- Multiplying the pre-birth charge by a lower infectious-population bound
is paid for by the actual susceptible decrease. -/
theorem Counts.LegalNext.birthCharge_mul_le_drop {c d : Counts} (hl : c.LegalNext d)
    {B : ℝ} (hI : B ≤ (c.infectious : ℝ)) :
    B * birthCharge c d ≤ (c.susceptible : ℝ) - d.susceptible := by
  rcases hl with ⟨_, rfl⟩ | ⟨hi, ⟨hu, rfl⟩ | rfl⟩
  · simp [birthCharge]
  · have hd : c.susceptible - 1 < c.susceptible := by omega
    have hiR : (0 : ℝ) < c.infectious := by exact_mod_cast hi
    simp only [birthCharge, infectCounts, ite_eq_left hd, Nat.cast_sub (by omega : 1 ≤ c.susceptible), Nat.cast_one]
    have hh := (div_le_one hiR).mpr hI
    simpa only [mul_one_div, sub_sub_cancel] using hh
  · simp [birthCharge, recoverCounts]

theorem birthHistoryCharge_shift_add (H : ℕ → Counts) (a b c : ℕ) :
    birthHistoryCharge (CountableMarkovChain.shift a H) (b + c) =
      birthHistoryCharge (CountableMarkovChain.shift a H) b +
        birthHistoryCharge (CountableMarkovChain.shift (a + b) H) c := by
  unfold birthHistoryCharge
  rw [Finset.sum_range_add]
  simp only [CountableMarkovChain.shift, Nat.add_assoc]

theorem legalHistory_birth_charge_mul_le (H : ℕ → Counts)
    (hl : ∀ k, (H k).LegalNext (H (k + 1))) (a K : ℕ) {B : ℝ}
    (hI : ∀ i < K, B ≤ ((H (a + i)).infectious : ℝ)) :
    B * birthHistoryCharge (CountableMarkovChain.shift a H) K ≤ (H a).susceptible := by
  have haux : ∀ K : ℕ, (∀ i < K, B ≤ ((H (a + i)).infectious : ℝ)) →
      B * birthHistoryCharge (CountableMarkovChain.shift a H) K + (H (a + K)).susceptible ≤
        (H a).susceptible := by
    intro k
    induction k with
    | zero => simp [birthHistoryCharge]
    | succ k ih =>
      intro hI
      have hp := ih (fun i hi => hI i (by omega))
      have hs := (hl (a + k)).birthCharge_mul_le_drop (hI k (by omega))
      have he : birthHistoryCharge (CountableMarkovChain.shift a H) (k + 1) =
          birthHistoryCharge (CountableMarkovChain.shift a H) k +
            birthCharge (H (a + k)) (H (a + k + 1)) := by
        simp [birthHistoryCharge, Finset.sum_range_succ, CountableMarkovChain.shift, Nat.add_assoc]
      rw [he]
      simp only [Nat.add_assoc] at hs ⊢
      nlinarith
  exact (le_add_of_nonneg_right (Nat.cast_nonneg (H (a + K)).susceptible)).trans (haux K hI)

/-- The whole middle interval charge is negligible without a logarithmic
normalization. It is bounded by the remaining susceptible fraction. -/
theorem countsFullLaw_middle_birth_charge_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop) {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | eta ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n / 2)}) atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      (countsFullLaw (rate n) n).real
        {H | eta ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n / 2)} ≤
      (countsFullLaw (rate n) n).real {H | ∃ k ≤ 2 * n,
        ((1 : ℝ) / 8) * n ≤ |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|} +
      (countsFullLaw (rate n) n).real {H | (eta / 4) * n ≤ (H n).susceptible} := by
    have hsub :
        (countsFullLaw (rate n) n).real
          {H | eta ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n / 2)} ≤
        (countsFullLaw (rate n) n).real
          ({H | ∃ k ≤ 2 * n, ((1 : ℝ) / 8) * n ≤
            |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|} ∪
           {H | (eta / 4) * n ≤ (H n).susceptible}) := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono_ae
      filter_upwards [countsFullLaw_legal (rate n) n] with H hl hbad
      by_cases hgrid : ∃ k ≤ 2 * n, ((1 : ℝ) / 8) * n ≤
          |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|
      · exact Or.inl hgrid
      · right
        change (eta / 4) * (n : ℝ) ≤ (H n).susceptible
        have hgood : ∀ k ≤ 2 * n,
            |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)| < ((1 : ℝ) / 8) * n := by
          simpa only [not_exists, not_and, not_le] using hgrid
        have hI : ∀ i < n / 2, (n : ℝ) / 4 ≤ ((H (n + i)).infectious : ℝ) := by
          intro i hi
          have hk : n + i ≤ 2 * n := by omega
          have ht : n ≤ 2 * min (n + i) (2 * n - (n + i)) := by omega
          have htR : (n : ℝ) ≤ 2 * (min (n + i) (2 * n - (n + i)) : ℕ) := by exact_mod_cast ht
          have hh := (abs_lt.mp (hgood (n + i) hk)).1
          nlinarith
        have hh := legalHistory_birth_charge_mul_le H hl n (n / 2) hI
        have hm := mul_le_mul_of_nonneg_left hbad (show 0 ≤ (n : ℝ) / 4 by positivity)
        nlinarith
    exact hsub.trans (measureReal_union_le _ _)
  have hsum := (countsFullLaw_triangle_tendsto_zero rate hstrong
    (by norm_num : (0 : ℝ) < 1 / 8)).add
      (countsFullLaw_susceptible_at_population_tendsto_zero rate hstrong (by positivity : 0 < eta / 4))
  simp only [add_zero] at hsum
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound hsum

theorem countsFullLaw_middle_birth_charge_over_log_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop) {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | eta * Real.log n ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n / 2)})
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      (countsFullLaw (rate n) n).real
        {H | eta * Real.log n ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n / 2)} ≤
      (countsFullLaw (rate n) n).real
        {H | eta ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n / 2)} := by
    filter_upwards [eventually_harmonic_succ_le_three_log] with n hn
    apply measureReal_mono _ (measure_ne_top _ _)
    intro H hH
    change eta * Real.log n ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n / 2) at hH
    change eta ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n / 2)
    have hh := mul_le_mul_of_nonneg_left hn.1 heta.le
    linarith
  exact squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound
    (countsFullLaw_middle_birth_charge_tendsto_zero rate hstrong heta)

/-- All attachment charges from event time `n` through the proved terminal
horizon are `o(log n)` in probability under the actual stopped law. -/
theorem countsFullLaw_post_population_birth_charge_over_log_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop) {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | eta * Real.log n ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n + 1)})
      atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      (countsFullLaw (rate n) n).real
        {H | eta * Real.log n ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n + 1)} ≤
      (countsFullLaw (rate n) n).real
        {H | (eta / 2) * Real.log n ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n / 2)} +
      (countsFullLaw (rate n) n).real
        {H | (eta / 2) * Real.log n ≤
          birthHistoryCharge (CountableMarkovChain.shift (lateIndex n) H) (n + 1 - n / 2)} := by
    have hsub :
        {H : ℕ → Counts | eta * Real.log n ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n + 1)} ⊆
        {H | (eta / 2) * Real.log n ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n / 2)} ∪
        {H | (eta / 2) * Real.log n ≤
          birthHistoryCharge (CountableMarkovChain.shift (lateIndex n) H) (n + 1 - n / 2)} := by
      intro H hH
      have hs := birthHistoryCharge_shift_add H n (n / 2) (n + 1 - n / 2)
      rw [show n / 2 + (n + 1 - n / 2) = n + 1 by omega] at hs
      change birthHistoryCharge (CountableMarkovChain.shift n H) (n + 1) =
        birthHistoryCharge (CountableMarkovChain.shift n H) (n / 2) +
        birthHistoryCharge (CountableMarkovChain.shift (lateIndex n) H) (n + 1 - n / 2) at hs
      by_contra hh
      simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hh
      change eta * Real.log n ≤ birthHistoryCharge (CountableMarkovChain.shift n H) (n + 1) at hH
      linarith [hh.1, hh.2]
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  have hsum := (countsFullLaw_middle_birth_charge_over_log_tendsto_zero rate hstrong
    (by positivity : 0 < eta / 2)).add
      (countsFullLaw_late_birth_charge_over_log_tendsto_zero rate hstrong
        (fun n => n + 1 - n / 2) (by positivity : 0 < eta / 2))
  simp only [add_zero] at hsum
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound hsum

/-- The post-birth reciprocal used by the height scale is dominated by the
pre-birth charge controlled above, on every actual legal transition. -/
theorem Counts.LegalNext.post_birth_reciprocal_le {c d : Counts} (hl : c.LegalNext d) :
    (if d.susceptible < c.susceptible then 1 / (d.infectious : ℝ) else 0) ≤ birthCharge c d := by
  rcases hl with ⟨_, rfl⟩ | ⟨hi, ⟨hu, rfl⟩ | rfl⟩
  · simp [birthCharge]
  · have hd : c.susceptible - 1 < c.susceptible := by omega
    have hiR : (0 : ℝ) < c.infectious := by exact_mod_cast hi
    simp only [infectCounts, birthCharge, ite_eq_left hd, Nat.cast_add, Nat.cast_one]
    exact one_div_le_one_div_of_le hiR (by linarith)
  · simp [birthCharge, recoverCounts]

end Freezing1.SIR
