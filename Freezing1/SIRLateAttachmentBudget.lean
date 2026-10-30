module

public import Freezing1.SIRLateReciprocalBudget

/-!
# A forward expected budget for late attachment charges

The cost detects actual susceptible-consuming transitions. The harmonic
potential controls its accumulated sum from the actual Markov law; no
reverse-time independence or future-conditioned coupling is assumed.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable def birthCharge (c d : Counts) : ℝ :=
  if d.susceptible < c.susceptible then 1 / (c.infectious : ℝ) else 0

theorem birthCharge_nonneg (c d : Counts) : 0 ≤ birthCharge c d := by
  unfold birthCharge
  split_ifs <;> positivity

theorem countsKernel_integral_birthCharge (rate : ℝ≥0) (c : Counts) :
    (∫ d, birthCharge c d ∂countsKernel rate c) =
      (infectionProbability rate c.susceptible : ℝ) / c.infectious := by
  by_cases hi : c.infectious = 0
  · rw [countsKernel_absorbed rate hi]
    simp [birthCharge, hi]
  · have hi0 : 0 < c.infectious := by omega
    by_cases hu : c.susceptible = 0
    · rw [countsKernel_zero_susceptible rate hi0 hu]
      simp [birthCharge, recoverCounts, hu]
    · rw [countsKernel_integral_split rate hi0]
      have hd : c.susceptible - 1 < c.susceptible := by omega
      simp only [birthCharge, infectCounts, recoverCounts, ite_eq_left hd,
        lt_self_iff_false, ite_false, mul_zero, add_zero]
      ring

noncomputable def birthHistoryCharge (H : ℕ → Counts) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, birthCharge (H i) (H (i + 1))

theorem birthHistoryCharge_nonneg (H : ℕ → Counts) (k : ℕ) :
    0 ≤ birthHistoryCharge H k :=
  Finset.sum_nonneg fun _ _ => birthCharge_nonneg _ _

@[fun_prop] theorem measurable_birthHistoryCharge (k : ℕ) :
    Measurable (fun H : ℕ → Counts => birthHistoryCharge H k) := by
  unfold birthHistoryCharge
  apply Finset.measurable_sum
  intro i _
  exact (measurable_of_countable (fun q : Counts × Counts => birthCharge q.1 q.2)).comp
    (show Measurable (fun H : ℕ → Counts => (H i, H (i + 1))) by fun_prop)

noncomputable def birthBudgetCoefficient (eps : ℝ) : ℝ := eps / (1 - 2 * eps)

theorem birthBudgetCoefficient_nonneg {eps : ℝ} (heps0 : 0 ≤ eps) (heps : eps < 1 / 2) :
    0 ≤ birthBudgetCoefficient eps := div_nonneg heps0 (by linarith)

theorem countsKernel_birth_harmonic_budget (rate : ℝ≥0) (c : Counts) {eps : ℝ}
    (heps0 : 0 ≤ eps) (heps : eps < 1 / 2)
    (hp : (infectionProbability rate c.susceptible : ℝ) ≤ eps) :
    (∫ d, birthCharge c d ∂countsKernel rate c) +
      birthBudgetCoefficient eps * (∫ d, harmonicPopulation d ∂countsKernel rate c) ≤
        birthBudgetCoefficient eps * harmonicPopulation c := by
  have hcoef := birthBudgetCoefficient_nonneg heps0 heps
  have hd : 1 - 2 * eps ≠ 0 := by linarith
  have hh := mul_le_mul_of_nonneg_left
    (countsKernel_harmonic_reciprocal_bound rate c hp) hcoef
  have he : birthBudgetCoefficient eps * ((1 - 2 * eps) / (c.infectious : ℝ)) =
      eps / c.infectious := by
    rw [show birthBudgetCoefficient eps * ((1 - 2 * eps) / (c.infectious : ℝ)) =
      (birthBudgetCoefficient eps * (1 - 2 * eps)) / c.infectious by ring]
    rw [birthBudgetCoefficient, div_mul_cancel₀ _ hd]
  rw [mul_add, he] at hh
  rw [countsKernel_integral_birthCharge]
  have hm := div_le_div_of_nonneg_right hp (Nat.cast_nonneg c.infectious : (0 : ℝ) ≤ c.infectious)
  linarith

noncomputable def birthBudgetUpdate (a : ℝ × Counts) (d : Counts) : ℝ × Counts :=
  (a.1 + birthCharge a.2 d, d)

noncomputable def birthBudgetPotential (eps : ℝ) (a : ℝ × Counts) (c : Counts) : ℝ≥0∞ :=
  ENNReal.ofReal (a.1 + birthBudgetCoefficient eps * harmonicPopulation c)

theorem accumulate_birthBudget {H : ℕ → Counts} {c : Counts} (h0 : H 0 = c) (k : ℕ) :
    CountableMarkovChain.accumulate ((0 : ℝ), c) birthBudgetUpdate H k =
      (birthHistoryCharge H k, H k) := by
  induction k with
  | zero => simp [CountableMarkovChain.accumulate_zero, birthHistoryCharge, h0]
  | succ k ih =>
    rw [CountableMarkovChain.accumulate_succ, ih]
    simp [birthBudgetUpdate, birthHistoryCharge, Finset.sum_range_succ]

theorem countsKernel_accumulated_birth_budget (rate : ℝ≥0) (c : Counts)
    {eps a : ℝ} (heps0 : 0 ≤ eps) (heps : eps < 1 / 2) (ha : 0 ≤ a)
    (hp : (infectionProbability rate c.susceptible : ℝ) ≤ eps) :
    (∫⁻ d, birthBudgetPotential eps (birthBudgetUpdate (a, c) d) d ∂countsKernel rate c) ≤
      birthBudgetPotential eps (a, c) c := by
  let f : Counts → ℝ := fun d => a + birthCharge c d +
    birthBudgetCoefficient eps * harmonicPopulation d
  have hf : Integrable f (countsKernel rate c) := countsKernel_integrable rate c f
  have hf0 : ∀ d, 0 ≤ f d := by
    intro d
    exact add_nonneg (add_nonneg ha (birthCharge_nonneg c d))
      (mul_nonneg (birthBudgetCoefficient_nonneg heps0 heps) (harmonicPopulation_nonneg d))
  have hreal : (∫ d, f d ∂countsKernel rate c) ≤ a +
      birthBudgetCoefficient eps * harmonicPopulation c := by
    dsimp only [f]
    rw [integral_add (countsKernel_integrable rate c _) (countsKernel_integrable rate c _),
      integral_add (integrable_const a) (countsKernel_integrable rate c _), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    have hh := countsKernel_birth_harmonic_budget rate c heps0 heps hp
    linarith
  have hh := ENNReal.ofReal_le_ofReal hreal
  rw [ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf0)] at hh
  exact hh

/-- An actual forward expected attachment-charge bound, uniform in the
future horizon and valid from every starting state with small infection
probability. -/
theorem countsPath_lintegral_birthHistoryCharge_le (rate : ℝ≥0) (c : Counts)
    {eps : ℝ} (heps : eps < 1 / 2)
    (hp : (infectionProbability rate c.susceptible : ℝ) ≤ eps) (k : ℕ) :
    (∫⁻ H, ENNReal.ofReal (birthHistoryCharge H k)
      ∂CountableMarkovChain.fullLaw (countsKernel rate) c) ≤
        ENNReal.ofReal (birthBudgetCoefficient eps * harmonicPopulation c) := by
  have heps0 : 0 ≤ eps := (infectionProbability rate c.susceptible).property.1.trans hp
  have hbudget := CountableMarkovChain.lintegral_accumulate_of_superharmonic
    (countsKernel rate) c ((0 : ℝ), c) birthBudgetUpdate
    (birthBudgetPotential eps) (fun j => ?_) k
  · calc
      _ ≤ ∫⁻ H, birthBudgetPotential eps
          (CountableMarkovChain.accumulate ((0 : ℝ), c) birthBudgetUpdate H k) (H k)
          ∂CountableMarkovChain.fullLaw (countsKernel rate) c := by
        apply lintegral_mono_ae
        filter_upwards [CountableMarkovChain.fullLaw_initial (countsKernel rate) c] with H h0
        rw [accumulate_birthBudget h0]
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_nonneg (birthBudgetCoefficient_nonneg heps0 heps)
          (harmonicPopulation_nonneg (H k))
        exact le_add_of_nonneg_right hh
      _ ≤ _ := by simpa [birthBudgetPotential] using hbudget
  · filter_upwards [CountableMarkovChain.fullLaw_initial (countsKernel rate) c,
      countsPath_susceptible_le_initial rate c] with H h0 hu
    rw [accumulate_birthBudget h0]
    apply countsKernel_accumulated_birth_budget rate (H j) heps0 heps
    · exact birthHistoryCharge_nonneg H j
    · have hm : (infectionProbability rate (H j).susceptible : ℝ) ≤
          (infectionProbability rate c.susceptible : ℝ) := by
        exact_mod_cast infectionProbability_mono_susceptible rate (hu j)
      exact hm.trans hp

end Freezing1.SIR
