module

public import Freezing1.SIRCountLaw
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A forward harmonic potential for the late epidemic

When infection probability is small, harmonic infectious population has a
negative drift controlling reciprocal population sums. This is a forward
kernel estimate; it does not reverse a path conditioned on extinction.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Classical

theorem countsKernel_integral_split (rate : ℝ≥0) {c : Counts} (hi : 0 < c.infectious)
    (f : Counts → ℝ) :
    (∫ d, f d ∂countsKernel rate c) =
      (infectionProbability rate c.susceptible : ℝ) * f (infectCounts c) +
        (1 - (infectionProbability rate c.susceptible : ℝ)) * f (recoverCounts c) := by
  by_cases hu : c.susceptible = 0
  · rw [countsKernel_zero_susceptible rate hi hu]
    simp [hu]
  · change (∫ d, f d ∂(bernoulliMeasure true false
      (infectionProbability rate c.susceptible)).map (countsStep c)) = _
    rw [integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable f).aestronglyMeasurable, integral_bernoulliMeasure]
    simp [countsStep, hi.ne', hu]

theorem countsKernel_integrable (rate : ℝ≥0) (c : Counts) (f : Counts → ℝ) :
    Integrable f (countsKernel rate c) := by
  change Integrable f ((bernoulliMeasure true false
    (infectionProbability rate c.susceptible)).map (countsStep c))
  apply (integrable_map_measure (measurable_of_countable f).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).mpr
  exact integrable_bernoulliMeasure true false _ (f ∘ countsStep c)

noncomputable def harmonicPopulation (c : Counts) : ℝ := harmonic c.infectious

theorem harmonicPopulation_nonneg (c : Counts) : 0 ≤ harmonicPopulation c := by
  unfold harmonicPopulation harmonic
  push_cast
  exact Finset.sum_nonneg fun i _ => by positivity

theorem harmonic_real_succ (i : ℕ) :
    (harmonic (i + 1) : ℝ) = (harmonic i : ℝ) + 1 / (i + 1 : ℝ) := by
  rw [harmonic_succ]
  push_cast
  ring

theorem harmonic_real_pred {i : ℕ} (hi : 0 < i) :
    (harmonic (i - 1) : ℝ) = (harmonic i : ℝ) - 1 / (i : ℝ) := by
  have he : i - 1 + 1 = i := by omega
  have hh := harmonic_real_succ (i - 1)
  rw [he] at hh
  have hcast : ((i - 1 : ℕ) : ℝ) + 1 = i := by exact_mod_cast he
  rw [hcast] at hh
  linarith

theorem countsKernel_harmonic_drift (rate : ℝ≥0) {c : Counts}
    (hi : 0 < c.infectious) :
    (∫ d, harmonicPopulation d ∂countsKernel rate c) - harmonicPopulation c =
      (infectionProbability rate c.susceptible : ℝ) / (c.infectious + 1 : ℝ) -
        (1 - (infectionProbability rate c.susceptible : ℝ)) / c.infectious := by
  rw [countsKernel_integral_split rate hi]
  simp only [harmonicPopulation, infectCounts, recoverCounts,
    harmonic_real_succ, harmonic_real_pred hi]
  ring

theorem countsKernel_harmonic_reciprocal_bound (rate : ℝ≥0) (c : Counts) {eps : ℝ}
    (heps : (infectionProbability rate c.susceptible : ℝ) ≤ eps) :
    (∫ d, harmonicPopulation d ∂countsKernel rate c) +
      (1 - 2 * eps) / c.infectious ≤ harmonicPopulation c := by
  by_cases hi : c.infectious = 0
  · rw [countsKernel_absorbed rate hi]
    simp [hi]
  · have hi0 : 0 < c.infectious := by omega
    have hiR : (0 : ℝ) < c.infectious := by exact_mod_cast hi0
    have hd := countsKernel_harmonic_drift rate hi0
    have hp0 : 0 ≤ (infectionProbability rate c.susceptible : ℝ) :=
      (infectionProbability rate c.susceptible).property.1
    have hdiv : (infectionProbability rate c.susceptible : ℝ) / (c.infectious + 1 : ℝ) ≤
        (infectionProbability rate c.susceptible : ℝ) / c.infectious := by
      exact div_le_div_of_nonneg_left hp0 hiR (by linarith)
    have he : (infectionProbability rate c.susceptible : ℝ) / c.infectious -
        (1 - (infectionProbability rate c.susceptible : ℝ)) / c.infectious =
        (2 * (infectionProbability rate c.susceptible : ℝ) - 1) / c.infectious := by ring
    have hm := div_le_div_of_nonneg_right (by linarith :
      2 * (infectionProbability rate c.susceptible : ℝ) - 1 ≤ 2 * eps - 1) hiR.le
    have hcancel : (2 * eps - 1) / (c.infectious : ℝ) +
        (1 - 2 * eps) / c.infectious = 0 := by ring
    linarith

theorem countsKernel_lintegral_harmonic_budget (rate : ℝ≥0) (c : Counts) {eps : ℝ}
    (heps : eps ≤ 1 / 2)
    (hp : (infectionProbability rate c.susceptible : ℝ) ≤ eps) :
    (∫⁻ d, ENNReal.ofReal (harmonicPopulation d) ∂countsKernel rate c) +
      ENNReal.ofReal ((1 - 2 * eps) / c.infectious) ≤
        ENNReal.ofReal (harmonicPopulation c) := by
  have hc : 0 ≤ (1 - 2 * eps) / (c.infectious : ℝ) :=
    div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hint : 0 ≤ ∫ d, harmonicPopulation d ∂countsKernel rate c :=
    integral_nonneg harmonicPopulation_nonneg
  have hh := ENNReal.ofReal_le_ofReal (countsKernel_harmonic_reciprocal_bound rate c hp)
  rw [ENNReal.ofReal_add hint hc,
    ofReal_integral_eq_lintegral_ofReal (countsKernel_integrable rate c harmonicPopulation)
      (Filter.Eventually.of_forall harmonicPopulation_nonneg)] at hh
  exact hh

end Freezing1.SIR
