module

public import Freezing1.SIRCounts
public import Freezing1.SIRProbability
public import Freezing1.CountableMarkovObservations

/-!
# The actual embedded SIR count chain

An independent Bernoulli choice at each transition has the infection
probability determined by the current susceptible count. The process is
held at zero infectious count, and impossible infections at zero susceptible
count have zero probability. The full path is the genuine Markov path law.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

noncomputable def countsKernel (rate : ℝ≥0) : Kernel Counts Counts where
  toFun c := (bernoulliMeasure true false (infectionProbability rate c.susceptible)).map
    (countsStep c)
  measurable' := measurable_of_countable _

instance countsKernel_markov (rate : ℝ≥0) : IsMarkovKernel (countsKernel rate) := by
  constructor
  intro c
  change IsProbabilityMeasure ((bernoulliMeasure true false
    (infectionProbability rate c.susceptible)).map (countsStep c))
  infer_instance

theorem countsKernel_absorbed (rate : ℝ≥0) {c : Counts} (hi : c.infectious = 0) :
    countsKernel rate c = Measure.dirac c := by
  have he : countsStep c = fun _ => c := funext (countsStep_of_absorbed hi)
  change (bernoulliMeasure true false (infectionProbability rate c.susceptible)).map
    (countsStep c) = _
  rw [he, Measure.map_const]
  simp

theorem countsKernel_zero_susceptible (rate : ℝ≥0) {c : Counts}
    (hi : 0 < c.infectious) (hu : c.susceptible = 0) :
    countsKernel rate c = Measure.dirac (recoverCounts c) := by
  change (bernoulliMeasure true false (infectionProbability rate c.susceptible)).map
    (countsStep c) = _
  rw [hu, infectionProbability_zero_susceptible, bernoulliMeasure_zero,
    Measure.map_dirac' (measurable_of_countable _)]
  simp [countsStep, hi.ne']

theorem countsKernel_split (rate : ℝ≥0) {c : Counts} (hi : 0 < c.infectious) :
    countsKernel rate c =
      unitInterval.toNNReal (infectionProbability rate c.susceptible) •
        Measure.dirac (infectCounts c) +
      unitInterval.toNNReal (unitInterval.symm (infectionProbability rate c.susceptible)) •
        Measure.dirac (recoverCounts c) := by
  by_cases hu : c.susceptible = 0
  · rw [countsKernel_zero_susceptible rate hi hu]
    simp [hu]
  · change (bernoulliMeasure true false (infectionProbability rate c.susceptible)).map
      (countsStep c) = _
    rw [bernoulliMeasure_def, Measure.map_add _ _ (measurable_of_countable _),
      Measure.map_smul _ (measurable_of_countable _).aemeasurable,
      Measure.map_smul _ (measurable_of_countable _).aemeasurable,
      Measure.map_dirac' (measurable_of_countable _),
      Measure.map_dirac' (measurable_of_countable _)]
    simp [countsStep, hi.ne', hu]

theorem countsKernel_legal (rate : ℝ≥0) (c : Counts) :
    ∀ᵐ d ∂countsKernel rate c, c.LegalNext d := by
  by_cases hi : c.infectious = 0
  · rw [countsKernel_absorbed rate hi]
    simp [Counts.LegalNext, hi]
  · have hpos : 0 < c.infectious := by omega
    by_cases hu : c.susceptible = 0
    · rw [countsKernel_zero_susceptible rate hpos hu]
      simp [Counts.LegalNext, hpos]
    · change ∀ᵐ d ∂(bernoulliMeasure true false
        (infectionProbability rate c.susceptible)).map (countsStep c), c.LegalNext d
      apply (ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)).mpr
      apply Filter.Eventually.of_forall
      intro sign
      cases sign
      · exact Or.inr ⟨hpos, Or.inr (by simp [countsStep, hi])⟩
      · exact Or.inr ⟨hpos, Or.inl ⟨by omega, by simp [countsStep, hi, hu]⟩⟩

noncomputable def countsFullLaw (rate : ℝ≥0) (n : ℕ) : Measure (ℕ → Counts) :=
  CountableMarkovChain.fullLaw (countsKernel rate) (initialCounts n)

instance countsFullLaw_probability (rate : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (countsFullLaw rate n) := by unfold countsFullLaw; infer_instance

theorem countsFullLaw_initial (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂countsFullLaw rate n, H 0 = initialCounts n :=
  CountableMarkovChain.fullLaw_initial (countsKernel rate) (initialCounts n)

theorem countsFullLaw_legal (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂countsFullLaw rate n, ∀ k, (H k).LegalNext (H (k + 1)) :=
  CountableMarkovChain.fullLaw_steps (countsKernel rate) (initialCounts n)
    Counts.LegalNext (countsKernel_legal rate)

theorem countsFullLaw_valid (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂countsFullLaw rate n, ∀ k, (H k).Valid n := by
  filter_upwards [countsFullLaw_initial rate n, countsFullLaw_legal rate n] with H h0 hl
  intro k
  induction k with
  | zero => rw [h0]; exact initialCounts_valid n
  | succ k ih => exact (hl k).valid ih

theorem countsFullLaw_susceptible_bounds (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂countsFullLaw rate n, ∀ k,
      n - k ≤ (H k).susceptible ∧ (H k).susceptible ≤ n := by
  filter_upwards [countsFullLaw_initial rate n, countsFullLaw_legal rate n] with H h0 hl
  exact legalHistory_susceptible_bounds h0 hl

theorem countsFullLaw_absorbed_by (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂countsFullLaw rate n,
      (H (2 * n + 1)).infectious = 0 ∧
        ∀ k ≥ 2 * n + 1, H k = H (2 * n + 1) := by
  filter_upwards [countsFullLaw_initial rate n, countsFullLaw_legal rate n] with H h0 hl
  have ha := legalHistory_absorbed_by h0 hl
  exact ⟨ha, legalHistory_absorbed_persists hl ha⟩

end Freezing1.SIR
