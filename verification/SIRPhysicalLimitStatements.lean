module

public import Freezing1.SIRPhysicalLimits

/-! Source-facing limit probes with eventual original process assumptions. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (mu : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (mu n)]
  (X : (n : ℕ) → (c : ClockSlot n) → Ω n → ClockDatum c)

example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : 0 < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (hdata : ∀ᶠ n in atTop,
      (∀ c, Measurable (X n c)) ∧ iIndepFun (X n) (mu n) ∧
      (∀ v : Individual n, (mu n).map (X n (v, none)) = expMeasure 1) ∧
      (∀ v w : Individual n,
        PoissonContact.HasPoissonCounts ((mu n).map (X n (v, some w))) (rate n))) :
    Tendsto (fun n => physicalTerminalTreeLaw (mu n) n (X n)) atTop
      (𝓝 (geometricProbabilityLaw (infectionProbability lam 1))) := by
  apply physical_sir_geometric_local_limit_of_source_ratio mu X rate lam hlam hratio
  filter_upwards [hdata] with n hn
  exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2⟩

example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : 1 < (lam : ℝ))
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1))
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)) :
    Tendsto (fun n => physicalPopulationPathLaw (mu n) n (X n)) atTop
      (𝓝 (geometricSurvivalPathLaw lam)) :=
  physical_sir_fluid_limit_of_source_ratio mu X rate lam hlam hratio hdata

example (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (physicalCountsPathLaw (mu n) n (X n) : Measure (ℕ → Counts)).real
      {H | ∃ t ∈ Set.Icc (0 : ℝ) 2, eps ≤
        |((H ⌊(n : ℝ) * t⌋₊).infectious : ℝ) / n - min t (2 - t)|}) atTop (𝓝 0) :=
  physical_sir_strong_uniform_fluid_limit_of_source_ratio mu X rate hratio hdata heps

example (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (hdata : ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => physicalPairDataLaw (mu n) n (X n) (2 * n + 1)
      {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2|}) atTop (𝓝 0) :=
  physical_sir_strong_terminal_uniform_distance_of_source_ratio mu X rate hratio hdata heps

#print axioms PoissonSIRData.scaledPopulationPath_ae
#print axioms eventually_rate_pos_of_scaled_limit
#print axioms eventually_rate_pos_of_scaled_atTop
#print axioms physical_sir_geometric_local_limit_of_source_ratio
#print axioms physical_terminal_bounded_degree_tendsto_zero_of_source_ratio
#print axioms physical_sir_not_tight_of_source_ratio
#print axioms physical_sir_fluid_limit_of_source_ratio
#print axioms physical_sir_strong_uniform_fluid_limit_of_source_ratio
#print axioms physical_sir_strong_terminal_uniform_height_of_source_ratio
#print axioms physical_sir_strong_terminal_uniform_distance_of_source_ratio
#print axioms physical_sir_strong_terminal_maximum_of_source_ratio

end Freezing1.SIR
