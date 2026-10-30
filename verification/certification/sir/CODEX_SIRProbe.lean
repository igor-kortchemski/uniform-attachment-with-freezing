module

import Freezing1

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace Freezing1.SIR

/-! A non-vacuous end-to-end specialization: the existence theorem supplies
one family of real data at rate one, on which both actual-model conclusions
hold. No `PoissonSIRData` or tail estimate is assumed by this example. -/

example :
    ∃ (Ω : ℕ → Type) (_ : ∀ n, MeasurableSpace (Ω n))
      (mu : (n : ℕ) → Measure (Ω n)) (_ : ∀ n, IsProbabilityMeasure (mu n))
      (X : (n : ℕ) → (c : ClockSlot n) → Ω n → ClockDatum c),
      (∀ᶠ n in atTop, PoissonSIRData (mu n) n 1 (X n)) ∧
      (¬IsTightMeasureSet (Set.range fun n =>
        (physicalTerminalTreeLaw (mu n) n (X n) : Measure PlaneTree.Tree))) ∧
      (∀ eps : ℝ, 0 < eps →
        Tendsto (fun n => (physicalCountsPathLaw (mu n) n (X n) : Measure (ℕ → Counts)).real
          {H | ∃ t ∈ Set.Icc (0 : ℝ) 2, eps ≤
            |((H ⌊(n : ℝ) * t⌋₊).infectious : ℝ) / n - min t (2 - t)|})
          atTop (𝓝 0)) := by
  obtain ⟨Ω, mΩ, mu, pmu, X, hX⟩ :=
    PoissonSIRData.exists_family (fun _ : ℕ => (1 : ℝ≥0))
      (Filter.Eventually.of_forall fun _ => zero_lt_one)
  let : ∀ n, MeasurableSpace (Ω n) := mΩ
  let : ∀ n, IsProbabilityMeasure (mu n) := pmu
  have hrate : Tendsto (fun n : ℕ => (1 : ℝ) / (1 / (n : ℝ))) atTop atTop := by
    simpa only [one_div_one_div] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  refine ⟨Ω, mΩ, mu, pmu, X, hX, ?_, ?_⟩
  · exact physical_sir_not_tight_of_source_ratio mu X (fun _ => 1) hrate hX
  · intro eps heps
    exact physical_sir_strong_uniform_fluid_limit_of_source_ratio mu X (fun _ => 1)
      hrate hX heps

#print axioms PoissonSIRData.exists_data
#print axioms PoissonSIRData.exists_family
#print axioms PoissonSIRData.exists_data_iff
#print axioms physical_sir_not_tight_of_source_ratio
#print axioms physical_sir_strong_uniform_fluid_limit_of_source_ratio
#print axioms independent_poisson_fullContact_counts_fullLaw

end Freezing1.SIR
