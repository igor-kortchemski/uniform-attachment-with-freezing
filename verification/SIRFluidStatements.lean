module

import Freezing1.MainSIREmbedded
import Freezing1.SIRSusceptibleFluid
import Freezing1.SIRStoppedCoupling

/-!
Source reconstruction of the auxiliary fluid claims at lines2131--2197
and their analytic dependencies at lines2087 and2118--2121. These are
unstopped paths. This probe does not claim the stopped survival mixture.
The reconstruction was written separately from those implementations.
-/

open Freezing1 Filter MeasureTheory
open scoped Topology NNReal ContDiff

example (lam : ℝ) (hlam : 0 < lam) :
    SIR.fluidProfile lam 0 = 1 ∧
    (∀ t : ℝ, 0 < SIR.fluidProfile lam t) ∧
    (∀ t : ℝ, HasDerivAt (SIR.fluidProfile lam)
      (-lam * SIR.fluidProfile lam t / (1 + lam * SIR.fluidProfile lam t)) t) :=
  ⟨SIR.fluidProfile_zero hlam, SIR.fluidProfile_pos hlam,
    SIR.fluidProfile_hasDerivAt hlam⟩

-- The proved uniqueness class is explicit: positive solutions on t>=0.
example (lam : ℝ) (hlam : 0 < lam) (g : ℝ → ℝ) (h0 : g 0 = 1)
    (hpos : ∀ t ≥ 0, 0 < g t)
    (hode : ∀ t ≥ 0, HasDerivAt g (-lam * g t / (1 + lam * g t)) t) :
    ∀ t ≥ 0, g t = SIR.fluidProfile lam t := by
  intro t ht
  exact SIR.fluidProfile_unique_positive hlam h0 hpos hode ht

example (lam : ℝ) (hlam : 0 < lam) :
    ContDiff ℝ ∞ (SIR.fluidProfile lam) ∧
    StrictAnti (SIR.fluidProfile lam) ∧
    StrictConvexOn ℝ Set.univ (SIR.fluidProfile lam) ∧
    Tendsto (SIR.fluidProfile lam) atTop (𝓝 0) :=
  ⟨SIR.fluidProfile_contDiff hlam, SIR.fluidProfile_strictAnti hlam,
    SIR.fluidProfile_strictConvex hlam, SIR.fluidProfile_tendsto_zero hlam⟩

example (lam : ℝ) (hlam : 1 < lam) :
    ∃ t0 ∈ Set.Ioo (0 : ℝ) 2,
      (2 - 2 * SIR.fluidProfile lam t0 - t0 = 0) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) t0, 0 < 2 - 2 * SIR.fluidProfile lam t - t) ∧
      (∀ t > t0, 2 - 2 * SIR.fluidProfile lam t - t < 0) := by
  refine ⟨SIR.fluidExtinctionTime lam,
    ⟨(SIR.fluidExtinctionTime_spec hlam).1, (SIR.fluidExtinctionTime_spec hlam).2.1⟩,
    (SIR.fluidExtinctionTime_spec hlam).2.2, ?_, ?_⟩
  · exact fun t ht => SIR.infectiousProfile_pos_before hlam ht.1 ht.2
  · exact fun t ht => SIR.infectiousProfile_neg_after hlam ht

-- No exact rate lambda/n is substituted. Each n uses its own genuine law.
example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : 0 < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / n)) atTop (𝓝 1))
    (T : ℝ) (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun n : ℕ => SIR.Susceptible.fullLaw (rate n) n
      {U | ∃ k : ℕ, (k : ℝ) / n ≤ T ∧
        eps ≤ |(U k : ℝ) / n - SIR.fluidProfile lam ((k : ℝ) / n)|}) atTop (𝓝 0) :=
  SIR.Susceptible.uniform_fluid_on_time_interval_tendsto rate
    (by exact_mod_cast hlam) (SIR.scaled_rate_of_source_ratio rate lam hlam hratio) T heps

example (rate : ℕ → ℝ≥0) (lam : ℝ) (hlam : 0 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (m : ℕ) (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun n : ℕ => SIR.Susceptible.fullLaw (rate n) n
      {U | ∃ k ≤ n * m,
        eps ≤ |((2 * ((n : ℤ) - U k) - k + 1 : ℤ) : ℝ) / n -
          (2 - 2 * SIR.fluidProfile lam ((k : ℝ) / n) - (k : ℝ) / n)|}) atTop (𝓝 0) :=
  SIR.Susceptible.uniform_infectious_fluid_tendsto rate hlam hrate m heps

-- Exact joint full-path marginals and the first extinct state are retained.
example (rate : ℝ≥0) (n : ℕ) :
    (SIR.StoppedCoupling.fullLaw rate n).map (fun H k => (H k).1) = SIR.countsFullLaw rate n ∧
    (SIR.StoppedCoupling.fullLaw rate n).map (fun H k => (H k).2) = SIR.Susceptible.fullLaw rate n :=
  ⟨SIR.StoppedCoupling.map_fullLaw_counts rate n, SIR.StoppedCoupling.map_fullLaw_unstopped rate n⟩

example (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂SIR.StoppedCoupling.fullLaw rate n, ∀ k : ℕ,
      (∀ j : ℕ, j < k → 0 < (H j).1.infectious) →
        (H k).1.susceptible = (H k).2 ∧
        ((H k).1.infectious : ℤ) = 2 * ((n : ℤ) - (H k).2) - k + 1 :=
  SIR.StoppedCoupling.fullLaw_agree_until_extinction rate n

#print axioms Freezing1.SIR.Susceptible.transition
#print axioms Freezing1.SIR.Susceptible.fullLaw
#print axioms Freezing1.SIR.Susceptible.noise_lintegral_exp_le
#print axioms Freezing1.SIR.Susceptible.noise_uniform_div_population_tendsto
#print axioms Freezing1.SIR.Susceptible.uniform_fluid_on_time_interval_tendsto
#print axioms Freezing1.SIR.Susceptible.uniform_infectious_fluid_tendsto
#print axioms Freezing1.SIR.fluidProfile_unique_positive
#print axioms Freezing1.SIR.fluidExtinctionTime_spec
#print axioms Freezing1.SIR.StoppedCoupling.map_fullLaw_counts
#print axioms Freezing1.SIR.StoppedCoupling.map_fullLaw_unstopped
#print axioms Freezing1.SIR.StoppedCoupling.fullLaw_agree_until_extinction
