module

import Freezing1.SIRStrongCounts
import Freezing1.MainSIREmbedded

/-!
Independent reconstruction of T07.II.a (source 2095--2101), including the
actual stopped law, the real interval [0,2], and the source ratio premise.
This verifies the constructed embedded model. The physical Poisson-process
bridge and the relative near-origin estimate A79 are separate obligations.
-/

open Freezing1 Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

-- The uniform event is Borel, despite quantification over real times.
example (n : ℕ) (eps : ℝ) :
    MeasurableSet {H : ℕ → SIR.Counts | ∃ t ∈ Set.Icc (0 : ℝ) 2,
      eps ≤ |((H ⌊(n : ℝ) * t⌋₊).infectious : ℝ) / n - min t (2 - t)|} :=
  SIR.measurableSet_triangle_uniform_error n eps

-- Full literal event-form reconstruction of T07.II.a. The full Markov law
-- and initial susceptible/infectious population are expanded explicitly.
example (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ =>
      (CountableMarkovChain.fullLaw (SIR.countsKernel (rate n)) (SIR.initialCounts n)).real
        {H | ∃ t ∈ Set.Icc (0 : ℝ) 2,
          eps ≤ |((H ⌊(n : ℝ) * t⌋₊).infectious : ℝ) / n - min t (2 - t)|})
      atTop (𝓝 0) :=
  SIR.countsFullLaw_strong_uniform_tendsto rate
    (SIR.scaled_rate_atTop_of_source_ratio rate hratio) heps

-- Constant unscaled intensity one satisfies the source's strong scaled
-- hypothesis, without itself diverging. No survival assumption is supplied.
example {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => (SIR.countsFullLaw 1 n).real
      {H | ∃ t ∈ Set.Icc (0 : ℝ) 2,
        eps ≤ |((H ⌊(n : ℝ) * t⌋₊).infectious : ℝ) / n - min t (2 - t)|})
      atTop (𝓝 0) :=
  SIR.countsFullLaw_strong_uniform_tendsto (fun _ => 1)
    (by simpa only [NNReal.coe_one, mul_one] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)) heps

-- A finite bound pays for absorption; it does not condition it away.
example (rate : ℝ≥0) (n m : ℕ) (hpressure : 1 ≤ (rate : ℝ) * (n - m : ℕ)) :
    SIR.countsFullLaw rate n {H | (H m).infectious = 0} ≤
      ENNReal.ofReal (((rate : ℝ) * (n - m : ℕ))⁻¹) :=
  SIR.countsFullLaw_early_absorption_inv_le rate n m hpressure

-- The deterministic triangle bound controls the entire 0,...,2n interval
-- on every legal path, including an early absorbed path.
example {H : ℕ → SIR.Counts} {n m : ℕ}
    (h0 : H 0 = SIR.initialCounts n)
    (hlegal : ∀ k, (H k).LegalNext (H (k + 1))) (hm : m ≤ n) :
    ∀ k ≤ 2*n,
      |((H k).infectious : ℝ) - (min k (2*n-k) : ℕ)| ≤ 2 * (H m).susceptible + 1 :=
  fun _ hk => SIR.legalHistory_triangle_error h0 hlegal hm hk

-- Initial time contributes the correct 1/n error, and the time-2 endpoint
-- may still contain one infective. No premature extinction at 2n is used.
example (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂SIR.countsFullLaw rate n,
      |((H ⌊(n : ℝ) * 0⌋₊).infectious : ℝ) / n - min 0 (2-0)| = 1 / n := by
  filter_upwards [SIR.countsFullLaw_initial rate n] with H h0
  simp [h0, SIR.initialCounts]

example (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂SIR.countsFullLaw rate n, (H (2*n)).infectious ≤ 1 := by
  filter_upwards [SIR.countsFullLaw_initial rate n, SIR.countsFullLaw_legal rate n] with H h0 hl
  by_cases hi : (H (2*n)).infectious = 0
  · omega
  · have hh := SIR.legalHistory_count_identity h0 hl (by omega : 0 < (H (2*n)).infectious)
    omega

#print axioms Freezing1.SIR.countsKernel_lintegral_power_le
#print axioms Freezing1.SIR.countsFullLaw_lintegral_power_le
#print axioms Freezing1.SIR.countsFullLaw_early_absorption_le
#print axioms Freezing1.SIR.countsFullLaw_early_absorption_inv_le
#print axioms Freezing1.SIR.countsFullLaw_lintegral_missedInfections_le
#print axioms Freezing1.SIR.legalHistory_triangle_error
#print axioms Freezing1.SIR.countsFullLaw_lintegral_susceptible_early_le
#print axioms Freezing1.SIR.countsFullLaw_triangle_error_real_le
#print axioms Freezing1.SIR.countsFullLaw_triangle_tendsto_zero
#print axioms Freezing1.SIR.measurableSet_triangle_uniform_error
#print axioms Freezing1.SIR.countsFullLaw_strong_uniform_tendsto
