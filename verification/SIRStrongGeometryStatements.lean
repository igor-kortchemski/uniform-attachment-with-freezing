module

import Freezing1.MainSIRStrongMaximum
import Freezing1.MainSIRUniformDistanceStrong
import Freezing1.MainSIRUniformSamplesStrong

/-!
Independent reconstruction from source 2095--2104 and 2241--2330.
The time-n statements are distinguished from the terminal statements.
The underlying full Markov law, population, graph metric and actual terminal
horizon are made explicit. Physical exponential/Poisson identification is
a separate obligation.
-/

open Freezing1 Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology Classical

-- A uniform height is sampled from all vertices of the actual plane state.
example (rate : ℝ≥0) (n k : ℕ) :
    SIR.sirUniformHeightLaw rate n k =
      ((CountableMarkovChain.fullLaw (SIR.treeKernel rate) (SIR.initialTreeState n)).map
        (fun H => (H k).tree)).bind PlaneForward.vertexHeightKernel := rfl

-- Both vertices are drawn conditionally independently from the same tree.
-- The diagonal remains part of this law.
example (s : PlaneForward.State) (hs : s.vertices.Nonempty) :
    PlaneForward.pairDataKernel s = (Measure.uniformOfFinset s.vertices).bind
      (fun u => (Measure.uniformOfFinset s.vertices).map
        (fun v => (u.length, v.length, (PlaneForward.parentGraph s).dist u v))) := by
  change (if s.vertices.Nonempty then _ else _) = _
  rw [ite_eq_left hs]

-- Population time n is an intermediate observation, not the terminal time.
example (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => SIR.sirUniformHeightLaw (rate n) n n
      {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - 1|}) atTop (𝓝 0) :=
  SIR.sir_time_n_uniform_height_tendsto rate
    (SIR.scaled_rate_atTop_of_source_ratio rate hratio) heps

example (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n =>
      (((CountableMarkovChain.fullLaw (SIR.treeKernel (rate n))
        (SIR.initialTreeState n)).map (fun H => (H n).tree)).bind PlaneForward.pairDataKernel)
      {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2|}) atTop (𝓝 0) :=
  SIR.sir_time_n_uniform_distance_tendsto rate
    (SIR.scaled_rate_atTop_of_source_ratio rate hratio) heps

-- Exact terminal T07.II.b maximum, under the source rate-ratio premise.
example (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n =>
      (((CountableMarkovChain.fullLaw (SIR.treeKernel (rate n))
        (SIR.initialTreeState n)).map (fun H => (H (2*n+1)).tree)).bind
          PlaneForward.vertexHeightKernel)
      {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - 1|}) atTop (𝓝 0) :=
  SIR.sir_terminal_uniform_height_tendsto rate
    (SIR.scaled_rate_atTop_of_source_ratio rate hratio) heps

example (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n =>
      (((CountableMarkovChain.fullLaw (SIR.treeKernel (rate n))
        (SIR.initialTreeState n)).map (fun H => (H (2*n+1)).tree)).bind
          PlaneForward.pairDataKernel)
      {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2|}) atTop (𝓝 0) :=
  SIR.sir_terminal_uniform_distance_tendsto rate
    (SIR.scaled_rate_atTop_of_source_ratio rate hratio) heps

-- Exact terminal T07.II.b maximum, under the source rate-ratio premise.
example (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n =>
      (CountableMarkovChain.fullLaw (SIR.treeKernel (rate n)) (SIR.initialTreeState n))
        {H | eps ≤ |(((H (2*n+1)).tree.vertices.sup List.length : ℕ) : ℝ) /
          Real.log (n : ℝ) - Real.exp 1|}) atTop (𝓝 0) :=
  SIR.sir_terminal_maximum_of_source_ratio rate hratio heps

-- A constant per-pair rate satisfies the strong regime without itself
-- tending to infinity. No extra survival or late-height premise is supplied.
example {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => SIR.treeFullLaw 1 n
      {H | eps ≤ |(((H (2*n+1)).tree.vertices.sup List.length : ℕ) : ℝ) /
        Real.log (n : ℝ) - Real.exp 1|}) atTop (𝓝 0) :=
  SIR.sir_terminal_maximum_tendsto (fun _ => 1)
    (by simpa only [NNReal.coe_one, mul_one] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)) heps

#print axioms Freezing1.SIR.RandomEnvironment.uniform_bound_of_sequential
#print axioms Freezing1.SIR.RandomEnvironment.uniform_profile_height_bound
#print axioms Freezing1.SIR.RandomEnvironment.uniform_profile_distance_bound
#print axioms Freezing1.SIR.RandomEnvironment.uniform_profile_maximum_bound
#print axioms Freezing1.SIR.RandomEnvironment.strong_average_score_tendsto_zero
#print axioms Freezing1.SIR.sir_time_n_uniform_height_tendsto
#print axioms Freezing1.SIR.sir_time_n_uniform_distance_tendsto
#print axioms Freezing1.SIR.sir_time_n_maximum_tendsto
#print axioms Freezing1.SIR.countsFullLaw_post_population_birth_charge_over_log_tendsto_zero
#print axioms Freezing1.SIR.terminalForwardLaw_cutMaximum_over_log_tendsto_zero
#print axioms Freezing1.SIR.terminalForwardLaw_prefix_maximum_event_eq_actual
#print axioms Freezing1.SIR.sir_terminal_maximum_tendsto
#print axioms Freezing1.SIR.sir_terminal_maximum_of_source_ratio
#print axioms Freezing1.SIR.terminal_word_uniform_samples_bound
#print axioms Freezing1.SIR.strong_terminal_average_tendsto_zero
#print axioms Freezing1.SIR.sir_terminal_uniform_height_tendsto
#print axioms Freezing1.SIR.sir_terminal_uniform_distance_tendsto
