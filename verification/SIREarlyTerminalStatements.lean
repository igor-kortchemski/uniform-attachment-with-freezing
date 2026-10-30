module

import Freezing1.SIREarlyTerminalSampling

/-!
Development statement checks for the small-epidemic branch of T07.I.b.
These checks are self-review of the root-authored helpers, not an independent
audit of a completed finite-rate height theorem.
-/

open Freezing1 Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : (1 : ℝ) < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    (L : ℕ → ℕ) (hL : Tendsto L atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (L n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (CountableMarkovChain.fullLaw (SIR.countsKernel (rate n)) (SIR.initialCounts n)).real
        {H | (H (L n)).infectious = 0}) atTop (𝓝 (1 / (lam : ℝ))) :=
  SIR.countsFullLaw_sublinear_extinction_tendsto rate lam hlam hrate L hL hsmall

example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : (1 : ℝ) < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ))) :
    Tendsto (fun n : ℕ => (SIR.treeFullLaw (rate n) n).real
      {H | (H ⌈Real.log (Real.log (n : ℝ))⌉₊).tree.active = ∅})
      atTop (𝓝 (1 / (lam : ℝ))) :=
  SIR.treeFullLaw_logLog_extinction_tendsto rate lam hlam hrate

-- On this very same actual early-extinction event, the complete terminal
-- tree has negligible maximum. No new probability space is substituted.
example (rate : ℕ → ℝ≥0) {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => SIR.treeFullLaw (rate n) n
      {H | (H ⌈Real.log (Real.log (n : ℝ))⌉₊).tree.active = ∅ ∧ eps ≤
        (((H (2*n+1)).tree.vertices.sup List.length : ℕ) : ℝ) / Real.log (n : ℝ)})
      atTop (𝓝 0) :=
  SIR.treeFullLaw_logLog_early_terminal_height_negligible rate heps

#print axioms Freezing1.SIR.susceptible_gap_pressure_tendsto
#print axioms Freezing1.SIR.countsFullLaw_sublinear_extinction_tendsto
#print axioms Freezing1.SIR.treeFullLaw_maximum_le_time
#print axioms Freezing1.SIR.treeFullLaw_absorbed_persists
#print axioms Freezing1.SIR.treeFullLaw_logLog_extinction_tendsto
#print axioms Freezing1.SIR.treeFullLaw_logLog_early_terminal_height_negligible
#print axioms Freezing1.PlaneForward.Valid.parentGraph_root_dist
#print axioms Freezing1.PlaneForward.Valid.pairDataKernel_metric_bounds
#print axioms Freezing1.SIR.treeFullLaw_early_uniform_height_negligible
#print axioms Freezing1.SIR.treeFullLaw_early_uniform_distance_negligible
