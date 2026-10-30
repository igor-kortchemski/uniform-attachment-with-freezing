module

import Freezing1.SIRBiasedWalkExtinction
import Freezing1.SIRProbability

/-!
Independent statement reconstruction for the absorbed iid walk used in
the source SIR early-extinction comparison (A73).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Freezing1.SIR.BiasedWalkStatementAudit

example (p : unitInterval) :
    BiasedWalk.transition p 0 = Measure.dirac 0 := by
  rfl

example (p : unitInterval) (i : ℕ) (hi : 0 < i) :
    BiasedWalk.transition p i = bernoulliMeasure (i + 1) (i - 1) p := by
  change (if i = 0 then _ else _) = _
  rw [ite_eq_right hi.ne']

example (p : unitInterval) :
    BiasedWalk.fullLaw p = CountableMarkovChain.fullLaw (BiasedWalk.transition p) 1 := rfl

theorem source_probability_gt_half (lam : ℝ≥0) (hlam : 1 < (lam : ℝ)) :
    (1 : ℝ) / 2 < (infectionProbability lam 1 : ℝ) := by
  rw [infectionProbability_coe]
  simp only [Nat.cast_one, mul_one]
  apply (lt_div_iff₀ (by positivity : 0 < 1 + (lam : ℝ))).mpr
  linarith

theorem source_extinction_parameter (lam : ℝ≥0) (hlam : 1 < (lam : ℝ)) :
    (1 - (infectionProbability lam 1 : ℝ)) / (infectionProbability lam 1 : ℝ) =
      1 / (lam : ℝ) := by
  rw [infectionProbability_complement, infectionProbability_coe]
  simp only [Nat.cast_one, mul_one]
  field_simp

/-- Exact source parameter, with the real probability of the true stopped
walk started at one. No extinction-probability premise is added. -/
theorem source_walk_extinction_tendsto (lam : ℝ≥0) (hlam : 1 < (lam : ℝ)) :
    Tendsto (fun k : ℕ =>
      (CountableMarkovChain.fullLaw (BiasedWalk.transition (infectionProbability lam 1)) 1).real
        {H | H k = 0}) atTop (nhds (1 / (lam : ℝ))) := by
  have hh := BiasedWalk.zero_probability_tendsto (infectionProbability lam 1)
    (source_probability_gt_half lam hlam)
  rw [source_extinction_parameter lam hlam] at hh
  have hreal := (ENNReal.continuousAt_toReal ENNReal.ofReal_ne_top).tendsto.comp hh
  change Tendsto (fun k : ℕ => (BiasedWalk.fullLaw (infectionProbability lam 1)).real
    {H | H k = 0}) atTop (nhds (1 / (lam : ℝ)))
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  simpa only [Function.comp_def, Measure.real] using hreal

end Freezing1.SIR.BiasedWalkStatementAudit

#print axioms Freezing1.SIR.BiasedWalk.transition_power_harmonic
#print axioms Freezing1.SIR.BiasedWalk.fullLaw_positivePower_le
#print axioms Freezing1.SIR.BiasedWalk.zero_probability_tendsto
#print axioms Freezing1.SIR.BiasedWalkStatementAudit.source_walk_extinction_tendsto
