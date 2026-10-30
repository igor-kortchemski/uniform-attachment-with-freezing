module

import Freezing1.SIRReverseCouplingSourceGap
import Freezing1.SIRReverseCouplingNecessary

open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical

noncomputable section

namespace Freezing1.SIR.ReverseCouplingProgressStatementCheck

example (rate : ℝ≥0) (hr : 0 < rate) :
    SignWordFeasible 6 reverseWindowExampleWord ∧
      0 < (signWordLaw rate 6 9).real {reverseWindowExampleWord} :=
  ⟨reverseWindowExampleWord_feasible, reverseWindowExampleWord_positive_probability rate hr⟩

example (rate : ℝ≥0) (hr : 0 < rate) :
    0 < (countsFullLaw rate 6)
      {H | H ∈ sourceReverseBadEvent rate 6 (infectionProbability rate 2) 3 ∧
        (infectionProbability rate 2 : ℝ) <
          infectionProbability rate (H (boundedExtinctionIndex 6 H - 3)).susceptible} := by
  apply (countsFullLaw_reverseWindowHazardGap_pos rate hr).trans_le
  exact measure_mono (fun H hH => reverseWindowHazardGap_sourceBad rate H hH)

example (rate : ℝ≥0) (hr : 0 < rate) :
    ¬ (∀ᵐ H ∂countsFullLaw rate 6,
      H ∈ sourceLatePressureEvent rate 6 (infectionProbability rate 2) →
        ∀ j : ℕ, 1 ≤ j → j ≤ sourceReverseWindow 6 H →
          (infectionProbability rate (H (boundedExtinctionIndex 6 H - j)).susceptible : ℝ) ≤
            infectionProbability rate 2) :=
  late_gate_reverse_hazard_inheritance_false rate hr

example :
    (infectionProbability (1 / 100 : ℝ≥0) 2 : ℝ) = 1 / 51 ∧
      (infectionProbability (1 / 100 : ℝ≥0) 3 : ℝ) = 3 / 103 ∧
      (0 : ℝ) < 1 / 51 ∧ (1 / 51 : ℝ) < 3 / 103 ∧ (3 / 103 : ℝ) < 1 := by
  norm_num [infectionProbability_coe]

/-- This is explicitly a necessary-condition result with a coupling premise;
it makes no assertion of the unresolved coupling's existence. -/
example (rate : ℝ≥0) (n : ℕ) (ε : unitInterval)
    (hc : SourceReverseIidCoupling rate n ε) (j : ℕ) :
    (countsFullLaw rate n) (sourceReverseBadEvent rate n ε j) ≤
      (unitInterval.toNNReal ε : ℝ≥0∞) :=
  hc.bad_coordinate_le rate n ε j

#print axioms reverseWindowExampleWord_feasible
#print axioms reverseWindowExampleWord_positive_probability
#print axioms reverseWindowExampleWord_prefix_positive
#print axioms countsFullLaw_reverseWindowHazardGap_pos
#print axioms reverseWindowHazardGap_extinctionIndex
#print axioms reverseWindowHazardGap_sourceGate
#print axioms reverseWindowHazardGap_sourceBad
#print axioms late_gate_reverse_hazard_inheritance_false
#print axioms measurableSet_sourceReverseBadEvent
#print axioms SourceReverseIidCoupling.bad_coordinate_le

end Freezing1.SIR.ReverseCouplingProgressStatementCheck
