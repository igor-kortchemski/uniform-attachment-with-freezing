module

import Freezing1.GeometricBranchingTails

/-! Exact source A26 recurrence, with its predecessor index and boundary. -/

open Freezing1 MeasureTheory
open scoped ENNReal

example {T : Type*} [MeasurableSpace T] (D : FirstChildStructure T)
    (mu : Measure T) [IsProbabilityMeasure mu] (q r : ℝ≥0∞)
    (hmu : mu = q • Measure.dirac D.leaf + r • (mu.prod mu).map D.graft)
    (j : ℕ) (hj : 1 ≤ j) :
    mu {t | j ≤ D.degree t} = r * mu {t | j - 1 ≤ D.degree t} := by
  simpa only [Nat.sub_add_cancel hj] using
    D.degree_tail_recurrence_of_fixedPoint mu q r hmu (j - 1)

example (p : unitInterval) (hp : (p : ℝ) < 1) (j : ℕ) :
    (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree)
      {T | j ≤ PlaneTree.degree T} = ENNReal.ofReal ((p : ℝ) ^ j) :=
  ForwardAnnealed.planeLimitLaw_offspring_tail p hp j

#print axioms Freezing1.FirstChildStructure.degree_tail_recurrence_of_fixedPoint
#print axioms Freezing1.FirstChildStructure.degree_tail_of_fixedPoint
#print axioms Freezing1.ForwardAnnealed.planeLimitLaw_offspring_tail
#print axioms Freezing1.ForwardAnnealed.planeLimitLaw_offspring_tail_recurrence
