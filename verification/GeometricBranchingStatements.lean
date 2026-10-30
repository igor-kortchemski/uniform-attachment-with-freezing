module

import Freezing1.PlaneTreeBranching

/-!
The source L05 hypothesis and conclusion are expanded here. This is a
characterization of arbitrary plane-tree probability laws; the separate
T02 bridge must verify the hypothesis for the actual attachment model.
-/

open Freezing1 MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

example (p : unitInterval) (hp : (p : ℝ) < 1)
    (μ : Measure PlaneTree.Tree) [IsProbabilityMeasure μ]
    (h0 : μ {T | T.val [] = 0} = ENNReal.ofReal (1 - (p : ℝ)))
    (hsplit : (p : ℝ) ≠ 0 →
      (ProbabilityTheory.cond μ {T | 0 < T.val []}).map
        (fun T => (PlaneTree.child T 1, PlaneTree.dropFirst T)) = μ.prod μ) :
    μ.map (fun T => T.val []) = geometricMeasure (unitInterval.symm p) ∧
    ∀ k : ℕ, μ {T | T.val [] = k} ≠ 0 →
      (ProbabilityTheory.cond μ {T | T.val [] = k}).map
        (fun T (i : Fin k) => PlaneTree.child T (i.val + 1)) =
          Measure.pi (fun _ : Fin k => μ) :=
  PlaneTree.isBienayme_geometric_of_conditional_split p hp μ h0 hsplit

#print axioms Freezing1.FirstChildStructure.measurableSet_childrenEvent
#print axioms Freezing1.FirstChildStructure.graft_preimage_childrenEvent_succ
#print axioms Freezing1.FirstChildStructure.childrenEvent_measure_of_fixedPoint
#print axioms Freezing1.FirstChildStructure.degree_measure_of_fixedPoint
#print axioms Freezing1.FirstChildStructure.conditional_childrenLaw_of_fixedPoint
#print axioms Freezing1.FirstChildStructure.fixedPoint_of_conditional_split
#print axioms Freezing1.PlaneTree.firstChildStructure
#print axioms Freezing1.PlaneTree.IsBienayme
#print axioms Freezing1.PlaneTree.isBienayme_geometric_of_fixedPoint
#print axioms Freezing1.PlaneTree.isBienayme_geometric_of_conditional_split
