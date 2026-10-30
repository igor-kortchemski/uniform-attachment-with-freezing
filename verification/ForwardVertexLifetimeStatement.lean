module

import Freezing1.ForwardVertexLifetime

open Freezing1 MeasureTheory
open scoped BigOperators Classical

example (x : SignSequence) (a k : ℕ) (s : Forward.State)
    (hs : Forward.PhaseData x a s) (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x)
    (r : ℕ) (hr : r ≤ a) :
    (Forward.continuationLaw x a k s).real {q | r ∈ q.active} =
      (if r ∈ s.active then (1 : ℝ) else 0) *
        ∏ i ∈ Finset.Ioc a (a + k),
          (if x i then 1 else 1 - 1 / (activeCount x (i - 1) : ℝ)) :=
  Forward.continuationLaw_vertex_survival hs hτ hr

#print axioms Freezing1.Forward.vertexSurvivalFactor
#print axioms Freezing1.Forward.vertexSurvivalFactor_nonneg
#print axioms Freezing1.Forward.step_active_old
#print axioms Freezing1.Forward.transitionLaw_old_active_probability
#print axioms Freezing1.Forward.transitionLaw_vertex_survival
#print axioms Freezing1.Forward.continuationLaw_vertex_survival_measure
#print axioms Freezing1.Forward.continuationLaw_vertex_survival
