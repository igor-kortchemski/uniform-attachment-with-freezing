module

import Freezing1.MainLocalNecessity

/-!
Independent expanded statement probes for the necessary direction of T01.
No survival condition is imposed on the diagonal schedules.
-/

open Freezing1 Filter MeasureTheory
open scoped Topology Classical

example (x : SignSequence) (d a b : ℕ) (hab : a ≤ b) :
    (Forward.treeLaw x a)
        {s | d < (s.vertices.filter fun v => s.graph.Adj 0 v).card} ≤
      (Forward.treeLaw x b)
        {s | d < (s.vertices.filter fun v => s.graph.Adj 0 v).card} :=
  Forward.treeLaw_rootDegree_tail_mono x d hab

example (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤)
    (ν : ProbabilityMeasure LocalTree.Tree)
    (hconv : Tendsto (fun n => ForwardInfiniteHistory.localProbabilityLaw (x n) n)
      atTop (𝓝 ν)) :
    ¬Summable (fun i => if y (i + 1) then (0 : ℝ)
      else 1 / (activeCount y (i + 1) : ℝ)) :=
  ForwardInfiniteHistory.not_summable_freezing_of_diagonal_local_tendsto x y hxy hτ hconv

example (μ : ℕ → ProbabilityMeasure LocalTree.Tree)
    (ν : ProbabilityMeasure LocalTree.Tree) (hconv : Tendsto μ atTop (𝓝 ν))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ d : ℕ, ∀ᶠ n in atTop, (μ n : Measure LocalTree.Tree).real
      {T | d < (T.val 1).card - 1} < δ :=
  LocalTree.eventually_rootDegree_tail_lt_of_tendsto hconv hδ

#print axioms Freezing1.Forward.rootDegree_le_of_legalOrHeld
#print axioms Freezing1.ForwardInfiniteHistory.fullLaw_rootDegree_monotone
#print axioms Freezing1.Forward.treeLaw_rootDegree_tail_mono
#print axioms Freezing1.Forward.treeLaw_rootDegree_tail_real_mono
#print axioms Freezing1.LocalTree.rootDegree_tail_isClopen
#print axioms Freezing1.LocalTree.rootDegree_tail_tendsto_zero
#print axioms Freezing1.LocalTree.eventually_rootDegree_tail_lt_of_tendsto
#print axioms Freezing1.Forward.diagonal_rootDegree_not_tight_of_summable_freezing
#print axioms Freezing1.ForwardInfiniteHistory.localProbabilityLaw_rootDegree_tail_real
#print axioms Freezing1.ForwardInfiniteHistory.not_summable_freezing_of_diagonal_local_tendsto
#print axioms Freezing1.ForwardInfiniteHistory.not_summable_freezing_of_local_tendsto
