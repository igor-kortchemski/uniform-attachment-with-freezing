module

import Freezing1.ForwardDegreeLimits

open Freezing1 Filter MeasureTheory
open scoped Topology BigOperators Classical

example (x : SignSequence) (n d : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (Forward.treeLaw x n).real
      {s | 0 ∈ s.active ∧ (s.vertices.filter fun v => s.graph.Adj 0 v).card ≤ d} ≤
      Real.exp (θ * (d : ℝ) + (Real.exp (-θ) - 1) *
        ∑ i ∈ Finset.range n, (if x (i + 1) then 1 / (activeCount x i : ℝ) else 0)) :=
  Forward.treeLaw_active_bounded_degree_le x n d hn hθ

example (x : SignSequence) (hτ : extinctionTime x = ⊤) (d : ℕ) :
    Tendsto (fun n => (Forward.treeLaw x n)
      {s | 0 ∈ s.active ∧ (s.vertices.filter fun v => s.graph.Adj 0 v).card ≤ d})
      atTop (𝓝 0) :=
  Forward.treeLaw_active_bounded_degree_tendsto_zero_ennreal x hτ d

example (x : SignSequence) (hτ : extinctionTime x = ⊤)
    (hs : Summable (fun i => if x (i + 1) then (0 : ℝ)
      else 1 / (activeCount x (i + 1) : ℝ))) :
    ∃ δ > 0, ∀ d : ℕ, ∀ᶠ n in atTop,
      δ ≤ (Forward.treeLaw x n).real
        {s | d < (s.vertices.filter fun v => s.graph.Adj 0 v).card} :=
  Forward.rootDegree_not_tight_of_summable_freezing x hτ hs

#print axioms Freezing1.Forward.rootDegree
#print axioms Freezing1.Forward.rootDegree_initial
#print axioms Freezing1.Forward.rootDegree_le_vertices_card
#print axioms Freezing1.Forward.rootNeighbors_attach
#print axioms Freezing1.Forward.rootDegree_attach
#print axioms Freezing1.Forward.rootDegree_freeze
#print axioms Freezing1.Forward.rootDegree_step
#print axioms Freezing1.Forward.survivingRootWeight
#print axioms Freezing1.Forward.survivingRootWeight_bounds
#print axioms Freezing1.Forward.integrable_survivingRootWeight
#print axioms Freezing1.Forward.survivingRootWeight_step
#print axioms Freezing1.Forward.degreeSurvivalFactor
#print axioms Freezing1.Forward.transitionLaw_survivingRootWeight
#print axioms Freezing1.Forward.prod_Ioc_zero_eq_range_succ
#print axioms Freezing1.Forward.integral_continuationLaw_succ_survivingRootWeight
#print axioms Freezing1.Forward.continuationLaw_survivingRootWeight_product
#print axioms Freezing1.Forward.treeLaw_survivingRootWeight_product
#print axioms Freezing1.Forward.treeLaw_root_survival_product
#print axioms Freezing1.Forward.degreeSurvivalFactor_succ
#print axioms Freezing1.Forward.degree_attachmentFactor_nonneg
#print axioms Freezing1.Forward.treeLaw_survivingRootWeight_le
#print axioms Freezing1.Forward.treeLaw_active_bounded_degree_le_weight
#print axioms Freezing1.Forward.treeLaw_active_bounded_degree_le
#print axioms Freezing1.Forward.treeLaw_active_bounded_degree_tendsto_zero
#print axioms Freezing1.Forward.treeLaw_active_bounded_degree_tendsto_zero_ennreal
#print axioms Freezing1.Forward.treeLaw_root_survival_tendsto_of_summable
#print axioms Freezing1.Forward.rootDegree_not_tight_of_summable_freezing
