module

import Freezing1.RootedForestFiniteDistance
import Freezing1.ReverseHistoryDistance

open Freezing1 MeasureTheory
open Freezing1.ReverseHistory
open scoped Classical

set_option backward.isDefEq.respectTransparency false

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) :
    ∀ᵐ H ∂fullLaw x n,
      0 ≤ (H.current.depth u : ℝ) + H.current.depth v - H.current.graph.dist u v ∧
      (H.current.depth u : ℝ) + H.current.depth v - H.current.graph.dist u v ≤
        2 * (@Nat.findGreatest (fun i =>
          u ∈ (stage H i).vertices ∧ v ∈ (stage H i).vertices ∧
          (stage H i).root u = (stage H i).root v)
            (fun _ => Classical.propDecidable _) n : ℝ) := by
  have hh := fullLaw_distance_defect_bounds x n hn hu hv
  unfold coalescenceTime Coalesced at hh
  simpa only [stage_zero] using hh

#print axioms Freezing1.RootedForest.dist_eq_of_le_isAcyclic
#print axioms Freezing1.RootedForest.dist_le_depth_add_depth
#print axioms Freezing1.RootedForest.graph_le_join
#print axioms Freezing1.RootedForest.join_preserves_dist
#print axioms Freezing1.RootedForest.adjoin_preserves_dist
#print axioms Freezing1.RootedForest.potential_le_add_length
#print axioms Freezing1.RootedForest.joinPotential
#print axioms Freezing1.RootedForest.joinPotential_le_of_old_adj
#print axioms Freezing1.RootedForest.joinPotential_le_of_join_adj
#print axioms Freezing1.RootedForest.join_dist_eq_depth_add_depth
#print axioms Freezing1.RootedForest.graph_le_joinChoice
#print axioms Freezing1.RootedForest.joinChoice_isAcyclic
#print axioms Freezing1.RootedForest.joinChoice_preserves_dist
#print axioms Freezing1.RootedForest.joinChoice_new_coalescence_dist
#print axioms Freezing1.RootedForest.toGraph_dist_eq
#print axioms Freezing1.RootedForest.depth_eq_tree_dist
#print axioms Freezing1.Reverse.insertLabel_graph
#print axioms Freezing1.Reverse.DistanceStep
#print axioms Freezing1.Reverse.transitionLaw_distanceStep
#print axioms Freezing1.ReverseHistory.DistanceChain
#print axioms Freezing1.ReverseHistory.lawAfter_distanceChain
#print axioms Freezing1.ReverseHistory.dist_stage_zero_eq_of_coalesced
#print axioms Freezing1.ReverseHistory.fullLaw_phaseIncrement_le_one
#print axioms Freezing1.ReverseHistory.fullLaw_depth_zero_le_depth_phase_add
#print axioms Freezing1.ReverseHistory.fullLaw_depth_le_birth
#print axioms Freezing1.ReverseHistory.fullLaw_coalescenceTime_lt_min_birth
#print axioms Freezing1.ReverseHistory.fullLaw_dist_depth_bounds
#print axioms Freezing1.ReverseHistory.fullLaw_distance_defect_bounds
