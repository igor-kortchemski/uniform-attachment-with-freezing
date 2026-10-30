module

import Solution.SameLaw

open MeasureTheory
open scoped Classical ENNReal

namespace Freezing1

-- Expand both actual observable samplers, rather than only their law aliases.
example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (Forward.treeLaw x n).map (fun s : Forward.State =>
      ({ vertices := s.vertices, graph := s.graph, active := s.active,
         frozen := CanonicalTree.frozenPairs s.vertices id s.frozenAt } :
        CanonicalTree.Observable)) =
    (ReverseStamped.treeLaw x n).map (fun F : ReverseStamped.Forest =>
      ({ vertices := F.forest.vertices.image F.edgeTime,
         graph := CanonicalTree.transportGraph F.forest.vertices F.edgeTime F.forest.graph,
         active := (F.forest.vertices.filter fun v => CanonicalTree.reverseLabel v = none).image
           F.edgeTime,
         frozen := CanonicalTree.frozenPairs F.forest.vertices F.edgeTime
           CanonicalTree.reverseLabel } : CanonicalTree.Observable)) :=
  CanonicalTree.construction_laws_eq x n hn

-- The source domain contains every horizon of the all-positive schedule.
example : extinctionTime (fun _ => true) = ⊤ := by
  apply (extinctionTime_eq_top_iff _).mpr
  intro n
  simp only [activeCount, ↓reduceIte, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  omega

-- The zero-step boundary is included, without an added survival hypothesis.
example (x : SignSequence) :
    CanonicalTree.forwardLaw x 0 = CanonicalTree.reverseLaw x 0 :=
  CanonicalTree.construction_laws_eq x 0 (by simp)

-- Frozen labels, rather than only the unlabelled graph, belong to the observable.
example (s : Forward.State) (v t : ℕ) :
    (v, t) ∈ (CanonicalTree.forward s).frozen ↔
      v ∈ s.vertices ∧ s.frozenAt v = some t := CanonicalTree.forward_frozen_iff

#print axioms CanonicalTree.construction_laws_eq
#print axioms CanonicalTree.reverseStateLaw_eq_forward_treeLaw
#print axioms ReverseStamped.treeLaw_canonical_ids
#print axioms CanonicalTree.treeLaw_reverse_graph_isomorphic
#print axioms Forward.treeLaw_valid

end Freezing1
