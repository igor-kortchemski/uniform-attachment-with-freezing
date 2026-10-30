module

import Freezing1.ConstructionEquivalence

/- Independently reconstructed T05 statement. Canonical identifiers retain the
root (0), incoming edge times, all frozen labels and the active vertex set. -/
open MeasureTheory
open Freezing1
open scoped Classical

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (Forward.treeLaw x n).map (fun s : Forward.State =>
      ({ vertices := s.vertices
         graph := s.graph
         active := s.active
         frozen := CanonicalTree.frozenPairs s.vertices id s.frozenAt } :
        CanonicalTree.Observable)) =
    (ReverseStamped.treeLaw x n).map (fun F : ReverseStamped.Forest =>
      ({ vertices := F.forest.vertices.image F.edgeTime
         graph := CanonicalTree.transportGraph F.forest.vertices F.edgeTime F.forest.graph
         active := (F.forest.vertices.filter fun v => CanonicalTree.reverseLabel v = none).image F.edgeTime
         frozen := CanonicalTree.frozenPairs F.forest.vertices F.edgeTime CanonicalTree.reverseLabel } :
        CanonicalTree.Observable)) := by
  exact CanonicalTree.construction_laws_eq x n hn

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (ReverseStamped.treeLaw x n).map CanonicalTree.reverseState = Forward.treeLaw x n :=
  CanonicalTree.reverseStateLaw_eq_forward_treeLaw x n hn

#print axioms CanonicalTree.construction_laws_eq
#print axioms CanonicalTree.reverseStateLaw_eq_forward_treeLaw
#print axioms CanonicalTree.reverseStateLaw_hasForwardHistory
#print axioms CanonicalTree.reverseState_historyShape
#print axioms CanonicalTree.reverseStateLaw_real_singleton_of_hasHistory
#print axioms CanonicalTree.terminalFiber_eq_activeOrbit
#print axioms Forward.HistoryShape.hasHistory
#print axioms probability_eq_of_ae_singleton_eq
