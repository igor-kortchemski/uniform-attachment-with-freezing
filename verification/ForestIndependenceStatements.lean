module

import Freezing1.ForwardForestBareMatching
import Freezing1.ForwardForestRootMatchingEquiv
import Freezing1.ForwardBlockHeightAncestor

/-! Independent integrating-reviewer reconstruction of the full-forest
probability interfaces. The bare and augmented forests remain distinct. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
open Freezing1 Freezing1.Forward

example (x : SignSequence) (a b : ℕ) (hab : a ≤ b)
    (hb : (b : ℕ∞) ≤ extinctionTime x) :
    (treeLaw x b).map (fun t => (truncateAt t a, slotForest t a)) =
      (treeLaw x a).prod
        (continuationLaw x a (b - a) (forestInitial (Finset.range (activeCount x a).toNat))) :=
  treeLaw_prefix_slotForest x hab hb

example (x : SignSequence) (a b : ℕ) (hab : a ≤ b)
    (hb : (b : ℕ∞) ≤ extinctionTime x) :
    IndepFun (fun t => truncateAt t a)
      (fun t => bareSlotOrbit (activeCount x a).toNat (slotForest t a)) (treeLaw x b) :=
  indepFun_prefix_bareForest x hab hb

example (x : SignSequence) (a b : ℕ) (t : State) (ht : HasHistory x b t)
    (hb : (b : ℕ∞) ≤ extinctionTime x) :
    reconstructSlotForest x a b (truncateAt t a) (slotForest t a) = t :=
  reconstructSlotForest_actual ht hb

example (x : SignSequence) (a b : ℕ) (hab : a ≤ b)
    (hb : (b : ℕ∞) ≤ extinctionTime x) :
    let m := (activeCount x a).toNat
    (treeLaw x b).map (fun t => (truncateAt t a, bareSlotOrbit m (slotForest t a), t)) =
      (treeLaw x a).bind (fun past => (forestSlotLaw x a (b - a) m).bind
        (fun F => (uniformPermutationLaw (Fin m)).map
          (fun σ => (past, bareSlotOrbit m F,
            reconstructSlotForest x a b past (F.relabel (rootSlotPermutation m σ)))))) :=
  treeLaw_uniform_root_matching_bare x hab hb

example (a : ℕ) (roots : Finset ℕ) (hr : ∀ r ∈ roots, r ≤ a) :
    Nonempty (Equiv.Perm (Fin roots.card) ≃ (Fin roots.card ≃ roots)) :=
  ⟨rootMatchingParametrization a roots hr⟩

example (n a b : ℕ) (s : State) (hs : ValidAt n s) (hab : a ≤ b)
    (v : ℕ) (hv : v ∈ s.vertices) :
    cutHeight s a v - cutHeight s b v = cutHeight s a (cutAncestor s b v) :=
  blockHeight_eq_cutHeight_ancestor hs hab hv

#print axioms treeLaw_prefix_slotForest
#print axioms indepFun_prefix_bareForest
#print axioms reconstructSlotForest_actual
#print axioms treeLaw_uniform_root_matching_bare
#print axioms rootMatchingParametrization
#print axioms blockHeight_eq_cutHeight_ancestor
#print axioms star_activity_counterexample
