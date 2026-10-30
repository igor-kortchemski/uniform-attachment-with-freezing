module

import Freezing1.ForwardBlockIndependence

open Freezing1 MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

example (s : Forward.State) (a r : ℕ) (hr : r ≤ a) :
    TaggedPopulation.rootPopulation (Forward.taggedPopulation s a) r +
      (if (r, 0) ∈ Forward.taggedPopulation s a then 0 else 1) =
        (insert r (Forward.componentActive s a r)).card :=
  Forward.rootPopulationWithRoot_taggedPopulation s a r hr

example {x : SignSequence} {a k : ℕ} {s : Forward.State}
    (hs : Forward.HasHistory x a s)
    (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) (t : ℝ) :
    (Forward.continuationLaw x a k s).map
        (fun q => (Forward.blockTallCount q a (a + k) t, Forward.componentMaximum q a)) =
      TaggedPopulation.blockStatisticsLaw x a k (activeCount x a).toNat t :=
  Forward.continuationLaw_blockStatistics hs hn t

example (x : SignSequence) {n a b : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hab : a ≤ b) (hb : b ≤ n) (t : ℝ) :
    IndepFun (fun q => Forward.truncateAt q a)
      (fun q => (Forward.blockTallCount q a b t,
        Forward.componentMaximum (Forward.truncateAt q b) a)) (Forward.treeLaw x n) :=
  Forward.indepFun_prefix_blockStatistics x hn hab hb t

#print axioms Freezing1.TaggedPopulation.blockStatistics_relabel
#print axioms Freezing1.TaggedPopulation.map_blockStatistics_eq_of_card_eq
#print axioms Freezing1.Forward.zero_mem_taggedPopulation_iff
#print axioms Freezing1.Forward.componentMaximum_taggedPopulation
#print axioms Freezing1.Forward.continuationLaw_blockStatistics
#print axioms Freezing1.Forward.treeLaw_prefix_blockStatistics_event
#print axioms Freezing1.Forward.indepFun_prefix_blockStatistics
