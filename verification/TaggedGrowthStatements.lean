module

import Freezing1.ForwardGoodChainStep

open Freezing1 MeasureTheory
open scoped ENNReal Classical

example {x : SignSequence} {a k : ℕ} {s : Forward.State}
    (hs : Forward.PhaseData x a s) (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    (Forward.continuationLaw x a k s).map
        (fun q => q.active.val.map (fun v =>
          (Forward.cutAncestor q a v, Forward.cutHeight q a v))) =
      TaggedPopulation.continuationLaw x a k
        (s.active.val.map (fun r => (r, 0))) :=
  Forward.continuationLaw_taggedPopulation_at_cut hs hn

example {x : SignSequence} {s : Forward.State} {C k₀ k : ℕ}
    (hs : Forward.HasHistory x (C ^ k) s) (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hn : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : (3 : ℝ) ≤ (C ^ k : ℕ)) (t : ℝ) (b M : ℝ) (hb : 0 < b) (hM : 0 ≤ M)
    (hg : b ≤ ((Forward.goodSet s C k₀ k t).card : ℝ)) :
    (Forward.continuationLaw x (C ^ k) (C ^ (k + 1) - C ^ k) s).real
      {q | 4 * ((C ^ k : ℕ) : ℝ) ≤
          (Forward.blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) ∧
        (Forward.componentMaximum q (C ^ k) : ℝ) ≤ M ∧
        ((Forward.goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * b} ≤ 3 * M / b :=
  Forward.continuationLaw_goodSet_growth_failure_le hs hC hk hn ha t hb hM hg

#print axioms Freezing1.map_uniformFinset_eq_multisetUniform
#print axioms Freezing1.TaggedPopulation.continuationLaw_initial_invariant
#print axioms Freezing1.TaggedPopulation.goodTall_eq_weightedPermutationCount
#print axioms Freezing1.integral_permutation_action_indicator
#print axioms Freezing1.TaggedPopulation.continuationLaw_goodTall_growth_failure_le
#print axioms Freezing1.Forward.continuationLaw_taggedPopulation_at_cut
#print axioms Freezing1.Forward.totalTall_taggedPopulation
#print axioms Freezing1.Forward.continuationLaw_goodSet_growth_failure_le
