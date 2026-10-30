module

import Freezing1.ForwardForestConditionalChainVariance

/-! Source-reconstructed conditional-moment checks by the integrating
reviewer. The forest implementation was written by another worker. -/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
open Freezing1 Freezing1.Forward

set_option backward.isDefEq.respectTransparency false

example (x : SignSequence) (C k₀ k : ℕ) (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x) (t : ℝ) (ht : 0 ≤ t) :
    (treeLaw x (C ^ (k + 1)))[(fun q => ((goodSet q C k₀ (k + 1) t).card : ℝ)) |
      MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] =ᵐ[treeLaw x (C ^ (k + 1))]
      (fun q => ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ) *
        blockTallCount q (C ^ k) (C ^ (k + 1)) t / (activeCount x (C ^ k) : ℝ)) :=
  condExp_goodSet_succ_given_forest x hC hk hb ht

example (x : SignSequence) (C k₀ k : ℕ) (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x) (t : ℝ) (ht : 0 ≤ t) :
    condVar (MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance)
      (fun q => ((goodSet q C k₀ (k + 1) t).card : ℝ)) (treeLaw x (C ^ (k + 1))) ≤ᵐ[treeLaw x (C ^ (k + 1))]
      (fun q => (componentMaximum q (C ^ k) : ℝ) *
        (treeLaw x (C ^ (k + 1)))[(fun r => ((goodSet r C k₀ (k + 1) t).card : ℝ)) |
          MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q) :=
  condVar_goodSet_succ_given_forest x hC hk hb ht

example (x : SignSequence) (a b : ℕ) (hab : a ≤ b)
    (hb : (b : ℕ∞) ≤ extinctionTime x) (G : State → Finset ℕ)
    (hG : ∀ s, HasHistory x a s → G s ⊆ s.active) (t : ℝ) (ht : 0 ≤ t) :
    (treeLaw x b)[(fun q => (markedTallCount G a t q : ℝ)) |
      MeasurableSpace.comap (pastBareForest x a) inferInstance] =ᵐ[treeLaw x b]
      (fun q => ((G (truncateAt q a)).card : ℝ) / (activeCount x a).toNat * blockTallCount q a b t) :=
  condExp_markedTallCount x hab hb G hG ht

#print axioms condExp_goodSet_succ_given_forest
#print axioms condVar_goodSet_succ_given_forest
#print axioms condExp_markedTallCount
#print axioms condExp_markedTallCount_centered_sq_le
#print axioms markedTallCount_rematching_average
#print axioms map_treeLaw_rematchState
#print axioms pastBareForest_rematchState
#print axioms bareForestTallCount_actual
#print axioms bareForestComponentMaximum_actual
