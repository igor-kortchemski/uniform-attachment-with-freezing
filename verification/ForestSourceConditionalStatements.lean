module

import Freezing1.ForwardForestConditionalChainCovariance
import Freezing1.ForwardForestConditionalExchangeability
import Freezing1.ForwardForestChainComponentMarks
import Freezing1.ForwardForestConditionalChebyshev
import Freezing1.GeometricChainPositiveCutoff
import Freezing1.ForwardHeightChainTelescoping
import Freezing1.ForwardForestUpperPrefix

/- Authored expanded source-interface probe. Independent source review is
recorded separately; no audit premise occurs in a mathematical result. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
open Freezing1 Freezing1.Forward

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

example {n : ℕ} {s : State} (hs : ValidAt n s) (C : ℕ) (hC : 1 < C)
    (A : ℕ → ℝ) (N k : ℕ) (t : ℝ) (hA : 0 < A N) :
    goodSet (truncateAt s (C ^ k)) C (max 1 (chainLowerIndex C A N)) k t =
      (truncateAt s (C ^ k)).active.filter fun v => ∀ ell : ℕ,
        1 ≤ ell → ell < k → A N ≤ ((C ^ ell : ℕ) : ℝ) →
          t < (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ) :=
  goodSet_truncate_eq_source_filter_positiveCutoff hs C hC A N k t hA

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ) (k : ℕ)
    (hk : max 1 (chainLowerIndex C A n) ≤ k) (t : ℝ) (hA : 0 < A n) :
    ∀ᵐ s ∂treeLaw x n, ∀ v ∈ (truncateAt s (C ^ k)).active,
      (∀ ell : ℕ, 1 ≤ ell → ell < k → A n ≤ ((C ^ ell : ℕ) : ℝ) →
        t < (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ)) →
      ∃ V : ℕ → ℕ, V k = v ∧
        (∀ i ∈ Finset.Icc (max 1 (chainLowerIndex C A n)) k,
          V i ∈ (truncateAt s (C ^ i)).active) ∧
        (∀ i ∈ Finset.Ico (max 1 (chainLowerIndex C A n)) k,
          ∃ d : ℕ, (s.parent^[d]) (V (i + 1)) = V i ∧
            t < (s.graph.dist (V i) (V (i + 1)) : ℝ)) ∧
        ((k - max 1 (chainLowerIndex C A n) : ℕ) : ℝ) * t ≤ (s.height v : ℝ) :=
  treeLaw_source_good_graph_chain x n hn C hC A k hk t hA

example (x : SignSequence) {C k₀ k : ℕ} (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x) {t : ℝ} (ht : 0 ≤ t) (v w : ℕ) :
    ∀ᵐ q ∂treeLaw x (C ^ (k + 1)),
      v ∈ (starForest q (C ^ k)).active → w ∈ (starForest q (C ^ k)).active →
      cutAncestor q (C ^ k) v ≠ cutAncestor q (C ^ k) w →
      (treeLaw x (C ^ (k + 1)))[(fun r =>
        (if v ∈ goodSet r C k₀ (k + 1) t then (1 : ℝ) else 0) *
        (if w ∈ goodSet r C k₀ (k + 1) t then (1 : ℝ) else 0)) |
        MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q -
        (treeLaw x (C ^ (k + 1)))[(fun r => if v ∈ goodSet r C k₀ (k + 1) t then (1 : ℝ) else 0) |
          MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q *
        (treeLaw x (C ^ (k + 1)))[(fun r => if w ∈ goodSet r C k₀ (k + 1) t then (1 : ℝ) else 0) |
          MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q ≤ 0 :=
  goodVertices_conditionally_negatively_correlated x hC hk hb ht v w

example (x : SignSequence) {C k₀ k b : ℕ} (hC : 1 ≤ C)
    (hab : C ^ k ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) (t : ℝ) :
    ∀ᵐ q ∂treeLaw x b, ∀ v ∈ (starForest q (C ^ k)).active,
      ∀ w ∈ (starForest q (C ^ k)).active,
      cutAncestor q (C ^ k) v = cutAncestor q (C ^ k) w →
        ((∀ ell ∈ Finset.Ico k₀ k, t < (blockHeight q (C ^ ell) (C ^ (ell + 1)) v : ℝ)) ↔
          ∀ ell ∈ Finset.Ico k₀ k, t < (blockHeight q (C ^ ell) (C ^ (ell + 1)) w : ℝ)) :=
  oldBlockTests_star_same_component x hC hab hb t

example (x : SignSequence) {C k₀ k : ℕ} (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : 3 ≤ C ^ k) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ q ∂treeLaw x (C ^ (k + 1)),
      (2 : ℝ) ^ k ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ) →
      4 * (C ^ k : ℝ) ≤ (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) →
      (componentMaximum q (C ^ k) : ℝ) ≤ (k : ℝ) ^ 3 →
      (treeLaw x (C ^ (k + 1)))[(fun r =>
          if ((goodSet r C k₀ (k + 1) t).card : ℝ) < (2 : ℝ) ^ (k + 1) then (1 : ℝ) else 0) |
        MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q ≤
          3 * (k : ℝ) ^ 3 / (2 : ℝ) ^ k :=
  condExp_goodSet_doubling_on_source_event x hC hk hb ha ht

example (x : SignSequence) :
    ∀ᵐ H ∂ForwardInfiniteHistory.fullLaw x, ∀ R : ℕ → ℕ, ∀ m n : ℕ,
      R 0 = 0 → R m = n →
      (∑ i ∈ Finset.range m, ((treeHeight (H (R (i + 1))) : ℝ) - treeHeight (H (R i)))) =
        (treeHeight (H n) : ℝ) :=
  fullLaw_treeHeight_chain_telescopes x

example (x : SignSequence) {n a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    IndepFun (fun q => truncateAt q a)
      (fun q => bareSlotOrbit (activeCount x a).toNat (slotForest (truncateAt q b) a)) (treeLaw x n) :=
  indepFun_prefix_bareForest_at_upper x hab hbn hn

example (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (σ : Equiv.Perm (Fin (activeCount x a).toNat)) (A : Set State) :
    (treeLaw x b)[(fun q => if rematchState x a b σ q ∈ A then (1 : ℝ) else 0) |
      MeasurableSpace.comap (fun q => truncateAt q a) inferInstance] =ᵐ[treeLaw x b]
      (treeLaw x b)[(fun q => if q ∈ A then (1 : ℝ) else 0) |
        MeasurableSpace.comap (fun q => truncateAt q a) inferInstance] :=
  condExp_rematching_event_given_prefix x hab hb σ A

#print axioms treeLaw_prefix_slotForest_at_upper
#print axioms indepFun_prefix_bareForest_at_upper
#print axioms condExp_rematchState_given_prefix
#print axioms condExp_rematchState_given_past_forest
#print axioms condExp_rematching_event_given_prefix
#print axioms fullLaw_treeHeight_chain_telescopes
#print axioms cutAncestor_truncate_of_mem
#print axioms goodSet_truncate_eq_source_filter
#print axioms ValidAt.cutAncestor_path_data
#print axioms ValidAt.dist_cutAncestor_eq_cutHeight
#print axioms HistoryShape.cutAncestor_historically_active
#print axioms treeLaw_good_graph_ancestor_chain
#print axioms mem_positiveChainInterval_iff_source
#print axioms eventually_positiveChainLowerIndex_eq
#print axioms goodSet_truncate_eq_source_filter_positiveCutoff
#print axioms treeLaw_source_good_graph_chain
#print axioms treeLaw_goodSet_succ_eq_filter
#print axioms goodVertexIndicator_succ_zero_before_cut
#print axioms treeLaw_oldBlockTests_star_mark
#print axioms oldBlockTests_star_same_component
#print axioms goodVertices_next_same_component_iff_oldRoot
#print axioms condExp_markedVertexIndicators_pair_le
#print axioms goodVertices_conditionally_negatively_correlated
#print axioms condExp_relativeLowerIndicator_le
#print axioms condExp_growthIndicator_le
#print axioms goodSet_condExp_square_integrable
#print axioms condExp_goodSet_relative_lower_given_forest
#print axioms condExp_goodSet_doubling_on_favorable_forest
#print axioms condExp_goodSet_doubling_on_source_event
