module

import Freezing1.GeometricChainPositiveCutoff
import Freezing1.ForwardForestConditionalChainCovariance
import Freezing1.ForwardForestChainComponentMarks
import Freezing1.ForwardForestUpperPrefix

/-! Independent reconstruction of source positive-index filters, graph
chains, and conditional covariance by the integrating reviewer. -/

open Filter MeasureTheory
open scoped Classical ENNReal
open Freezing1 Freezing1.Forward

example (s : State) (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ) (n k : ℕ)
    (t : ℝ) (hA : 0 < A n) :
    goodSet s C (max 1 (chainLowerIndex C A n)) k t = s.active.filter fun v =>
      ∀ ell : ℕ, 1 ≤ ell → ell < k → A n ≤ ((C ^ ell : ℕ) : ℝ) →
        t < (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ) :=
  goodSet_eq_source_filter_positiveCutoff s C hC A n k t hA

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
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x) {t : ℝ}
    (ht : 0 ≤ t) (v w : ℕ) :
    ∀ᵐ q ∂treeLaw x (C ^ (k + 1)),
      v ∈ (starForest q (C ^ k)).active → w ∈ (starForest q (C ^ k)).active →
      cutAncestor q (C ^ k) v ≠ cutAncestor q (C ^ k) w →
      (treeLaw x (C ^ (k + 1)))[(fun r =>
        (if v ∈ goodSet r C k₀ (k + 1) t then 1 else 0 : ℝ) *
        (if w ∈ goodSet r C k₀ (k + 1) t then 1 else 0 : ℝ)) |
          MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q -
        (treeLaw x (C ^ (k + 1)))[(fun r =>
          (if v ∈ goodSet r C k₀ (k + 1) t then 1 else 0 : ℝ)) |
          MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q *
        (treeLaw x (C ^ (k + 1)))[(fun r =>
          (if w ∈ goodSet r C k₀ (k + 1) t then 1 else 0 : ℝ)) |
          MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q ≤ 0 :=
  goodVertices_conditionally_negatively_correlated x hC hk hb ht v w

#print axioms goodSet_eq_source_filter_positiveCutoff
#print axioms goodSet_truncate_eq_source_filter_positiveCutoff
#print axioms treeLaw_source_good_graph_chain
#print axioms treeLaw_good_graph_ancestor_chain
#print axioms treeLaw_prefix_slotForest_at_upper
#print axioms indepFun_prefix_bareForest_at_upper
#print axioms goodVertices_conditionally_negatively_correlated
#print axioms goodVertexIndicators_same_component
