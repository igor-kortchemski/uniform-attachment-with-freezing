module

import Freezing1.BernoulliPairCouplingConclusions
import Freezing1.BernoulliPairCouplingComplete
import Freezing1.BernoulliPairCouplingSourceChecks

/-! Independent expanded source checks: one constructed space retains the
actual complete history, auxiliary drivers and monotone thinning. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
open Freezing1 Freezing1.BernoulliPairCoupling

set_option backward.isDefEq.respectTransparency false

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (u v : ℕ ⊕ ℕ) (a k : ℕ) (H : Base) :
    (completeLaw x n hn u v a k H).map (fun z => z.1.history) =
      ReverseHistory.blockHistoryLaw x a k H :=
  completeLaw_map_history x n hn u v a k H

example {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    (completeLaw x n hn u v a k H).map (fun z => (z.1.first, (z.1.second, z.2))) =
      (wordLaw (Reverse.stepParameter x n hn) a k).prod
        ((wordLaw (auxiliaryParameter x n hn) a k).prod
          (wordLaw (fun i => unitInterval.symm (Reverse.stepParameter x n hn i)) a k)) :=
  completeLaw_map_drivers hn hk hH hu hv

example {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    ∀ᵐ z ∂coupledBlockLaw x n hn u v a k H, ∀ j : Fin k,
      z.first j = ReverseHistory.phaseIncrement u (k - 1 - j.val) z.history ∧
      ReverseHistory.phaseIncrement v (k - 1 - j.val) z.history =
        if (ReverseHistory.stage z.history (k - j.val)).root u =
          (ReverseHistory.stage z.history (k - j.val)).root v
        then z.first j else z.second j * (1 - z.first j) :=
  coupledBlockLaw_increment_relations hn hk hH hu hv

example {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    ∀ᵐ z ∂coupledBlockLaw x n hn u v a k H,
      H.current.depth u + (∑ j, z.first j) = z.history.current.depth u ∧
      (H.current.root u = H.current.root v →
        z.history.current.root u = z.history.current.root v) ∧
      (z.history.current.root u ≠ z.history.current.root v →
        z.history.current.depth v ≤ H.current.depth v + ∑ j, z.second j) :=
  coupledBlockLaw_geometry hn hk hH hu hv

example {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    (completeLaw x n hn u v a k H).map
        (fun z => (z.1.first, fun j => z.1.second j * z.2 j)) =
      (wordLaw (Reverse.stepParameter x n hn) a k).prod
        (wordLaw (Reverse.stepParameter x n hn) a k) :=
  completeLaw_map_first_thinned hn hk hH hu hv

example {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    ∀ᵐ z ∂completeLaw x n hn u v a k H, ∀ j,
      z.1.second j * z.2 j ≤ z.1.second j :=
  completeLaw_thinning_le hn hk hH hu hv

example (p q : ℕ → unitInterval) (a k : ℕ)
    (hpq : ∀ i, a ≤ i → i < a + k → (1 - (p i : ℝ)) * (q i : ℝ) = p i) (t : ℝ) :
    (wordLaw q a k).real {w | t < ((∑ j, w j : ℕ) : ℝ)} -
      (wordLaw p a k).real {w | t < ((∑ j, w j : ℕ) : ℝ)} =
        (thinningLaw p q a k).real {z |
          t < ((∑ j, z.1 j : ℕ) : ℝ) ∧ ((∑ j, z.1 j * z.2 j : ℕ) : ℝ) ≤ t} :=
  thinningLaw_tail_difference p q a k hpq t

example (p q : ℕ → unitInterval) (a k : ℕ)
    (hpq : ∀ i, a ≤ i → i < a + k → (1 - (p i : ℝ)) * (q i : ℝ) = p i) :
    (∫ z, ((wordSum z.1 - ∑ j, z.1 j * z.2 j : ℕ) : ℝ) ∂thinningLaw p q a k) =
      ∑ j : Fin k, ((q (a + k - 1 - j.val) : ℝ) - p (a + k - 1 - j.val)) :=
  thinningLaw_discrepancy_integral p q a k hpq

example (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (a k : ℕ) (hk : a + k ≤ n) :
    auxiliaryError x n hn a k = ∑ i ∈ Finset.Ico a (a + k),
      if x (i + 1) then
        1 / ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1)) else 0 :=
  auxiliaryError_eq_reciprocal_sum x n hn a k hk

example {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.roots) (hv : v ∈ H.current.roots) (huv : u ≠ v) (t : ℝ) :
    (ReverseHistory.blockHistoryLaw x a k H).real
        {G | t < (G.current.depth u : ℝ) ∧ t < (G.current.depth v : ℝ)} ≤
      (ReverseHistory.blockHistoryLaw x a k H).real {G | t < (G.current.depth u : ℝ)} *
        (ReverseHistory.blockHistoryLaw x a k H).real {G | t < (G.current.depth v : ℝ)} +
        (∑ i ∈ Finset.Ico a (a + k), if x (i + 1) then
          1 / ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1)) else 0) +
        Reverse.blockCoalescenceRisk x a k := by
  have h := actual_pair_tail_le_product_add_errors hn hk hH hu hv huv t
  change _ ≤ _ + auxiliaryError x n hn a k + _ at h
  rwa [auxiliaryError_eq_reciprocal_sum x n hn a k hk] at h

example (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hn : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A c)
    (C : ℕ) (hC : 1 < C) :
    ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ (a : ℕ) (_hbn : a * C ≤ n), A n ≤ (a : ℝ) →
        ((a * C : ℕ) : ℝ) ≤ ε * n →
        ∀ H : Base, Reverse.ValidAt (x n) n (a * C) H.current →
          ∀ u ∈ H.current.roots, ∀ v ∈ H.current.roots, u ≠ v → ∀ t : ℝ,
            (ReverseHistory.blockHistoryLaw (x n) a (a * C - a) H).real
                {G | t < (G.current.depth u : ℝ) ∧ t < (G.current.depth v : ℝ)} ≤
              (ReverseHistory.blockHistoryLaw (x n) a (a * C - a) H).real
                  {G | t < (G.current.depth u : ℝ)} *
                (ReverseHistory.blockHistoryLaw (x n) a (a * C - a) H).real
                  {G | t < (G.current.depth v : ℝ)} + L / a :=
  uniform_geometric_actual_pair_tail x A hc hn hA hnear C hC

example :
    let x : SignSequence := fun _ => true
    let H := ReverseHistory.initial x 1
    let u : ℕ ⊕ ℕ := .inl 0
    let v : ℕ ⊕ ℕ := .inl 1
    H.current.root u ≠ H.current.root v ∧
      (Reverse.transitionLaw x 0 H.current).real {F |
        ReverseHistory.heightIncrement u (ReverseHistory.push H F) = 1 ∧
        ReverseHistory.coalescenceTime 1 (ReverseHistory.push H F) u v ≤ 0 ∧
        F.root u = F.root v} = (1 / 2 : ℝ) :=
  source_current_merge_boundary

#print axioms augmentLaw_map_history
#print axioms augmentLaw_map_pair
#print axioms stepLaw_map_drivers
#print axioms stepLaw_relation
#print axioms wordLaw_independent
#print axioms pairWordLaw_independent
#print axioms coupledBlockLaw_map_history
#print axioms coupledBlockLaw_map_drivers
#print axioms coupledBlockLaw_increment_relations
#print axioms coupledBlockLaw_geometry
#print axioms thinningLaw_map
#print axioms thinningLaw_tail_difference
#print axioms thinningLaw_discrepancy_integral
#print axioms thinningLaw_tail_difference_le
#print axioms completeLaw_map_history
#print axioms completeLaw_map_first_thinned
#print axioms actual_pair_tail_le_product_add_errors
#print axioms auxiliaryError_eq_reciprocal_sum
#print axioms uniform_geometric_actual_pair_tail
#print axioms source_current_merge_boundary
