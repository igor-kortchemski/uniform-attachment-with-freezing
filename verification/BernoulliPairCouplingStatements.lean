module

import Freezing1.BernoulliPairCouplingConclusions
import Freezing1.BernoulliPairCouplingComplete
import Freezing1.BernoulliPairCouplingSourceChecks

open Filter MeasureTheory ProbabilityTheory
open Freezing1 Freezing1.BernoulliPairCoupling
open scoped Classical ENNReal BigOperators Topology

set_option backward.isDefEq.respectTransparency false

-- Authored source reconstruction: every auxiliary coin lives beside the original whole history.
example (x : SignSequence) (n a k : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (u v : ℕ ⊕ ℕ) (H : ReverseHistory.History) :
    (completeLaw x n hn u v a k H).map (fun z => z.1.history) =
      ReverseHistory.blockHistoryLaw x a k H :=
  completeLaw_map_history x n hn u v a k H

-- The source parameters are exactly the attachment-masked reciprocal populations.
example (x : SignSequence) (n a k : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (hk : a + k ≤ n) (j : Fin k) :
    (descendingParameter (Reverse.stepParameter x n hn) a k j : ℝ) =
      if x (a + k - j.val) then 1 / (activeCount x (a + k - j.val) : ℝ) else 0 := by
  have hi : a + k - 1 - j.val < n := by have := j.isLt; omega
  have he : a + k - 1 - j.val + 1 = a + k - j.val := by have := j.isLt; omega
  dsimp only [descendingParameter]
  rw [Reverse.stepParameter_of_lt x n hn hi, Reverse.attachmentParameter_coe, he]

-- Two full driver arrays, and not merely their sums, have the actual independent law.
example (x : SignSequence) (n a k : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (hk : a + k ≤ n) (H : ReverseHistory.History)
    (hH : Reverse.ValidAt x n (a + k) H.current) (u v : ℕ ⊕ ℕ)
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    (completeLaw x n hn u v a k H).map (fun z => (z.1.first, (z.1.second, z.2))) =
      (bernoulliProductLaw (fun j : Fin k => Reverse.stepParameter x n hn (a + k - 1 - j.val))).prod
        ((bernoulliProductLaw (fun j : Fin k => auxiliaryParameter x n hn (a + k - 1 - j.val))).prod
          (bernoulliProductLaw (fun j : Fin k =>
            unitInterval.symm (Reverse.stepParameter x n hn (a + k - 1 - j.val))))) :=
  completeLaw_map_drivers hn hk hH hu hv

-- Exact source expectation, including the mask and both reciprocal factors.
example (x : SignSequence) (n a k : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (hk : a + k ≤ n) :
    (∫ z, (thinningDiscrepancy z : ℝ)
      ∂thinningLaw (Reverse.stepParameter x n hn) (auxiliaryParameter x n hn) a k) =
      ∑ i ∈ Finset.Ico a (a + k), if x (i + 1) then
        1 / ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1)) else 0 := by
  calc
    _ = auxiliaryError x n hn a k := thinningLaw_discrepancy_integral _ _ _ _
      (fun i _ hi => step_parameters_relation x n hn (hi.trans_le hk))
    _ = _ := auxiliaryError_eq_reciprocal_sum x n hn a k hk

-- The final source uniformity has no assumptions about auxiliary independence or a coupling.
example (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hn : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A c)
    (C : ℕ) (hC : 1 < C) :
    ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ (a : ℕ) (_hbn : a * C ≤ n), A n ≤ (a : ℝ) →
        ((a * C : ℕ) : ℝ) ≤ ε * n →
        ∀ H : ReverseHistory.History, Reverse.ValidAt (x n) n (a * C) H.current →
          ∀ u ∈ H.current.roots, ∀ v ∈ H.current.roots, u ≠ v → ∀ t : ℝ,
            (ReverseHistory.blockHistoryLaw (x n) a (a * C - a) H).real
                {H' | t < (H'.current.depth u : ℝ) ∧ t < (H'.current.depth v : ℝ)} ≤
              (ReverseHistory.blockHistoryLaw (x n) a (a * C - a) H).real
                  {H' | t < (H'.current.depth u : ℝ)} *
                (ReverseHistory.blockHistoryLaw (x n) a (a * C - a) H).real
                  {H' | t < (H'.current.depth v : ℝ)} + L / a :=
  uniform_geometric_actual_pair_tail x A hc hn hA hnear C hC

#print axioms augmentLaw_map_pair
#print axioms augmentLaw_relation
#print axioms step_parameters_relation
#print axioms stepLaw_map_drivers
#print axioms stepLaw_relation
#print axioms pairWordLaw_succ
#print axioms coupledBlockLaw_map_history
#print axioms coupledBlockLaw_map_drivers
#print axioms coupledBlockLaw_increment_relations
#print axioms coupledBlockLaw_geometry
#print axioms thinningLaw_map
#print axioms thinningLaw_le
#print axioms thinningLaw_discrepancy_integral
#print axioms thinningLaw_tail_difference
#print axioms thinningLaw_tail_difference_le
#print axioms completeLaw_map_history
#print axioms completeLaw_map_drivers
#print axioms completeLaw_map_first_thinned
#print axioms completeLaw_thinning_le
#print axioms actual_pair_tail_le_product_add_errors
#print axioms auxiliaryError_eq_reciprocal_sum
#print axioms actual_separated_tail_le_enlarged_square
#print axioms uniform_geometric_actual_pair_tail
#print axioms source_current_merge_boundary
