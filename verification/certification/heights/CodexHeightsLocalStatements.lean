module

import Solution.Heights
import Solution.LocalLimits

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal BigOperators

namespace CandidateHeightsLocalReview

open Freezing1

example (x : ℕ → SignSequence)
    (hs : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm
      (fun k : ℕ => (k : ℝ) / heightScale (x n) n - 1)
      (ENNReal.ofReal p) (Forward.uniformActiveHeightLaw (x n) n)) atTop (𝓝 0) :=
  uniform_active_height_tendsto_Lp x hs hp

example (x : ℕ → SignSequence)
    (hs : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n => (Forward.treeLaw (x n) n).real
      {s | 1 - ε ≤ ((s.vertices.sup s.height : ℕ) : ℝ) / heightScale (x n) n ∧
        ((s.vertices.sup s.height : ℕ) : ℝ) / heightScale (x n) n ≤ Real.exp 1 + ε})
      atTop (𝓝 1) := maximum_height_window_tendsto_one x hs hε hε1

example (x : ℕ → SignSequence)
    (hs : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hl : Tendsto (fun n : ℕ => Real.log n / heightScale (x n) n) atTop (𝓝 0))
    (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm
      (fun s => (Forward.treeHeight s : ℝ) / heightScale (x n) n - 1)
      (ENNReal.ofReal p) (Forward.treeLaw (x n) n)) atTop (𝓝 0) :=
  maximum_height_tendsto_Lp x hs hl hp

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAi : Tendsto A atTop atTop)
    (hAl : Tendsto (fun n : ℕ => A n / Real.log n) atTop (𝓝 0))
    (hs : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hn : Tendsto (fun ε : ℝ => limsup (nearOriginMaximum x A c ε) atTop)
      (𝓝[>] 0) (𝓝 0))
    (hb : ∀ ε : ℝ, 0 < ε → ε < 1 → 0 < liminf (bulkMinimum x ε) atTop) :
    Tendsto (fun n : ℕ => heightScale (x n) n / Real.log n)
      atTop (𝓝 ((c + 1) / (2 * c))) :=
  linear_heightScale_tendsto x A hc hc1 hA hAi hAl hs hn hb

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAi : Tendsto A atTop atTop)
    (hAl : Tendsto (fun n : ℕ => A n / Real.log n) atTop (𝓝 0))
    (hs : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hn : NearOriginLimsup x A c) (hb : BulkLiminf x) (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun k : ℕ => (k : ℝ) / Real.log n - (c + 1) / (2 * c))
      (ENNReal.ofReal p) (Forward.uniformHeightLaw (x n) n)) atTop (𝓝 0) :=
  linear_uniform_height_tendsto_Lp x A hc hc1 hA hAi hAl hs hn hb hp

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAi : Tendsto A atTop atTop)
    (hAl : Tendsto (fun n : ℕ => A n / Real.log n) atTop (𝓝 0))
    (hs : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hn : NearOriginLimsup x A c) (hb : BulkLiminf x) (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun z : ℕ × ℕ × ℕ => (z.2.2 : ℝ) / Real.log n - (c + 1) / c)
      (ENNReal.ofReal p)
      ((Forward.treeLaw (x n) n).bind fun s =>
        (Measure.uniformOfFinset s.vertices).bind fun u =>
          (Measure.uniformOfFinset s.vertices).map fun v =>
            (s.height u, s.height v, s.graph.dist u v))) atTop (𝓝 0) :=
  linear_uniform_distance_tendsto_Lp x A hc hc1 hA hAi hAl hs hn hb hp

example (c : LinearRegimeParameter) (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (hA : ∀ n, 0 < A n) (hAi : Tendsto A atTop atTop)
    (hAl : Tendsto (fun n : ℕ => A n / Real.log n) atTop (𝓝 0))
    (hs : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hn : NearOriginLimsup x A (c : ℝ)) (hb : BulkLiminf x) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Forward.treeLaw (x n) n)
      {s | ε ≤ |(Forward.treeHeight s : ℝ) / Real.log n -
        (((c : ℝ) + 1) / (2 * (c : ℝ))) * linearHeightFactor c|}) atTop (𝓝 0) :=
  linear_maximum_deviation_tendsto_zero c x A hA hAi hAl hs hn hb hε

example (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i) (hs : extinctionTime y = ⊤) :
    ((∃ ν : ProbabilityMeasure LocalTree.Tree,
      Tendsto (fun n => ForwardInfiniteHistory.localProbabilityLaw (x n) n) atTop (𝓝 ν)) ↔
      (∀ᵐ H ∂ForwardInfiniteHistory.fullLaw y, ∃ t : LocalTree.Tree,
        Tendsto (fun n => Forward.localTreeOfState (H n)) atTop (𝓝 t))) ∧
      ((∀ᵐ H ∂ForwardInfiniteHistory.fullLaw y, ∃ t : LocalTree.Tree,
        Tendsto (fun n => Forward.localTreeOfState (H n)) atTop (𝓝 t)) ↔
        Tendsto (fun n => ∑ i ∈ Finset.Icc 1 n,
          if y i then (0 : ℝ) else 1 / (activeCount y i : ℝ)) atTop atTop) :=
  local_convergence_equivalences x y hxy hs

example (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i) (hs : extinctionTime y = ⊤) :
    (SourceDiagonalLocalConvergence x ↔ SourceAlmostSureLocalConvergence y) ∧
      (SourceAlmostSureLocalConvergence y ↔ Tendsto (freezingReciprocalSum y) atTop atTop) :=
  source_local_convergence_equivalences x y hxy hs

example (p : unitInterval) (hp : (p : ℝ) < 1) :
    (ForwardAnnealed.fullLaw p).map
      (fun H => LocalTree.toPlaneTree (ForwardInfiniteHistory.localLimit H)) =
        (PlaneTree.offspringFieldLaw (geometricMeasure (unitInterval.symm p))).map
          PlaneTree.prune :=
  (ForwardAnnealed.iid_signs_geometric_local_limit p hp).2

example : (ForwardAnnealed.planeLimitLaw 0 : Measure PlaneTree.Tree)
    {T | PlaneTree.degree T = 0} = 1 := by
  simpa using ForwardAnnealed.planeLimitLaw_offspring_mass 0 (by norm_num) 0

#print axioms Freezing1.uniform_active_height_tendsto_Lp
#print axioms Freezing1.maximum_height_window_tendsto_one
#print axioms Freezing1.maximum_height_tendsto_Lp
#print axioms Freezing1.linear_heightScale_tendsto
#print axioms Freezing1.linear_uniform_height_tendsto_Lp
#print axioms Freezing1.linear_uniform_distance_tendsto_Lp
#print axioms Freezing1.linear_maximum_deviation_tendsto_zero
#print axioms Freezing1.local_convergence_equivalences
#print axioms Freezing1.local_convergence_common_limit
#print axioms Freezing1.source_local_convergence_equivalences
#print axioms Freezing1.LocalTree.isClosedEmbedding_toUnordered
#print axioms Freezing1.ForwardAnnealed.iid_signs_geometric_local_limit
#print axioms Freezing1.ForwardAnnealed.planeLimitLaw_offspring_mass

end CandidateHeightsLocalReview
