module

import Freezing1.LinearBushGHTree
import Freezing1.ForwardActiveHeightMgf

open Filter MeasureTheory ProbabilityTheory GromovHausdorff
open scoped Topology ENNReal Classical

namespace Freezing1

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAi : Tendsto A atTop atTop)
    (hAl : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hn : NearOriginLimsup x A c) (hb : BulkLiminf x) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ((Forward.treeLaw (x n) n).bind fun s =>
        (Measure.pi fun _ : Fin k => Measure.uniformOfFinset s.vertices).map
          (fun v i j => s.graph.dist (v i) (v j)))
        {D | ∃ i j, ε ≤ |(D i j : ℝ) / Real.log n -
          (if i = j then 0 else (c + 1) / c)|}) atTop (𝓝 0) := by
  have h := LinearBush.linear_sampled_distance_matrix_tendsto_zero
    x A hc hc1 hA hAi hAl hτ hn hb k hε
  change Tendsto (fun n : ℕ => LinearBush.sampleLaw (x n) n k
    {D | ∃ i j, ε ≤ |(D i j : ℝ) / Real.log n -
      (if i = j then 0 else (c + 1) / c)|}) atTop (𝓝 0)
  simpa only [LinearBush.starMatrix_linear hc.ne'] using h

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAi : Tendsto A atTop atTop)
    (hAl : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hn : NearOriginLimsup x A c) (hb : BulkLiminf x) :
    letI : MeasurableSpace GHSpace := borel GHSpace
    ¬ IsTightMeasureSet (Set.range fun n : ℕ =>
      (Forward.treeLaw (x n) n).map (LinearBush.scaledGH n)) :=
  LinearBush.linear_not_isTightMeasureSet x A hc hc1 hA hAi hAl hτ hn hb

example {x : SignSequence} {n k : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt n s) (hcount : (s.active.card : ℤ) = activeCount x n)
    (hpos : PositiveThrough x (n + (k + 1))) (hx : x (n + k + 1) = true)
    (c : ℝ≥0∞) (hc : 1 ≤ c) :
    ∫⁻ r, c ^ r.height (n + k + 1) ∂Forward.treeLawFrom x n s (k + 1) ≤
      c ^ (Forward.treeHeight s + 1) *
        (∏ i ∈ Finset.range k, (1 + (if x (n + i + 1) = true then
          (((activeCount x (n + i)).toNat : ℝ≥0∞) + 1)⁻¹ else 0) * (c - 1))) := by
  have h := Forward.newVertex_height_pow_le hs hcount (k + 1) hpos hc le_rfl hx
    (H := Forward.treeHeight s)
    (fun a ha => Forward.height_le_treeHeight (hs.active_subset ha))
  calc
    _ ≤ _ := h
    _ = _ := by rw [pow_succ]; ring

#print axioms LinearBush.sampleLaw_pair_apply
#print axioms LinearBush.linear_sampled_distance_matrix_tendsto_zero
#print axioms LinearBush.exists_packingNumberLE_of_isCompact
#print axioms LinearBush.instMetricSpaceScaledVertices
#print axioms LinearBush.linear_not_isTightMeasureSet
#print axioms Forward.lintegral_activeHMean_pow_treeLawFrom
#print axioms Forward.newVertex_height_pow_le

end Freezing1
