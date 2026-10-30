module

import Freezing1.MainLinearHeightScale

open Filter
open scoped Topology

-- Independently reconstructed from the Introduction's Theorem thm:lineaire (I).
-- Keep the nested limit and bulk liminf visible instead of using hypothesis aliases.
example (schedule : ℕ → Freezing1.SignSequence) (cutoff : ℕ → ℝ)
    (slope : ℝ) (hslope : 0 < slope) (hslope_one : slope ≤ 1)
    (hcutoff_positive : ∀ n, 0 < cutoff n)
    (hcutoff_diverges : Tendsto cutoff atTop atTop)
    (hcutoff_small : Tendsto
      (fun n : ℕ => cutoff n / Real.log (n : ℝ)) atTop (𝓝 0))
    (survives : ∀ n : ℕ, (n : ℕ∞) < Freezing1.extinctionTime (schedule n))
    (near_origin : Tendsto
      (fun epsilon : ℝ => limsup
        (Freezing1.nearOriginMaximum schedule cutoff slope epsilon) atTop)
      (𝓝[>] 0) (𝓝 0))
    (bulk : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      0 < liminf (Freezing1.bulkMinimum schedule epsilon) atTop) :
    Tendsto
      (fun n : ℕ => Freezing1.heightScale (schedule n) n / Real.log (n : ℝ))
      atTop (𝓝 ((slope + 1) / (2 * slope))) :=
  Freezing1.linear_heightScale_tendsto schedule cutoff hslope hslope_one
    hcutoff_positive hcutoff_diverges hcutoff_small survives near_origin bulk

#print axioms Freezing1.linear_heightScale_tendsto
#print axioms Freezing1.tendsto_heightScale_div_log_of_uniformIntervals
#print axioms Freezing1.uniformLogIntervals_of_nearOriginLinear
#print axioms Freezing1.heightInterval_log_error_le
#print axioms Freezing1.nearOriginLimsup_iff
#print axioms Freezing1.bulkLiminf_iff
#print axioms Freezing1.tendsto_log_floor_div_ceil_div_log
#print axioms Freezing1.eventually_ceil_floor_cutoff_bounds
