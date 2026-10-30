module

import Freezing1.MainLinearUniformHeight

open MeasureTheory Filter
open scoped Topology ENNReal

example (schedule : ℕ → Freezing1.SignSequence) (cutoff : ℕ → ℝ)
    (growth : ℝ) (growth_pos : 0 < growth) (growth_le_one : growth ≤ 1)
    (cutoff_pos : ∀ n, 0 < cutoff n)
    (cutoff_diverges : Tendsto cutoff atTop atTop)
    (cutoff_small : Tendsto (fun n : ℕ => cutoff n / Real.log (n : ℝ)) atTop (𝓝 0))
    (survives : ∀ n : ℕ, (n : ℕ∞) < Freezing1.extinctionTime (schedule n))
    (near_origin : Tendsto
      (fun epsilon : ℝ => limsup (Freezing1.nearOriginMaximum schedule cutoff growth epsilon) atTop)
      (𝓝[>] 0) (𝓝 0))
    (bulk : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      0 < liminf (Freezing1.bulkMinimum schedule epsilon) atTop)
    (exponent : ℝ) (hexponent : 1 ≤ exponent) :
    Tendsto
      (fun n : ℕ => eLpNorm
        (fun height : ℕ => (height : ℝ) / Real.log (n : ℝ) - (growth + 1) / (2 * growth))
        (ENNReal.ofReal exponent) (Freezing1.Forward.uniformHeightLaw (schedule n) n))
      atTop (𝓝 0) :=
  Freezing1.linear_uniform_height_tendsto_Lp schedule cutoff growth_pos growth_le_one
    cutoff_pos cutoff_diverges cutoff_small survives near_origin bulk hexponent

#print axioms Freezing1.linear_uniform_height_tendsto_Lp
#print axioms Freezing1.centered_tendsto_Lp_of_eventual_exp_bound
#print axioms Freezing1.Forward.uniformHeightLaw_integral_mixture
#print axioms Freezing1.Forward.uniformHeightLaw_lower_tail_le
