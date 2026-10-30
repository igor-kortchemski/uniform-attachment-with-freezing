module

import Freezing1.ActiveHeightTailIntegral

/-! Source-reconstructed checks by the integrating reviewer, who did not
author either of the two A34 implementation modules. -/

open Filter Set MeasureTheory Asymptotics
open scoped Topology ENNReal Classical
open Freezing1

example (x : SignSequence) (n : ℕ) (p : ℝ) (hp : 0 < p) :
    (∫ k, |(k : ℝ) / heightScale x n - 1| ^ p ∂Forward.uniformActiveHeightLaw x n) =
      p * ∫ u in Ioi (0 : ℝ),
        (Forward.uniformActiveHeightLaw x n).real
          {k | u ≤ |(k : ℝ) / heightScale x n - 1|} * u ^ (p - 1) :=
  activeHeight_moment_layercake x n hp

example (x : SignSequence) (n : ℕ) (hx : PositiveThrough x n) (hn : 1 ≤ n)
    (p : ℝ) (hp : 1 ≤ p) :
    (∫ k, |(k : ℝ) / heightScale x n - 1| ^ p ∂Forward.uniformActiveHeightLaw x n) ≤
      (7 : ℝ) ^ p + 2 * p * ∫ u in Ioi (7 : ℝ),
        Real.exp (-heightScale x n * bennettRate u) * u ^ (p - 1) :=
  activeHeight_moment_le_split_seven x n hx hn hp

example (p m : ℝ) (hm : 0 < m) :
    (∫ u in Ioi (7 : ℝ), Real.exp (-m * u) * u ^ (p - 1)) =
      (1 / m ^ p) * ∫ u in Ioi (7 * m), Real.exp (-u) * u ^ (p - 1) := by
  simpa only [exponentialMomentTail, Real.rpow_neg hm.le, one_div] using
    exponentialMomentTail_dilation p hm

example (rows : ℕ → SignSequence) (hx : ∀ n, PositiveThrough (rows n) n)
    (p : ℝ) (hp : 1 ≤ p) :
    (fun n => ∫ u in Ioi (7 : ℝ),
      Real.exp (-heightScale (rows n) n * u) * u ^ (p - 1)) =O[atTop]
      (fun n => Real.exp (-7 * heightScale (rows n) n) / heightScale (rows n) n) :=
  activeHeight_exponentialTail_isBigO rows hx p hp

example (rows : ℕ → SignSequence) (hx : ∀ n, PositiveThrough (rows n) n)
    (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm (fun k : ℕ => (k : ℝ) / heightScale (rows n) n - 1)
      (ENNReal.ofReal p) (Forward.uniformActiveHeightLaw (rows n) n)) atTop (𝓝 0) :=
  uniformActiveHeight_tendsto_Lp_via_tail_integral rows hx hp

#print axioms exp_two_sub_one_le_seven
#print axioms exponentialMomentTail_dilation
#print axioms exponentialMomentTail_le
#print axioms activeHeight_moment_layercake
#print axioms integrable_activeHeightTailDensity
#print axioms activeHeight_moment_le_split_seven
#print axioms activeHeight_moment_le_split_seven_uniform
#print axioms uniformActiveHeight_tendsto_Lp_via_tail_integral
