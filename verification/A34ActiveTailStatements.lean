module

import Freezing1.ActiveHeightTailIntegral

/-! Author-created expanded source statement and axiom probe for A34. -/

open Filter Set MeasureTheory ProbabilityTheory Asymptotics
open scoped Topology ENNReal Classical
open Freezing1

set_option backward.isDefEq.respectTransparency false

example (x : SignSequence) (n : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    (∫ k, |(k : ℝ) / heightScale x n - 1| ^ p ∂Forward.uniformActiveHeightLaw x n) =
      p * ∫ u in Ioi (0 : ℝ),
        (Forward.uniformActiveHeightLaw x n).real {k | u ≤ |(k : ℝ) / heightScale x n - 1|} *
          u ^ (p - 1) :=
  activeHeight_moment_layercake x n (by linarith)

example (x : SignSequence) (n : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    IntegrableOn (fun u : ℝ => (Forward.uniformActiveHeightLaw x n).real
      {k | u ≤ |(k : ℝ) / heightScale x n - 1|} * u ^ (p - 1)) (Ioi 0) :=
  integrable_activeHeightTailDensity x n (by linarith)

example (x : SignSequence) (n : ℕ) (hx : PositiveThrough x n) (hn : 1 ≤ n)
    (p : ℝ) (hp : 1 ≤ p) :
    (∫ k, |(k : ℝ) / heightScale x n - 1| ^ p ∂Forward.uniformActiveHeightLaw x n) ≤
      (7 : ℝ) ^ p + 2 * p * ∫ u in Ioi (7 : ℝ),
        Real.exp (-heightScale x n * ((1 + u) * Real.log (1 + u) - u)) * u ^ (p - 1) :=
  activeHeight_moment_le_split_seven x n hx hn hp

example : Real.exp 2 - 1 ≤ 7 := exp_two_sub_one_le_seven

example (u : ℝ) (hu : 7 ≤ u) : u ≤ (1 + u) * Real.log (1 + u) - u :=
  self_le_bennettRate_of_seven hu

example (p m : ℝ) (hm : 0 < m) :
    (∫ u in Ioi (7 : ℝ), Real.exp (-m * u) * u ^ (p - 1)) =
      (1 / m ^ p) * ∫ u in Ioi (7 * m), Real.exp (-u) * u ^ (p - 1) := by
  simpa only [exponentialMomentTail, Real.rpow_neg hm.le, one_div] using
    exponentialMomentTail_dilation p hm

example (p m : ℝ) (hp : 1 ≤ p) (hm : 0 < m) (hlarge : 2 * (p - 1) / 7 ≤ m) :
    (∫ u in Ioi (7 : ℝ), Real.exp (-m * u) * u ^ (p - 1)) ≤
      2 * (7 : ℝ) ^ (p - 1) * Real.exp (-7 * m) / m :=
  exponentialMomentTail_le hp hm hlarge

example (p : ℝ) (hp : 1 ≤ p) :
    (fun m : ℝ => ∫ u in Ioi (7 : ℝ), Real.exp (-m * u) * u ^ (p - 1)) =O[atTop]
      (fun m => Real.exp (-7 * m) / m) :=
  exponentialMomentTail_isBigO p hp

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (p : ℝ) (hp : 1 ≤ p) :
    (fun n => ∫ u in Ioi (7 : ℝ),
      Real.exp (-heightScale (rows n) n * u) * u ^ (p - 1)) =O[atTop]
      (fun n => Real.exp (-7 * heightScale (rows n) n) / heightScale (rows n) n) :=
  activeHeight_exponentialTail_isBigO rows hrows p hp

example (x : SignSequence) (n : ℕ) (hx : PositiveThrough x n) (hn : 1 ≤ n)
    (p : ℝ) (hp : 1 ≤ p) (hlarge : 2 * (p - 1) / 7 ≤ heightScale x n) :
    (∫ k, |(k : ℝ) / heightScale x n - 1| ^ p ∂Forward.uniformActiveHeightLaw x n) ≤
      (7 : ℝ) ^ p + 4 * p * (7 : ℝ) ^ (p - 1) *
        Real.exp (-7 * heightScale x n) / heightScale x n :=
  activeHeight_moment_le_source_tail_asymptotic x n hx hn hp hlarge

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, ∀ n ≥ 1,
      (∫ k, |(k : ℝ) / heightScale (rows n) n - 1| ^ p
        ∂Forward.uniformActiveHeightLaw (rows n) n) ≤ C := by
  exact ⟨(7 : ℝ) ^ p + 2 * p * ∫ u in Ioi (7 : ℝ), bennettMomentDensity p (1 / 2) u,
    fun n hn => activeHeight_moment_le_split_seven_uniform (rows n) n (hrows n) hn hp⟩

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm (fun k : ℕ => (k : ℝ) / heightScale (rows n) n - 1)
      (ENNReal.ofReal p) (Forward.uniformActiveHeightLaw (rows n) n)) atTop (𝓝 0) :=
  uniformActiveHeight_tendsto_Lp_via_tail_integral rows hrows hp

#print axioms rpow_layercake_real
#print axioms rpow_layercake_real_integrable
#print axioms activeHeight_moment_layercake
#print axioms activeHeight_moment_le_split_seven
#print axioms exp_two_sub_one_le_seven
#print axioms self_le_bennettRate_of_seven
#print axioms exponentialMomentTail_dilation
#print axioms exponentialMomentTail_le
#print axioms exponentialMomentTail_isBigO
#print axioms activeHeight_moment_le_source_tail_asymptotic
#print axioms activeHeight_moment_le_split_seven_uniform
#print axioms activeHeight_exponentialTail_isBigO
#print axioms activeHeightError_eLpNorm_le_source_integral
#print axioms uniformActiveHeight_tendsto_Lp_via_tail_integral
