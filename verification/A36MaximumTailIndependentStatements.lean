module

import Freezing1.MaximumTailMoments

/-! Independent expanded review of the root-authored A36 route. The A34
analytic dependency has its own separately attributed proof evidence. -/

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal BigOperators Classical
open Freezing1

set_option backward.isDefEq.respectTransparency false

example : ∀ C : ℝ, 2 ≤ C →
    Real.log C ≤ (1 + 7 / bennettRate 1) * bennettRate (C - 1) := by
  intro C hC
  exact log_le_maximumRateSlack_mul_rate hC

example (x : SignSequence) (n : ℕ) (hn : 1 ≤ n) (hτ : (n : ℕ∞) < extinctionTime x)
    (C : ℝ) (hC : 1 ≤ C) :
    (Forward.treeLaw x n).real {s | C ≤ (Forward.treeHeight s : ℝ) / heightScale x n} ≤
      Real.exp (Real.log ((n : ℝ) + 1) + Real.log C - heightScale x n * bennettRate (C - 1)) :=
  Forward.treeHeight_unshifted_bennett_upper x n hn hτ hC

example (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n) atTop (𝓝 0)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ C : ℝ, 2 ≤ C →
      (Forward.treeLaw (rows n) n).real
        {s | C < (Forward.treeHeight s : ℝ) / heightScale (rows n) n} ≤
        Real.exp (-heightScale (rows n) n * bennettRate (C - 1) / 2) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_maximum_uniform_bennett_upper rows hτ hlog)
  refine ⟨N, fun n hn C hC => ?_⟩
  apply (measureReal_mono (s₂ := {s : Forward.State |
    C ≤ (Forward.treeHeight s : ℝ) / heightScale (rows n) n}) ?_ (measure_ne_top _ _)).trans
    (hN n hn C hC)
  intro s hs
  change C < (Forward.treeHeight s : ℝ) / heightScale (rows n) n at hs
  exact hs.le

example (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n) atTop (𝓝 0)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ u : ℝ, 7 < u →
      (Forward.treeLaw (rows n) n).real
        {s | u ≤ |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1|} ≤
        Real.exp (-bennettRate u / 2) :=
  eventually_atTop.mp (eventually_maximum_error_tail_seven rows hτ hlog)

example (x : SignSequence) (n : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    Integrable (fun s => |(Forward.treeHeight s : ℝ) / heightScale x n - 1| ^ p)
      (Forward.treeLaw x n) :=
  Forward.integrable_maximum_error_rpow x n (by linarith)

example (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n) atTop (𝓝 0))
    (p : ℝ) (hp : 1 ≤ p) :
    ∀ᶠ n in atTop,
      (∫ s, |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1| ^ p
        ∂Forward.treeLaw (rows n) n) ≤
        (7 : ℝ) ^ p + p * ∫ u in Ioi (7 : ℝ),
          Real.exp (-(1 / 2) * bennettRate u) * u ^ (p - 1) :=
  eventually_maximum_error_moment_le_source_integral rows hτ hlog hp

/-- The literal whole sequence is bounded: finitely many initial rows are
absorbed explicitly rather than only asserting an eventual bound. -/
example (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n) atTop (𝓝 0))
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, ∀ n : ℕ,
      (∫ s, |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1| ^ p
        ∂Forward.treeLaw (rows n) n) ≤ C := by
  let f : ℕ → ℝ := fun n => ∫ s, |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1| ^ p
    ∂Forward.treeLaw (rows n) n
  let K : ℝ := (7 : ℝ) ^ p + p * ∫ u in Ioi (7 : ℝ), bennettMomentDensity p (1 / 2) u
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_maximum_error_moment_le_source_integral rows hτ hlog hp)
  have hN' : ∀ n ≥ N, f n ≤ K := hN
  refine ⟨|K| + ∑ i ∈ Finset.range N, |f i|, fun n => ?_⟩
  change f n ≤ _
  by_cases hn : n < N
  · exact (le_abs_self (f n)).trans
      ((Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_range.mpr hn)).trans
        (le_add_of_nonneg_left (abs_nonneg K)))
  · exact (hN' n (Nat.le_of_not_gt hn)).trans
      ((le_abs_self K).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => abs_nonneg (f i)))))

example (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n) atTop (𝓝 0))
    (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm
      (fun s => (Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1)
      (ENNReal.ofReal p) (Forward.treeLaw (rows n) n)) atTop (𝓝 0) :=
  maximum_height_tendsto_Lp_via_tail_integral rows hτ hlog hp

#print axioms log_le_maximumRateSlack_mul_rate
#print axioms Forward.treeHeight_unshifted_bennett_upper
#print axioms Forward.treeHeight_uniform_bennett_upper_of_slack
#print axioms eventually_maximum_uniform_bennett_upper
#print axioms eventually_maximum_error_tail_seven
#print axioms moment_le_seven_of_bennett_tail
#print axioms Forward.integrable_maximum_error_rpow
#print axioms eventually_maximum_error_moment_le_source_integral
#print axioms eventually_maximum_error_eLpNorm_le_source_integral
#print axioms maximum_height_tendsto_Lp_via_tail_integral
