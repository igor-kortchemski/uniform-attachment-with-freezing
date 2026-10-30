module

import Freezing1.MaximumTailMoments

/-! Author-created exact-source checks; the new proof-route review is
explicitly labelled as self-review. The earlier main T03 interface has
separate independent source review. -/

open Filter MeasureTheory
open scoped Topology ENNReal Classical
open Freezing1

set_option backward.isDefEq.respectTransparency false

example (rows : ℕ → SignSequence)
    (survival : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (log_negligible : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n)
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ C : ℝ, 2 ≤ C →
      (Forward.treeLaw (rows n) n).real
        {s | C < (Forward.treeHeight s : ℝ) / heightScale (rows n) n} ≤
        Real.exp (-heightScale (rows n) n * bennettRate (C - 1) / 2) := by
  filter_upwards [eventually_maximum_uniform_bennett_upper rows survival log_negligible]
    with n hn
  intro C hC
  apply (measureReal_mono (s₂ := {s : Forward.State |
    C ≤ (Forward.treeHeight s : ℝ) / heightScale (rows n) n}) ?_ (measure_ne_top _ _)).trans (hn C hC)
  intro s hs
  change C < (Forward.treeHeight s : ℝ) / heightScale (rows n) n at hs
  exact hs.le

example (rows : ℕ → SignSequence)
    (survival : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (log_negligible : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n)
      atTop (𝓝 0)) (p : ℝ) (hp : 1 ≤ p) :
    ∀ᶠ n in atTop,
      (∫ s, |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1| ^ p
        ∂Forward.treeLaw (rows n) n) ≤
        (7 : ℝ) ^ p + p * ∫ u in Set.Ioi (7 : ℝ),
          Real.exp (-(1 / 2) * bennettRate u) * u ^ (p - 1) :=
  eventually_maximum_error_moment_le_source_integral rows survival log_negligible hp

example (rows : ℕ → SignSequence)
    (survival : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (log_negligible : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n)
      atTop (𝓝 0)) (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm
      (fun s => (Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1)
      (ENNReal.ofReal p) (Forward.treeLaw (rows n) n)) atTop (𝓝 0) :=
  maximum_height_tendsto_Lp_via_tail_integral rows survival log_negligible hp

#print axioms Forward.treeHeight_unshifted_bennett_upper
#print axioms log_le_maximumRateSlack_mul_rate
#print axioms eventually_maximum_uniform_bennett_upper
#print axioms moment_le_seven_of_bennett_tail
#print axioms Forward.integrable_maximum_error_rpow
#print axioms eventually_maximum_error_moment_le_source_integral
#print axioms eventually_maximum_error_eLpNorm_le_source_integral
#print axioms maximum_height_tendsto_Lp_via_tail_integral
