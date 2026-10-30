module

import Freezing1.MaximumTailBoundedness

/-! Author-created probe for the separately authored all-row corollary. -/

open Filter MeasureTheory
open scoped Topology ENNReal
open Freezing1

example (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n) atTop (𝓝 0))
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫ s, |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1| ^ p
        ∂Forward.treeLaw (rows n) n) ≤ C :=
  maximum_error_moments_bounded_all_rows rows hτ hlog hp

example (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n) atTop (𝓝 0))
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n : ℕ,
      eLpNorm (fun s => (Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1)
        (ENNReal.ofReal p) (Forward.treeLaw (rows n) n) ≤ C :=
  maximum_error_eLpNorm_bounded_all_rows rows hτ hlog hp

#print axioms maximum_error_moments_bounded_all_rows
#print axioms maximum_error_eLpNorm_bounded_all_rows
