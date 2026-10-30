module

public import Freezing1.MainLinearMaximumLower

/-!
Independent reconstruction of Introduction Theorem 4 (III), source lines
316–339. The two nested hypotheses are expanded; the height is the actual
maximum over the terminal forward tree. The constant is any real solution
greater than one of the paper's defining equation, using proved uniqueness.
-/

open MeasureTheory Filter
open scoped Topology Classical

namespace Freezing1.StatementAudit

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c f : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hf : 1 < f)
    (hfeq : f * (Real.log f - 1) = (c - 1) / (c + 1))
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : Tendsto
      (fun ε : ℝ => limsup (fun n => nearOriginMaximum x A c ε n) atTop)
      (𝓝[>] 0) (𝓝 0))
    (hbulk : ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 < liminf (fun n => bulkMinimum x ε n) atTop)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (Forward.treeLaw (x n) n)
      {s | δ ≤ |((s.vertices.sup s.height : ℕ) : ℝ) / Real.log (n : ℝ) -
        (c + 1) / (2 * c) * f|}) atTop (𝓝 0) := by
  let p : LinearRegimeParameter := ⟨c, hc, hc1⟩
  have he : f = linearHeightFactor p := linearHeightFactor_unique p hf hfeq
  rw [he]
  exact linear_maximum_deviation_tendsto_zero p x A hA hAinf hsmall hτ hnear hbulk hδ

end Freezing1.StatementAudit

#print axioms Freezing1.linear_maximum_deviation_tendsto_zero
#print axioms Freezing1.linear_maximum_lower_tendsto_zero
#print axioms Freezing1.linear_maximum_lower_tendsto_zero_of_bounds
#print axioms Freezing1.Forward.goodChain_survival
#print axioms Freezing1.Forward.treeLaw_goodChain_step_le
#print axioms Freezing1.Forward.continuationLaw_goodSet_growth_failure_le
#print axioms Freezing1.linearHeightFactor_unique
