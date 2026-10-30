module

public import Freezing1.MainLinearBlockCount

/-!
Independent statement reconstruction for the reverse-history counterpart of
source Lemma 12. The source's forward cut-forest observable still requires the
separate timestamped T05 and phase-reconstruction bridge. This probe deliberately
expands the actual reverse count and the nested-limit hypothesis.
-/

open MeasureTheory Filter
open scoped Topology Classical

namespace Freezing1.StatementAudit

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hApos : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hsurvive : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : Tendsto
      (fun ε : ℝ => limsup (fun n => nearOriginMaximum x A (c : ℝ) ε n) atTop)
      (𝓝[>] 0) (𝓝 0))
    (η : ℝ) (hηpos : 0 < η) (hηlt : η < 1) :
    ∃ C : ℕ, 1 < C ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) →
        ((C ^ k : ℕ) : ℝ) ≤ ε * (n : ℝ) / (C : ℝ) →
        5 * ((C ^ k : ℕ) : ℝ) ≤
          ∫ H, (((ReverseHistory.stage H (C ^ (k + 1))).roots.filter fun v =>
            (((c : ℝ) + 1) / (2 * (c : ℝ))) * Real.log (C : ℝ) *
                (linearHeightFactor c - η) <
              ((ReverseHistory.stage H (C ^ k)).depth v : ℝ)).card : ℝ)
            ∂ReverseHistory.fullLaw (x n) n := by
  simpa only [ReverseHistory.blockTallRootCount] using
    linear_geometricBlock_tallRoot_expectation_lower x A c hApos hAinf hsurvive hnear hηpos hηlt

end Freezing1.StatementAudit

#print axioms Freezing1.linear_geometricBlock_tallRoot_expectation_lower
#print axioms Freezing1.exists_geometricBlock_tallRoot_expectation_lower
#print axioms Freezing1.exists_uniform_geometricBlock_weighted_tail_lower
#print axioms Freezing1.ReverseHistory.integral_blockTallRootCount
