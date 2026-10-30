module

public import Freezing1.MainForwardBlockConcentration

/-!
Independent reconstruction of the source forward counts in Lemma 12 and
Lemma Forestier. The count is expanded into actual active vertices at the
later cut and the difference of the two certified cut-graph heights.
-/

open MeasureTheory Filter
open scoped Topology Classical

namespace Freezing1.StatementAudit

set_option backward.isDefEq.respectTransparency false in
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
          ∫ s, ((((Forward.truncateAt s (C ^ (k + 1))).active).filter fun v =>
            (((c : ℝ) + 1) / (2 * (c : ℝ))) * Real.log (C : ℝ) *
                (linearHeightFactor c - η) <
              ((Forward.cutHeight s (C ^ k) v -
                Forward.cutHeight s (C ^ (k + 1)) v : ℕ) : ℝ)).card : ℝ)
            ∂Forward.treeLaw (x n) n := by
  simpa only [Forward.blockTallCount, Forward.cutRoots, Forward.blockHeight] using
    linear_forward_geometricBlock_expectation_lower x A c hApos hAinf hsurvive hnear hηpos hηlt

set_option backward.isDefEq.respectTransparency false in
example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : LinearRegimeParameter)
    (hApos : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hsurvive : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : Tendsto
      (fun ε : ℝ => limsup (fun n => nearOriginMaximum x A (c : ℝ) ε n) atTop)
      (𝓝[>] 0) (𝓝 0))
    (η : ℝ) (hηpos : 0 < η) (hηlt : η < 1) :
    ∃ C : ℕ, 1 < C ∧ ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ᶠ n in atTop, ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) →
        ((C ^ k : ℕ) : ℝ) ≤ ε * (n : ℝ) / (C : ℝ) →
        (Forward.treeLaw (x n) n).real {s |
          (((((Forward.truncateAt s (C ^ (k + 1))).active).filter fun v =>
            (((c : ℝ) + 1) / (2 * (c : ℝ))) * Real.log (C : ℝ) *
                (linearHeightFactor c - η) <
              ((Forward.cutHeight s (C ^ k) v -
                Forward.cutHeight s (C ^ (k + 1)) v : ℕ) : ℝ)).card : ℝ)) ≤
              4 * ((C ^ k : ℕ) : ℝ)} ≤ L / ((C ^ k : ℕ) : ℝ) := by
  simpa only [Forward.blockTallCount, Forward.cutRoots, Forward.blockHeight] using
    linear_forward_geometricBlock_fewTallRoots_probability x A c
      hApos hAinf hsurvive hnear hηpos hηlt

end Freezing1.StatementAudit

#print axioms Freezing1.linear_forward_geometricBlock_expectation_lower
#print axioms Freezing1.linear_forward_geometricBlock_fewTallRoots_probability
#print axioms Freezing1.ReverseStampedHistory.forward_blockTallCount_law
#print axioms Freezing1.ReverseStampedHistory.cutHeight_eq_cutGraph_dist
