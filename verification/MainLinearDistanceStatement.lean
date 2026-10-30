module

public import Freezing1.MainLinearDistance

/-!
Independent reconstruction of Theorem 4 (II), distance assertion. The measure
is expanded into the actual forward tree law and two uniform draws conditional
on that same tree. The diagonal is retained, and the exponent is any real ≥1.
-/

open MeasureTheory Filter
open scoped Topology Classical

namespace Freezing1.StatementAudit

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hcpos : 0 < c) (hcle : c ≤ 1) (hApos : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hAsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hsurvive : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : Tendsto
      (fun ε : ℝ => limsup (fun n => nearOriginMaximum x A c ε n) atTop)
      (𝓝[>] 0) (𝓝 0))
    (hbulk : ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 < liminf (fun n => bulkMinimum x ε n) atTop)
    (r : ℝ) (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun z : ℕ × ℕ × ℕ => (z.2.2 : ℝ) / Real.log (n : ℝ) - (c + 1) / c)
      (ENNReal.ofReal r)
      ((Forward.treeLaw (x n) n).bind fun s =>
        (Measure.uniformOfFinset s.vertices).bind fun u =>
          (Measure.uniformOfFinset s.vertices).map fun v =>
            (s.height u, s.height v, s.graph.dist u v))) atTop (𝓝 0) := by
  exact linear_uniform_distance_tendsto_Lp x A hcpos hcle hApos hAinf hAsmall
    hsurvive hnear hbulk hr

end Freezing1.StatementAudit

#print axioms Freezing1.linear_uniform_distance_tendsto_Lp
#print axioms Freezing1.linear_uniform_distance_deviation_tendsto_zero
#print axioms Freezing1.CanonicalTree.forwardPairDataLaw_eq_history
#print axioms Freezing1.CanonicalTree.pairCoalescenceLaw_geometry
#print axioms Freezing1.CanonicalTree.pairCoalescenceLaw_distance_mgf_le
