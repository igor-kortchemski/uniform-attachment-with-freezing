module

public import Freezing1.MainLinearComponentMaximum
public import Freezing1.CanonicalComponentGeometry

/-!
Independent reconstruction of Lemma Forestjump. The source maximum is expanded
into the roots of the actual time-cut graph and their active component fibers,
with every star root explicitly inserted even when it later froze.
-/

open MeasureTheory Filter
open scoped Topology Classical

namespace Freezing1.StatementAudit

set_option backward.isDefEq.respectTransparency false in
example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hcpos : 0 < c) (hcle : c ≤ 1) (hApos : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsurvive : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : Tendsto
      (fun ε : ℝ => limsup (fun n => nearOriginMaximum x A c ε n) atTop)
      (𝓝[>] 0) (𝓝 0))
    (hbulk : ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 < liminf (fun n => bulkMinimum x ε n) atTop)
    (C : ℕ) (hC : 2 ≤ C) :
    ∀ᶠ n in atTop, ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) →
      ((C ^ k : ℕ) : ℝ) ≤ (n : ℝ) / C →
      (Forward.treeLaw (x n) (C ^ (k + 1))).real {s |
        (k : ℝ) ^ 3 < (((Forward.cutRoots s (C ^ k)).sup fun r =>
          (insert r (s.active.filter fun v => Forward.cutAncestor s (C ^ k) v = r)).card : ℕ) : ℝ)} ≤
            1 / (k : ℝ) ^ 2 := by
  have hf (s : Forward.State) (a : ℕ) : Forward.componentPopulationWithRoot s a =
      fun r => (insert r (s.active.filter fun v => Forward.cutAncestor s a v = r)).card := by
    funext r
    rfl
  simpa only [Forward.componentMaximum, hf] using linear_geometric_componentMaximum_tail x A
      hcpos hcle hApos hAinf hsurvive hnear hbulk C hC

end Freezing1.StatementAudit

#print axioms Freezing1.linear_geometric_componentMaximum_tail
#print axioms Freezing1.Forward.treeLaw_componentMaximum_tail_le
#print axioms Freezing1.Forward.continuationLaw_componentPopulation_of_root
#print axioms Freezing1.Forward.treeLaw_cutAncestor_eq_root_iff_reachable
