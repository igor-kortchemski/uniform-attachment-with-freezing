module

import Freezing1.SourceUrnComponentMaximum

/-! Independently reconstructed finite exponent, actual component union
and full source-window conclusion. -/

open Filter MeasureTheory
open scoped Topology
open Freezing1

example {a s D E K k : ℝ} (ha : 1 ≤ a) (hs : 0 < s) (hsa : s ≤ a + 1)
    (hK : 0 < K) (hD : 0 < D) (hDK : D ≤ K / a) (hEK : E ≤ K / a) (hk : 1 ≤ k) :
    k ^ 2 / (16 * K) ≤ ((k ^ 4 / 4) * s⁻¹) / (D + k ^ 2 * max D E) :=
  source_urn_exponent_lower ha hs hsa hK hD hDK hEK hk

example (x : SignSequence) {a b k : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hb : PositiveThrough x b) {K : ℝ} (hK : 0 < K)
    (hSa : (activeCount x a : ℝ) ≤ (a : ℝ) + 1)
    (hD : SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b) ≤ K / a)
    (hE : SignedUrn.sourceEpsilon x a b hab ≤ K / a) (hk : 1 ≤ k)
    (hthreshold : 1 + (1 + (k : ℝ) ^ 2) * (activeCount x b : ℝ) / activeCount x a ≤ (k : ℝ) ^ 3) :
    (Forward.treeLaw x b).real {q | (k : ℝ) ^ 3 < (Forward.componentMaximum q a : ℝ)} ≤
      (activeCount x a : ℝ) * (2 * Real.exp (-((k : ℝ) ^ 2 / (16 * K)))) :=
  Forward.positiveExtension_treeLaw_maximum_tail_le x ha hab hb hK hSa hD hE hk hthreshold

example (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop) (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x) (C : ℕ) (hC : 2 ≤ C) :
    ∀ᶠ n in atTop, ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) →
      ((C ^ k : ℕ) : ℝ) ≤ (n : ℝ) / C →
      (Forward.treeLaw (x n) (C ^ (k + 1))).real
        {q | (k : ℝ) ^ 3 < (Forward.componentMaximum q (C ^ k) : ℝ)} ≤ 1 / (k : ℝ) ^ 2 :=
  linear_geometric_componentMaximum_tail_via_positiveExtension x A hc hc1 hA hAinf hτ hnear hbulk C hC

#print axioms source_urn_exponent_lower
#print axioms eventually_cubic_ge_marked_threshold
#print axioms eventually_geometric_exp_square_le_inv_sq
#print axioms positiveExtension_component_cubic_tail_le
#print axioms uniform_positiveExtension_component_parameters
#print axioms Forward.positiveExtension_continuation_maximum_tail_le
#print axioms Forward.positiveExtension_treeLaw_root_count
#print axioms linear_geometric_componentMaximum_tail_via_positiveExtension
