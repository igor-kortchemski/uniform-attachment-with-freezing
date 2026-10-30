module

import Freezing1.SourceUrnComponentMaximum

/-! Author-created expanded checks of the A64 infinite-urn route. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Classical
open Freezing1 Freezing1.Forward

set_option backward.isDefEq.respectTransparency false

example (a s D E K k : ℝ) (ha : 1 ≤ a) (hs : 0 < s) (hsa : s ≤ a + 1)
    (hK : 0 < K) (hD : 0 < D) (hDK : D ≤ K / a) (hEK : E ≤ K / a) (hk : 1 ≤ k) :
    k ^ 2 / (16 * K) ≤ ((k ^ 4 / 4) * s⁻¹) / (D + k ^ 2 * max D E) :=
  source_urn_exponent_lower ha hs hsa hK hD hDK hEK hk

example (R : ℝ) :
    ∀ᶠ k : ℕ in atTop, 1 ≤ k ∧ 1 + (1 + (k : ℝ) ^ 2) * R ≤ (k : ℝ) ^ 3 :=
  eventually_cubic_ge_marked_threshold R

example (C : ℕ) (hC : 1 ≤ C) (β : ℝ) (hβ : 0 < β) :
    ∀ᶠ k : ℕ in atTop,
      (((C ^ k : ℕ) : ℝ) + 1) * (2 * Real.exp (-β * (k : ℝ) ^ 2)) ≤ 1 / (k : ℝ) ^ 2 :=
  eventually_geometric_exp_square_le_inv_sq C hC hβ

example {x : SignSequence} {a b k : ℕ} {s : State} (hs : PhaseData x a s)
    {r : ℕ} (hr : r ∈ s.active) (ha : 1 ≤ a) (hab : a < b) (hb : PositiveThrough x b)
    (K : ℝ) (hK : 0 < K) (hSa : (activeCount x a : ℝ) ≤ (a : ℝ) + 1)
    (hD : SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b) ≤ K / a)
    (hE : SignedUrn.sourceEpsilon x a b hab ≤ K / a) (hk : 1 ≤ k)
    (hthreshold : 1 + (1 + (k : ℝ) ^ 2) * (activeCount x b : ℝ) / activeCount x a ≤
      (k : ℝ) ^ 3) :
    (Forward.continuationLaw x a (b - a) s).real {q |
      (k : ℝ) ^ 3 < ((insert r (q.active.filter fun v => cutAncestor q a v = r)).card : ℝ)} ≤
      2 * Real.exp (-((k : ℝ) ^ 2 / (16 * K))) := by
  simpa only [componentPopulationWithRoot, componentActive] using
    positiveExtension_component_cubic_tail_le hs hr ha hab hb hK hSa hD hE hk hthreshold

example (x : SignSequence) {a b k : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : PositiveThrough x b)
    (K : ℝ) (hK : 0 < K) (hSa : (activeCount x a : ℝ) ≤ (a : ℝ) + 1)
    (hD : SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b) ≤ K / a)
    (hE : SignedUrn.sourceEpsilon x a b hab ≤ K / a) (hk : 1 ≤ k)
    (hthreshold : 1 + (1 + (k : ℝ) ^ 2) * (activeCount x b : ℝ) / activeCount x a ≤
      (k : ℝ) ^ 3) :
    (treeLaw x b).real {q | (k : ℝ) ^ 3 < (componentMaximum q a : ℝ)} ≤
      (activeCount x a : ℝ) * (2 * Real.exp (-((k : ℝ) ^ 2 / (16 * K)))) :=
  positiveExtension_treeLaw_maximum_tail_le x ha hab hb hK hSa hD hE hk hthreshold

example (x : SignSequence) (a b : ℕ) (hab : a ≤ b) (hb : PositiveThrough x b) :
    ∀ᵐ q ∂treeLaw x b, (cutRoots q a).card = (activeCount x a).toNat :=
  positiveExtension_treeLaw_root_count x hab hb

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x) (C : ℕ) (hC : 2 ≤ C) :
    ∃ β : ℝ, 0 < β ∧ ∀ᶠ n in atTop, ∀ k : ℕ,
      A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ (n : ℝ) / C →
      (SignedUrn.continuationLaw (activeCount (x n)) (C ^ k) (C ^ (k + 1) - C ^ k) 1).real
        {u : ℤ | (k : ℝ) ^ 3 < (u : ℝ) + 1} ≤ 2 * Real.exp (-β * (k : ℝ) ^ 2) :=
  uniform_positiveExtension_urn_cubic_tail x A hc hc1 hA hAinf hτ hnear hbulk C hC

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x) (C : ℕ) (hC : 2 ≤ C) :
    ∀ᶠ n in atTop, ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) →
      ((C ^ k : ℕ) : ℝ) ≤ (n : ℝ) / C →
      (treeLaw (x n) (C ^ (k + 1))).real {q |
        (k : ℝ) ^ 3 < ((((cutRoots q (C ^ k)).sup fun r =>
          (insert r (q.active.filter fun v => cutAncestor q (C ^ k) v = r)).card) : ℕ) : ℝ)} ≤
          1 / (k : ℝ) ^ 2 := by
  have hf (q : State) (a : ℕ) : componentPopulationWithRoot q a =
      (fun r => (insert r (q.active.filter fun v => cutAncestor q a v = r)).card) := rfl
  simpa only [componentMaximum, hf] using
    linear_geometric_componentMaximum_tail_via_positiveExtension
      x A hc hc1 hA hAinf hτ hnear hbulk C hC

#print axioms source_urn_exponent_lower
#print axioms eventually_cubic_ge_marked_threshold
#print axioms eventually_geometric_exp_square_le_inv_sq
#print axioms SignedUrn.positiveExtension_square_budget_pos
#print axioms positiveExtension_urn_cubic_tail_le
#print axioms positiveExtension_component_cubic_tail_le
#print axioms uniform_positiveExtension_component_parameters
#print axioms uniform_positiveExtension_urn_cubic_tail
#print axioms positiveExtension_continuation_maximum_tail_le
#print axioms positiveExtension_treeLaw_maximum_tail_le
#print axioms positiveExtension_treeLaw_root_count
#print axioms linear_geometric_componentMaximum_tail_via_positiveExtension
