module

import Freezing1.LinearGoodChainBase

open Freezing1 Filter MeasureTheory
open scoped Topology

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hnear : NearOriginLinear x A c) (C : ℕ) (hC : 2 ≤ C)
    (hτ : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n)) :
    ∀ᶠ n in atTop, ∀ᵐ s ∂Forward.treeLaw (x n) n,
      c / 4 * (2 : ℝ) ^ Nat.ceil (Real.log (A n) / Real.log (C : ℝ)) ≤
        ((Forward.truncateAt s (C ^ Nat.ceil (Real.log (A n) / Real.log (C : ℝ)))).active.card : ℝ) := by
  simpa only [Forward.goodSet_base, chainLowerIndex] using
    Forward.eventually_treeLaw_goodSet_base x A hc hA hAinf hsmall hnear C hC 0 hτ

#print axioms Freezing1.eventually_chain_base_population
#print axioms Freezing1.Forward.PhaseData.goodSet_base_card
#print axioms Freezing1.Forward.eventually_treeLaw_goodSet_base
