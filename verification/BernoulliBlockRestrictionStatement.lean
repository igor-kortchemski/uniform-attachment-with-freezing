module

import Freezing1.BernoulliBlockRestriction

open Freezing1
open scoped Classical

example {n b : ℕ} (hb : b ≤ n) (a : ℕ) (p : Fin n → unitInterval) :
    bernoulliPartialSumLaw p
      (Finset.univ.filter fun i : Fin n => a ≤ i.val ∧ i.val < b) =
      bernoulliPartialSumLaw
        (fun i : Fin b => p ⟨i.val, i.isLt.trans_le hb⟩)
        (Finset.univ.filter fun i : Fin b => a ≤ i.val) :=
  bernoulliPartialSumLaw_fin_restrict p a b hb

#print axioms Freezing1.bernoulliPartialSumLaw_map
#print axioms Freezing1.bernoulliPartialSumLaw_fin_restrict
