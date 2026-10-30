module

import Freezing1.ReverseSeparationLaw

open Freezing1 Freezing1.Reverse
open scoped BigOperators ENNReal

-- Literal attachment-filtered product on the actual reverse marginal law.
example (schedule : SignSequence) (horizon : ℕ)
    (survives : (horizon : ℕ∞) ≤ extinctionTime schedule)
    (u v : ℕ ⊕ ℕ) (hu : u ∈ vertexLabels schedule horizon)
    (hv : v ∈ vertexLabels schedule horizon) (distinct : u ≠ v)
    (phase : ℕ) (below_births : phase ≤ min (birthTime horizon u) (birthTime horizon v)) :
    (lawAfter schedule horizon (horizon - phase)).real {F | F.root u ≠ F.root v} =
      ∏ step ∈ (Finset.Ioc phase (min (birthTime horizon u) (birthTime horizon v))).filter
        (fun step => schedule step = true),
        (1 - 1 / ((activeCount schedule step).toNat.choose 2 : ℝ)) :=
  phaseLaw_separation_birth_product_attachment schedule horizon survives hu hv distinct below_births

#print axioms Freezing1.Reverse.phaseLaw

#print axioms Freezing1.Reverse.phaseLaw_probability

#print axioms Freezing1.Reverse.phaseLaw_top

#print axioms Freezing1.Reverse.phaseLaw_valid

#print axioms Freezing1.Reverse.phaseLaw_succ

#print axioms Freezing1.Reverse.phaseLabels_mono

#print axioms Freezing1.Reverse.separationFactor

#print axioms Freezing1.Reverse.separationFactor_nonneg

#print axioms Freezing1.Reverse.separationFactor_le_one

#print axioms Freezing1.Reverse.transitionLaw_separation_indicator

#print axioms Freezing1.Reverse.phaseLaw_separation_succ

#print axioms Freezing1.Reverse.phaseLaw_separation_product

#print axioms Freezing1.Reverse.birthTime_le_of_mem

#print axioms Freezing1.Reverse.label_eq_frozen_of_birthTime_lt

#print axioms Freezing1.Reverse.phaseLaw_separated_from_inserted

#print axioms Freezing1.Reverse.phaseLaw_separation_at_birth_of_lt

#print axioms Freezing1.Reverse.phaseLaw_separation_at_min_birth

#print axioms Freezing1.Reverse.phaseLaw_separation_birth_product

#print axioms Freezing1.Reverse.phaseLaw_separation_birth_product_attachment

#print axioms Freezing1.Reverse.phaseLaw_coalesced_birth_product

#print axioms Freezing1.Reverse.phaseLaw_separation_drop
