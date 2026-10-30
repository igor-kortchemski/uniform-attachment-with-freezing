module

import Freezing1.ForwardComponentUrnPathMaximal

/-! Independent reconstruction of the complete original-past mixture and
the genuine component's finite joint path laws. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Freezing1 Freezing1.Forward Freezing1.ForwardInfiniteHistory

example (x : SignSequence) {a b : ℕ} (hab : a ≤ b) :
    fullLaw (positiveExtension x b) =
      ((fullLaw x).map (Preorder.frestrictLe a)).bind
        (continuationHistoryLaw (positiveExtension x b) a) :=
  positiveExtension_bind_original_prefix x hab

example (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (hb : PositiveThrough x b) :
    ∀ᵐ past ∂(fullLaw x).map (Preorder.frestrictLe a),
      ∀ r ∈ (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩).active, ∀ k : ℕ,
        HasLaw (SignedUrn.record
          (fun i (H : History) => componentPopulation (H (a + i)) a r) 0 k)
          (SignedUrn.pathLaw (SignedUrn.positiveExtensionPopulation x a b) 0 k 1)
          (continuationHistoryLaw (positiveExtension x b) a past) :=
  positiveExtension_original_component_pathLaws x hab hb

example (x : SignSequence) {a b : ℕ} (hab : a < b) (hb : PositiveThrough x b)
    (past : (i : Finset.Iic a) → State)
    (hs : HasHistory (positiveExtension x b) a (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩))
    {r : ℕ} (hr : r ∈ (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩).active)
    {t : ℝ} (ht : 0 ≤ t) :
    (continuationHistoryLaw (positiveExtension x b) a past).real {H |
      ∃ i : ℕ, 1 ≤ i ∧ t / (activeCount x a : ℝ) <
        |(componentPopulation (H (a + i)) a r : ℝ) /
          SignedUrn.positiveExtensionPopulation x a b i - (activeCount x a : ℝ)⁻¹|} ≤
      2 * Real.exp (-((t ^ 2 / 4) * (activeCount x a : ℝ)⁻¹) /
        (SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b) + t *
          max (SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b))
            (SignedUrn.sourceEpsilon x a b hab))) :=
  positiveExtension_actual_component_infinite_maximal x hab hb past hs hr ht

#print axioms continuationLaw_componentPrefixRecord
#print axioms fullLaw_bind_continuationHistoryLaw
#print axioms continuationHistoryLaw_component_record
#print axioms positiveExtension_bind_original_prefix
#print axioms positiveExtension_actual_component_hasPathLaws
#print axioms positiveExtension_original_component_pathLaws
#print axioms positiveExtension_actual_component_infinite_maximal
