module

import Freezing1.SignedUrnPositiveExtensionMaximal

/- Authored source reconstruction; source-only combined verification and
separate-module artifact verification are recorded distinctly. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
open Freezing1 Freezing1.Forward Freezing1.SignedUrn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

example (x : SignSequence) (b : ℕ) :
    (ForwardInfiniteHistory.fullLaw (positiveExtension x b)).map (Preorder.frestrictLe b) =
      (ForwardInfiniteHistory.fullLaw x).map (Preorder.frestrictLe b) :=
  fullLaw_prefix_positiveExtension x b

example (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (hb : PositiveThrough x b) :
    infiniteSquareBudget (positiveExtensionPopulation x a b) =
      (∑ i ∈ Finset.Ioc a b, ((activeCount x i : ℝ)⁻¹) ^ 2) +
        ∑' j : ℕ, (((activeCount x b : ℝ) + (j + 1 : ℕ))⁻¹) ^ 2 := by
  simpa only [squareBudget, Nat.add_sub_of_le hab] using positiveExtension_square_budget_eq x hab hb

example (x : SignSequence) {a b : ℕ} (hab : a < b) (hb : PositiveThrough x b) :
    maximumReciprocal (positiveExtensionPopulation x a b) =
      (Finset.Ioc a b).sup' (Finset.nonempty_Ioc.mpr hab) (fun i => (activeCount x i : ℝ)⁻¹) :=
  positiveExtension_maximum_eq_sourceEpsilon x hab hb

example (Z : ℕ → ℤ) :
    ∀ k, HasLaw (record (fun i (H : InfiniteUrnHistory) => H i) 0 k)
      (pathLaw Z 0 k 1) (infiniteUrnLaw Z 1) :=
  infiniteUrnLaw_hasPathLaws Z 1

example (x : SignSequence) {a b : ℕ} (hab : a ≤ b) (hb : PositiveThrough x b) :
    ∀ᵐ H ∂infiniteUrnLaw (positiveExtensionPopulation x a b) 1,
      ∀ i : ℕ, 0 ≤ H i ∧ H i ≤ positiveExtensionPopulation x a b i :=
  positiveExtension_infinite_valid x hab hb

example {x : SignSequence} {a b : ℕ} {s : State} (hd : PhaseData x a s)
    (hab : a < b) (hb : PositiveThrough x b) {r : ℕ} (hr : r ∈ s.active) {t : ℝ} (ht : 0 ≤ t) :
    (Forward.continuationLaw x a (b - a) s).real {q |
      1 + (1 + t) * (activeCount x b : ℝ) / activeCount x a <
        (componentPopulationWithRoot q a r : ℝ)} ≤
      2 * Real.exp (-((t ^ 2 / 4) * (activeCount x a : ℝ)⁻¹) /
        (((∑ i ∈ Finset.Ioc a b, ((activeCount x i : ℝ)⁻¹) ^ 2) +
            ∑' j : ℕ, (((activeCount x b : ℝ) + (j + 1 : ℕ))⁻¹) ^ 2) + t *
          max ((∑ i ∈ Finset.Ioc a b, ((activeCount x i : ℝ)⁻¹) ^ 2) +
            ∑' j : ℕ, (((activeCount x b : ℝ) + (j + 1 : ℕ))⁻¹) ^ 2)
            ((Finset.Ioc a b).sup' (Finset.nonempty_Ioc.mpr hab) (fun i => (activeCount x i : ℝ)⁻¹)))) := by
  simpa only [positiveExtension_square_budget_eq x hab.le hb, squareBudget,
    Nat.add_sub_of_le hab.le, sourceEpsilon] using
      positiveExtension_marked_component_endpoint_upper hd hab hb hr ht

example
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop) (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    (C : ℕ) (hC : 2 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ k : ℕ,
      A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ (n : ℝ) / C →
      (activeCount (x n) (C ^ k) : ℝ) ≤ ((C ^ k : ℕ) : ℝ) + 1 ∧
      (activeCount (x n) (C ^ k) : ℝ)⁻¹ ≤ K / ((C ^ k : ℕ) : ℝ) ∧
      sourceEpsilon (x n) (C ^ k) (C ^ (k + 1)) (positiveExtension_geometricBlock_lt C hC k) ≤
        K / ((C ^ k : ℕ) : ℝ) ∧
      infiniteSquareBudget (positiveExtensionPopulation (x n) (C ^ k) (C ^ (k + 1))) ≤
        K / ((C ^ k : ℕ) : ℝ) :=
  linear_positiveExtension_source_budgets x A hc hc1 hA hAinf hτ hnear hbulk C hC

#print axioms positiveExtension_agrees
#print axioms activeCount_positiveExtension_tail
#print axioms positiveExtension_extinctionTime
#print axioms fullLaw_prefix_positiveExtension
#print axioms positiveExtension_component_urn
#print axioms positiveExtension_original_component_endpoint
#print axioms positiveExtensionPopulation_signed
#print axioms reciprocal_tail_square_le
#print axioms positiveExtension_square_summable
#print axioms positiveExtension_square_budget_eq
#print axioms positiveExtension_maximum_eq_sourceEpsilon
#print axioms positiveExtension_square_budget_le_of_linear
#print axioms linear_positiveExtension_source_budgets
#print axioms urn_traj_map_record
#print axioms infiniteUrnLaw_hasPathLaws
#print axioms infiniteUrnLaw_map_eval
#print axioms positiveExtension_infinite_valid
#print axioms positiveExtension_infinite_maximal
#print axioms positiveExtension_original_urn_endpoint
#print axioms positiveExtension_component_endpoint_upper
#print axioms positiveExtension_marked_component_endpoint_upper
