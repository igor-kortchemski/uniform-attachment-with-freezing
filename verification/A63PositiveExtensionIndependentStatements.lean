module

import Freezing1.SignedUrnPositiveExtensionMaximal

/-! Independently reconstructed A63 source interfaces. Full tree-prefix
preservation, canonical urn path laws, and actual endpoint transfer are
checked separately rather than conflated into an unproved path identity. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
open Freezing1 Freezing1.Forward Freezing1.SignedUrn

set_option backward.isDefEq.respectTransparency false

example (x : SignSequence) (b : ℕ) :
    (∀ i : ℕ, i ≤ b → positiveExtension x b i = x i) ∧
      ∀ i : ℕ, b < i → positiveExtension x b i = true := by
  constructor
  · intro i hi
    exact ite_eq_left hi
  · intro i hi
    exact ite_eq_right (by omega)

example (x : SignSequence) (b : ℕ) :
    (ForwardInfiniteHistory.fullLaw (positiveExtension x b)).map
        (fun H (i : Finset.Iic b) => H i.val) =
      (ForwardInfiniteHistory.fullLaw x).map (fun H (i : Finset.Iic b) => H i.val) :=
  fullLaw_prefix_positiveExtension x b

example (x : SignSequence) (a b : ℕ) (hab : a ≤ b) :
    (∀ i : ℕ, i ≤ b - a → positiveExtensionPopulation x a b i = activeCount x (a + i)) ∧
    (∀ j : ℕ, positiveExtensionPopulation x a b (b - a + j) = activeCount x b + (j : ℤ)) :=
  ⟨fun _ hi => positiveExtensionPopulation_retained x hab hi,
    positiveExtensionPopulation_tail x hab⟩

example (Z : ℕ → ℤ) (u : ℤ) :
    ∀ k : ℕ, (infiniteUrnLaw Z u).map
      (record (fun i (H : InfiniteUrnHistory) => H i) 0 k) = pathLaw Z 0 k u := by
  intro k
  simpa only [infiniteUrnLaw, recordEval] using urn_traj_map_record Z 0 k (fun _ => u)

example {x : SignSequence} {a b : ℕ} {s : State} (hd : PhaseData x a s)
    (hab : a ≤ b) (hb : PositiveThrough x b) {r : ℕ} (hr : r ∈ s.active) :
    (Forward.continuationLaw x a (b - a) s).map
        (fun q => ((q.active.filter fun v => cutAncestor q a v = r).card : ℤ)) =
      (infiniteUrnLaw (positiveExtensionPopulation x a b) 1).map (fun H => H (b - a)) := by
  exact (positiveExtension_original_component_endpoint hd hab hb hr).trans
    (infiniteUrnLaw_map_eval _ 1 (b - a)).symm

example (x : SignSequence) (a b : ℕ) (hab : a ≤ b) (hb : PositiveThrough x b) :
    (∑' i : ℕ, ((positiveExtensionPopulation x a b (i + 1) : ℝ)⁻¹) ^ 2) =
      (∑ i ∈ Finset.Ioc a b, ((activeCount x i : ℝ)⁻¹) ^ 2) +
        ∑' j : ℕ, (((activeCount x b : ℝ) + (j + 1 : ℕ))⁻¹) ^ 2 := by
  simpa only [infiniteSquareBudget, squareBudget, Nat.add_sub_of_le hab] using
    positiveExtension_square_budget_eq x hab hb

example (x : SignSequence) (a b : ℕ) (hab : a < b) (hb : PositiveThrough x b) :
    sSup (Set.range fun i : ℕ => (positiveExtensionPopulation x a b (i + 1) : ℝ)⁻¹) =
      (Finset.Ioc a b).sup' (Finset.nonempty_Ioc.mpr hab)
        (fun i => (activeCount x i : ℝ)⁻¹) :=
  positiveExtension_maximum_eq_sourceEpsilon x hab hb

example (x : SignSequence) (a b : ℕ) (hab : a < b) (hb : PositiveThrough x b)
    (t : ℝ) (ht : 0 ≤ t) :
    (infiniteUrnLaw (positiveExtensionPopulation x a b) 1).real {H |
      ∃ i : ℕ, 1 ≤ i ∧ t / (activeCount x a : ℝ) <
        |(H i : ℝ) / positiveExtensionPopulation x a b i - (activeCount x a : ℝ)⁻¹|} ≤
      2 * Real.exp (-((t ^ 2 / 4) * (activeCount x a : ℝ)⁻¹) /
        (((∑ i ∈ Finset.Ioc a b, ((activeCount x i : ℝ)⁻¹) ^ 2) +
            ∑' j : ℕ, (((activeCount x b : ℝ) + (j + 1 : ℕ))⁻¹) ^ 2) + t *
          max ((∑ i ∈ Finset.Ioc a b, ((activeCount x i : ℝ)⁻¹) ^ 2) +
            ∑' j : ℕ, (((activeCount x b : ℝ) + (j + 1 : ℕ))⁻¹) ^ 2)
            ((Finset.Ioc a b).sup' (Finset.nonempty_Ioc.mpr hab)
              (fun i => (activeCount x i : ℝ)⁻¹)))) := by
  simpa only [positiveExtension_square_budget_eq x hab.le hb, squareBudget,
    Nat.add_sub_of_le hab.le, sourceEpsilon] using positiveExtension_infinite_maximal x hab hb ht

example {x : SignSequence} {a b : ℕ} {s : State} (hd : PhaseData x a s)
    (hab : a < b) (hb : PositiveThrough x b) {r : ℕ} (hr : r ∈ s.active)
    (k : ℕ) :
    (Forward.continuationLaw x a (b - a) s).real {q |
      1 + (1 + (k : ℝ) ^ 2) * (activeCount x b : ℝ) / activeCount x a <
        ((insert r (q.active.filter fun v => cutAncestor q a v = r)).card : ℝ)} ≤
      2 * Real.exp (-(((k : ℝ) ^ 4 / 4) * (activeCount x a : ℝ)⁻¹) /
        (infiniteSquareBudget (positiveExtensionPopulation x a b) + (k : ℝ) ^ 2 *
          max (infiniteSquareBudget (positiveExtensionPopulation x a b)) (sourceEpsilon x a b hab))) := by
  simpa only [componentPopulationWithRoot, componentActive, ← pow_mul,
    show (2 : ℕ) * 2 = 4 by norm_num] using
    positiveExtension_marked_component_endpoint_upper hd hab hb hr (sq_nonneg (k : ℝ))

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x) (C : ℕ) (hC : 2 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ k : ℕ,
      A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ (n : ℝ) / C →
      (activeCount (x n) (C ^ k) : ℝ) ≤ ((C ^ k : ℕ) : ℝ) + 1 ∧
      (activeCount (x n) (C ^ k) : ℝ)⁻¹ ≤ K / ((C ^ k : ℕ) : ℝ) ∧
      (Finset.Ioc (C ^ k) (C ^ (k + 1))).sup'
          (Finset.nonempty_Ioc.mpr (positiveExtension_geometricBlock_lt C hC k))
          (fun i => (activeCount (x n) i : ℝ)⁻¹) ≤ K / ((C ^ k : ℕ) : ℝ) ∧
      ((∑ i ∈ Finset.Ioc (C ^ k) (C ^ (k + 1)), ((activeCount (x n) i : ℝ)⁻¹) ^ 2) +
        ∑' j : ℕ, (((activeCount (x n) (C ^ (k + 1)) : ℝ) + (j + 1 : ℕ))⁻¹) ^ 2) ≤
          K / ((C ^ k : ℕ) : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := linear_positiveExtension_source_budgets x A hc hc1 hA hAinf hτ hnear hbulk C hC
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with n hn k hAk hupper
  have hh := hn k hAk hupper
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hb : C ^ (k + 1) ≤ n := by
    have h := (le_div_iff₀ hC0).mp hupper
    rw [pow_succ]
    exact_mod_cast h
  have hp : PositiveThrough (x n) (C ^ (k + 1)) :=
    fun i hi => (lt_extinctionTime_iff (x n) n).mp (hτ n) i (hi.trans hb)
  have hlt := positiveExtension_geometricBlock_lt C hC k
  simpa only [sourceEpsilon, positiveExtension_square_budget_eq (x n) hlt.le hp,
    squareBudget, Nat.add_sub_of_le hlt.le] using hh

#print axioms fullLaw_prefix_positiveExtension
#print axioms positiveExtensionPopulation_signed
#print axioms urn_traj_map_record
#print axioms infiniteUrnLaw_hasPathLaws
#print axioms infiniteUrnLaw_map_eval
#print axioms positiveExtension_infinite_valid
#print axioms positiveExtension_original_component_endpoint
#print axioms positiveExtension_square_summable
#print axioms positiveExtension_square_budget_eq
#print axioms positiveExtension_maximum_eq_sourceEpsilon
#print axioms reciprocal_tail_square_le
#print axioms positiveExtension_infinite_maximal
#print axioms positiveExtension_component_endpoint_upper
#print axioms positiveExtension_marked_component_endpoint_upper
#print axioms uniform_positiveExtension_budgets
#print axioms linear_positiveExtension_source_budgets
