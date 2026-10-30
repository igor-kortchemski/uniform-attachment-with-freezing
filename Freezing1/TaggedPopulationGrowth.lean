module

public import Freezing1.TaggedPopulationCounts
public import Freezing1.FinitePermutationAverage

/-!
# Growth in the actual tagged continuation

The uniform matching estimate is integrated using a proved relabeling
symmetry of the true multiset kernel. The event simultaneously restricts
the total tall population and each component size. Neither conditioning on
that event nor independence of the two restrictions is used.
-/

@[expose] public section

namespace Freezing1.TaggedPopulation

open MeasureTheory
open scoped ENNReal BigOperators Classical

theorem all_rootPopulation_relabel (e : Equiv.Perm ℕ) (m : State) (M : ℝ) :
    (∀ r, (rootPopulation (relabel e m) r : ℝ) ≤ M) ↔
      ∀ r, (rootPopulation m r : ℝ) ≤ M := by
  constructor
  · intro h r
    simpa only [rootPopulation_relabel] using h (e r)
  · intro h r
    obtain ⟨q, rfl⟩ := e.surjective r
    simpa only [rootPopulation_relabel] using h q

theorem permutation_goodTall_growth_failure_le {roots G : Finset ℕ} {m : State}
    (hm : TagsIn roots m) (hG : G ⊆ roots) (t : ℝ) {a b M : ℝ}
    (ha : 3 ≤ a) (hb : 0 < b) (hroots : (roots.card : ℝ) ≤ a + 1)
    (hg : b ≤ G.card) (hweight : 4 * a ≤ totalTall m t) (hM : 0 ≤ M)
    (hcap : ∀ r, (rootPopulation m r : ℝ) ≤ M) :
    (uniformPermutationLaw roots).real
      {σ | (goodTall (relabel (extendRootPermutation roots σ) m) G t : ℝ) < 2 * b} ≤
        3 * M / b := by
  have hsum : (∑ r : roots, (rootTallPopulation m t r : ℝ)) = totalTall m t := by
    calc
      _ = ∑ r ∈ roots, (rootTallPopulation m t r : ℝ) :=
        Finset.sum_coe_sort roots (fun r : ℕ => (rootTallPopulation m t r : ℝ))
      _ = _ := by rw [← Nat.cast_sum, sum_rootTallPopulation hm t]
  have hgood : b ≤ ((goodRoots roots G).card : ℝ) := by rw [card_goodRoots roots G hG]; exact hg
  have hpop : (Fintype.card roots : ℝ) ≤ a + 1 := by simpa using hroots
  have hset : {σ : Equiv.Perm roots |
      (goodTall (relabel (extendRootPermutation roots σ) m) G t : ℝ) < 2 * b} =
      {σ | weightedPermutationCount (goodRoots roots G)
        (fun r : roots => (rootTallPopulation m t r : ℝ)) σ < 2 * b} := by
    ext σ
    simp only [Set.mem_ofPred_eq]
    rw [goodTall_eq_weightedPermutationCount hm G t σ]
  rw [hset]
  apply uniformPermutation_growth_failure_le (goodRoots roots G)
    (fun r : roots => (rootTallPopulation m t r : ℝ)) ha hb hpop hgood
    (by simpa only [hsum] using hweight) hM (fun _ => Nat.cast_nonneg _)
  intro r
  have hr : (rootTallPopulation m t r : ℝ) ≤ rootPopulation m r := by
    exact_mod_cast rootTallPopulation_le m t r
  exact hr.trans (hcap r)

/-- The finite matching bound is now a bound under the true continuation
kernel from one copy of each initial root. -/
theorem continuationLaw_goodTall_growth_failure_le
    (x : SignSequence) (a₀ k : ℕ) (roots G : Finset ℕ) (hG : G ⊆ roots) (t : ℝ)
    {a b M : ℝ} (ha : 3 ≤ a) (hb : 0 < b) (hroots : (roots.card : ℝ) ≤ a + 1)
    (hg : b ≤ G.card) (hM : 0 ≤ M) :
    (continuationLaw x a₀ k (initial roots)).real
      {m | 4 * a ≤ (totalTall m t : ℝ) ∧
        (∀ r, (rootPopulation m r : ℝ) ≤ M) ∧ (goodTall m G t : ℝ) < 2 * b} ≤
      3 * M / b := by
  let E : Set State := {m | 4 * a ≤ (totalTall m t : ℝ) ∧
    (∀ r, (rootPopulation m r : ℝ) ≤ M) ∧ (goodTall m G t : ℝ) < 2 * b}
  apply measureReal_le_of_permutation_average
    (continuationLaw x a₀ k (initial roots))
    (fun σ : Equiv.Perm roots => relabel (extendRootPermutation roots σ))
    (fun _ => measurable_from_top)
    (fun σ => continuationLaw_initial_invariant x a₀ k roots _ (image_extendRootPermutation roots σ))
    (show MeasurableSet E from by trivial)
  filter_upwards [continuationLaw_tagsIn x a₀ k (tagsIn_initial roots)] with m hm
  by_cases hc : 4 * a ≤ (totalTall m t : ℝ) ∧ ∀ r, (rootPopulation m r : ℝ) ≤ M
  · refine (measureReal_mono (fun σ hσ => hσ.2.2) (measure_ne_top _ _)).trans ?_
    exact permutation_goodTall_growth_failure_le hm hG t ha hb hroots hg hc.1 hM hc.2
  · have he : {σ : Equiv.Perm roots | relabel (extendRootPermutation roots σ) m ∈ E} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro σ hσ
      apply hc
      exact ⟨by simpa only [totalTall_relabel] using hσ.1,
        (all_rootPopulation_relabel _ m M).mp hσ.2.1⟩
    rw [he, measureReal_empty]
    positivity

end Freezing1.TaggedPopulation
