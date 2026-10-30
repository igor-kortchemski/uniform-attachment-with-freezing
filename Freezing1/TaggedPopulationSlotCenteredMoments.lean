module

public import Freezing1.TaggedPopulationSlotMoments

/-! The literal centered second moment and distinct-root covariance. -/

@[expose] public section

namespace Freezing1.TaggedPopulation

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

theorem centered_second_goodTall_slot_le {m : ℕ} {M : State} (hM : TagsIn (Finset.range m) M)
    (G : Finset ℕ) (hG : G ⊆ Finset.range m) (t : ℝ) {B : ℝ}
    (hcap : ∀ r : ℕ, (rootPopulation M r : ℝ) ≤ B) :
    (∫ σ, ((goodTall (relabel (Forward.rootSlotPermutation m σ) M) G t : ℝ) -
      ((G.card : ℝ) / m) * totalTall M t) ^ 2 ∂uniformPermutationLaw (Fin m)) ≤
      B * (((G.card : ℝ) / m) * totalTall M t) := by
  have hh := variance_goodTall_slot_le hM G t hcap
  rw [variance_eq_integral measurable_from_top.aemeasurable, integral_goodTall_slot hM G hG t] at hh
  exact hh

theorem covariance_slot_indicators_nonpos {m : ℕ} (G : Finset ℕ)
    {i j : Fin m} (hij : i ≠ j) :
    covariance (fun σ => permutationIndicator (goodSlotSet m G) σ i)
      (fun σ => permutationIndicator (goodSlotSet m G) σ j) (uniformPermutationLaw (Fin m)) ≤ 0 := by
  rw [covariance_eq_sub (uniformPermutation_memLp _ 2) (uniformPermutation_memLp _ 2),
    integral_permutationIndicator, integral_permutationIndicator]
  simp only [Pi.mul_apply]
  have hh := integral_permutationIndicator_pair_le (goodSlotSet m G) hij
  exact sub_nonpos.mpr (by simpa only [pow_two] using hh)

end Freezing1.TaggedPopulation
