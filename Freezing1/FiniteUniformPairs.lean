module

public import Freezing1.FiniteUniformRestriction
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Retained vertices and two independent uniform samples

The product finite-set law is the true independent product. Retaining a
fraction of the vertices controls every pair event, including the diagonal.
-/

@[expose] public section

namespace Freezing1.FiniteUniform

open MeasureTheory
open scoped ENNReal Classical

theorem uniformOfFinset_probability {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {A : Finset α} (hA : A.Nonempty) :
    IsProbabilityMeasure (Measure.uniformOfFinset A) := by
  constructor
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast hA.card_pos.ne') (by simp)

theorem uniformOfFinset_product {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α] [Countable β]
    {A : Finset α} {B : Finset β} (hA : A.Nonempty) (hB : B.Nonempty) :
    Measure.uniformOfFinset (A.product B) =
      (Measure.uniformOfFinset A).prod (Measure.uniformOfFinset B) := by
  haveI := uniformOfFinset_probability hA
  haveI := uniformOfFinset_probability hB
  apply Measure.ext_of_singleton
  rintro ⟨x, y⟩
  rw [Measure.uniformOfFinset_apply_singleton, ← Set.singleton_prod_singleton,
    Measure.prod_prod]
  simp only [Measure.uniformOfFinset_apply_singleton, Finset.mem_product]
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ B <;>
    simp [hx, hy, ENNReal.mul_inv]

theorem squared_fraction_loss_le_twice {u v : ℝ} (hv : 0 < v) :
    (v * v - u * u) / (v * v) ≤ 2 * ((v - u) / v) := by
  apply (div_le_iff₀ (mul_pos hv hv)).mpr
  have he : 2 * ((v - u) / v) * (v * v) = 2 * (v - u) * v := by field_simp
  rw [he]
  nlinarith [sq_nonneg (v - u)]

theorem uniform_pair_event_difference_le {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α]
    {A B : Finset α} (hA : A.Nonempty) (hAB : A ⊆ B) (S : Set (α × α)) :
    |((Measure.uniformOfFinset B).prod (Measure.uniformOfFinset B)).real S -
      ((Measure.uniformOfFinset A).prod (Measure.uniformOfFinset A)).real S| ≤
        2 * (((B.card : ℝ) - A.card) / B.card) := by
  have hB : B.Nonempty := hA.mono hAB
  rw [← uniformOfFinset_product hB hB, ← uniformOfFinset_product hA hA]
  have hh := uniformOfFinset_event_difference_le (hA.product hA)
    (Finset.product_subset_product hAB hAB) S
  simp only [Finset.card_product, Nat.cast_mul] at hh
  exact hh.trans (squared_fraction_loss_le_twice (by exact_mod_cast hB.card_pos))

theorem uniform_pair_observation_difference_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [Countable α]
    {A B : Finset α} (hA : A.Nonempty) (hAB : A ⊆ B) (f g : α × α → β)
    (he : ∀ u ∈ A, ∀ v ∈ A, f (u, v) = g (u, v)) (S : Set β) (hS : MeasurableSet S) :
    |(((Measure.uniformOfFinset B).prod (Measure.uniformOfFinset B)).map f).real S -
      (((Measure.uniformOfFinset A).prod (Measure.uniformOfFinset A)).map g).real S| ≤
        2 * (((B.card : ℝ) - A.card) / B.card) := by
  have hB : B.Nonempty := hA.mono hAB
  rw [← uniformOfFinset_product hB hB, ← uniformOfFinset_product hA hA]
  have hh := uniformOfFinset_observation_difference_le (hA.product hA)
    (Finset.product_subset_product hAB hAB) f g
    (by rintro ⟨u, v⟩ huv; exact he u (Finset.mem_product.mp huv).1 v (Finset.mem_product.mp huv).2)
    S hS
  simp only [Finset.card_product, Nat.cast_mul] at hh
  exact hh.trans (squared_fraction_loss_le_twice (by exact_mod_cast hB.card_pos))

end Freezing1.FiniteUniform
