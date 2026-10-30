module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Tactic

/-!
# Uniform sampling from a large finite set and a retained subset

Deleting a small fraction of vertices changes the probability of every
single-vertex event by at most that fraction. The comparison allows the
observable to change outside the retained vertices.
-/

@[expose] public section

namespace Freezing1.FiniteUniform

open MeasureTheory
open scoped ENNReal Classical

theorem abs_fraction_difference_le {u v a b : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (ha : 0 ≤ a) (hau : a ≤ u) (hab : a ≤ b) (hdiff : b - a ≤ v - u) :
    |b / v - a / u| ≤ (v - u) / v := by
  have hv : 0 < v := hu.trans_le huv
  have he : b / v - a / u = (b * u - a * v) / (v * u) := by
    field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hv hu), div_le_iff₀ (mul_pos hv hu)]
  have hr : ((v - u) / v) * (v * u) = (v - u) * u := by field_simp
  rw [hr, abs_le]
  have h1 := mul_nonneg hu.le (sub_nonneg.mpr hab)
  have h2 := mul_nonneg ha (sub_nonneg.mpr huv)
  have h3 := mul_nonneg (sub_nonneg.mpr hau) (sub_nonneg.mpr huv)
  have h4 := mul_nonneg hu.le (sub_nonneg.mpr hdiff)
  constructor <;> nlinarith

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

theorem uniformOfFinset_real (A : Finset α) (S : Set α) :
    (Measure.uniformOfFinset A).real S = ((A.filter (fun x => x ∈ S)).card : ℝ) / A.card := by
  rw [measureReal_def, Measure.uniformOfFinset_apply, ENNReal.toReal_div]
  simp

theorem uniformOfFinset_event_difference_le {A B : Finset α}
    (hA : A.Nonempty) (hAB : A ⊆ B) (S : Set α) :
    |(Measure.uniformOfFinset B).real S - (Measure.uniformOfFinset A).real S| ≤
      ((B.card : ℝ) - A.card) / B.card := by
  classical
  have hf : A.filter (fun x => x ∈ S) ⊆ B.filter (fun x => x ∈ S) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hAB (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
  have hd : (B.filter (fun x => x ∈ S)) \ (A.filter (fun x => x ∈ S)) ⊆ B \ A := by
    intro x hx
    obtain ⟨hxB, hxA⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hxB, hxS⟩ := Finset.mem_filter.mp hxB
    exact Finset.mem_sdiff.mpr ⟨hxB, fun h => hxA (Finset.mem_filter.mpr ⟨h, hxS⟩)⟩
  have hcard := Finset.card_le_card hd
  rw [Finset.card_sdiff_of_subset hf, Finset.card_sdiff_of_subset hAB] at hcard
  rw [uniformOfFinset_real, uniformOfFinset_real]
  apply abs_fraction_difference_le
  · exact_mod_cast hA.card_pos
  · exact_mod_cast Finset.card_le_card hAB
  · positivity
  · exact_mod_cast Finset.card_filter_le A (fun x => x ∈ S)
  · exact_mod_cast Finset.card_le_card hf
  · have hR : (((B.filter (fun x => x ∈ S)).card -
          (A.filter (fun x => x ∈ S)).card : ℕ) : ℝ) ≤ ((B.card - A.card : ℕ) : ℝ) := by
        exact_mod_cast hcard
    rw [Nat.cast_sub (Finset.card_le_card hf), Nat.cast_sub (Finset.card_le_card hAB)] at hR
    exact hR

theorem uniformOfFinset_observation_difference_le {β : Type*}
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable α]
    {A B : Finset α} (hA : A.Nonempty) (hAB : A ⊆ B) (f g : α → β)
    (he : ∀ x ∈ A, f x = g x) (S : Set β) (hS : MeasurableSet S) :
    |((Measure.uniformOfFinset B).map f).real S -
      ((Measure.uniformOfFinset A).map g).real S| ≤
        ((B.card : ℝ) - A.card) / B.card := by
  have hm (C : Finset α) (h : α → β) :
      ((Measure.uniformOfFinset C).map h).real S = (Measure.uniformOfFinset C).real (h ⁻¹' S) := by
    rw [measureReal_def, Measure.map_apply (measurable_of_countable _) hS]
    rfl
  rw [hm, hm]
  have hAe : (Measure.uniformOfFinset A).real (g ⁻¹' S) =
      (Measure.uniformOfFinset A).real (f ⁻¹' S) := by
    rw [uniformOfFinset_real, uniformOfFinset_real]
    have heq : A.filter (fun x => x ∈ g ⁻¹' S) = A.filter (fun x => x ∈ f ⁻¹' S) := by
      apply Finset.filter_congr
      intro x hx
      simp only [Set.mem_preimage, he x hx]
    rw [heq]
  rw [hAe]
  exact uniformOfFinset_event_difference_le hA hAB _

end Freezing1.FiniteUniform
