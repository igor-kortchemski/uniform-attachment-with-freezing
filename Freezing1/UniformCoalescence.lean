module

public import Freezing1.CoalescenceBounds

/-!
# Coalescence of conditionally independent uniform vertices

The two samples include both active and frozen vertices and may coincide.
The law below is identified with uniform sampling conditional on the actual
terminal history. Its tail bound retains the exact diagonal probability.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped ENNReal BigOperators Classical

theorem integral_uniform_finset {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    (∫ a, f a ∂Measure.uniformOfFinset s) = (∑ a ∈ s, f a) / s.card := by
  unfold Measure.uniformOfFinset
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
    ring
  · intro a _
    apply Integrable.smul_measure (integrable_dirac (by simp))
    simp [hs.ne_empty]

theorem uniform_bind_real {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α]
    (s : Finset α) (hs : s.Nonempty) (κ : α → Measure β)
    [∀ a, IsProbabilityMeasure (κ a)] (A : Set β) (hA : MeasurableSet A) :
    ((Measure.uniformOfFinset s).bind κ).real A =
      (∑ a ∈ s, (κ a).real A) / s.card := by
  unfold Measure.real
  rw [Measure.bind_apply hA (measurable_of_countable _).aemeasurable,
    ← integral_toReal (measurable_of_countable _).aemeasurable
      (Filter.Eventually.of_forall fun a => measure_lt_top (κ a) A)]
  exact integral_uniform_finset s hs _

namespace ReverseHistory

/-- Uniform independent labels, then their coalescence time in the actual
reverse history. A theorem below proves equality with conditional sampling
from the terminal forest itself. -/
noncomputable def uniformCoalescenceLaw (x : SignSequence) (n : ℕ) : Measure ℕ :=
  (uniformVertex x n).bind fun u =>
    (uniformVertex x n).bind fun v =>
      (fullLaw x n).map fun H => coalescenceTime n H u v

theorem uniformCoalescenceLaw_probability (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) : IsProbabilityMeasure (uniformCoalescenceLaw x n) := by
  let := uniformVertex_isProbabilityMeasure (activeCount_nonneg_of_le_extinctionTime hn)
  apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
  apply Filter.Eventually.of_forall
  intro u
  apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
  apply Filter.Eventually.of_forall
  intro v
  exact Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr inferInstance

/-- This is genuinely sampling twice independently and uniformly conditional
on the actual terminal forest, not merely an average over frozen birth labels. -/
theorem uniformCoalescenceLaw_eq_conditional (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    uniformCoalescenceLaw x n = (fullLaw x n).bind fun H =>
      (Measure.uniformOfFinset H.current.vertices).bind fun u =>
        (Measure.uniformOfFinset H.current.vertices).map fun v => coalescenceTime n H u v := by
  let := uniformVertex_isProbabilityMeasure (activeCount_nonneg_of_le_extinctionTime hn)
  calc
    _ = (uniformVertex x n).bind (fun u => (fullLaw x n).bind fun H =>
        (uniformVertex x n).map fun v => coalescenceTime n H u v) := by
      unfold uniformCoalescenceLaw
      congr 1
      funext u
      simp_rw [← Measure.bind_dirac_eq_map (fullLaw x n) measurable_from_top]
      rw [Measure.bind_comm (measurable_from_prod_countable_right fun _ => measurable_from_top)]
      congr 1
      funext H
      exact Measure.bind_dirac_eq_map _ (measurable_of_countable _)
    _ = (fullLaw x n).bind (fun H => (uniformVertex x n).bind fun u =>
        (uniformVertex x n).map fun v => coalescenceTime n H u v) :=
      Measure.bind_comm (measurable_from_prod_countable_right fun _ => measurable_from_top)
    _ = _ := by
      apply Measure.bind_congr_right
      filter_upwards [lawAfter_current_valid x n n hn le_rfl] with H hH
      have hv : H.current.vertices = vertexLabels x n := by
        simpa only [Nat.sub_self, Reverse.phaseLabels_zero] using hH.vertices_eq
      rw [hv]
      rfl

theorem uniformCoalescenceLaw_real (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (A : Set ℕ) :
    (uniformCoalescenceLaw x n).real A =
      (∑ u ∈ vertexLabels x n, ∑ v ∈ vertexLabels x n,
        (fullLaw x n).real {H | coalescenceTime n H u v ∈ A}) /
          ((vertexLabels x n).card : ℝ) ^ 2 := by
  have hne := vertexLabels_nonempty (activeCount_nonneg_of_le_extinctionTime hn)
  let := uniformVertex_isProbabilityMeasure (activeCount_nonneg_of_le_extinctionTime hn)
  let κ := fun u v : ℕ ⊕ ℕ => (fullLaw x n).map fun H => coalescenceTime n H u v
  have hκ : ∀ u v, IsProbabilityMeasure (κ u v) := fun _ _ =>
    Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr inferInstance
  let := hκ
  have hbind : ∀ u, IsProbabilityMeasure ((uniformVertex x n).bind (κ u)) := fun u =>
    isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      (Filter.Eventually.of_forall fun v => hκ u v)
  let := hbind
  have havg : ∀ u, ((uniformVertex x n).bind (κ u)).real A =
      (∑ v ∈ vertexLabels x n, (κ u v).real A) / (vertexLabels x n).card := by
    intro u
    let := hκ u
    exact uniform_bind_real _ hne (κ u) A (by measurability)
  change ((Measure.uniformOfFinset (vertexLabels x n)).bind
    fun u => (uniformVertex x n).bind (κ u)).real A = _
  rw [uniform_bind_real _ hne _ A (by measurability)]
  simp_rw [havg]
  have he : ∀ u v, (κ u v).real A =
      (fullLaw x n).real {H | coalescenceTime n H u v ∈ A} := by
    intro u v
    unfold κ Measure.real
    rw [Measure.map_apply measurable_from_top (by measurability)]
    rfl
  simp_rw [he]
  rw [← Finset.sum_div]
  ring

/-- The diagonal sampling probability is `1/N_n`; every off-diagonal pair,
including active labels, is controlled by the same finite hazard sum. -/
theorem uniformCoalescenceLaw_tail_le (x : SignSequence) (n i : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (uniformCoalescenceLaw x n).real {c | i ≤ c} ≤
      1 / ((vertexLabels x n).card : ℝ) +
        ∑ t ∈ Finset.Ioc i n, Reverse.coalescenceHazard x t := by
  have hne := vertexLabels_nonempty (activeCount_nonneg_of_le_extinctionTime hn)
  have hcard : (0 : ℝ) < (vertexLabels x n).card := by exact_mod_cast hne.card_pos
  rw [uniformCoalescenceLaw_real x n hn]
  calc
    _ ≤ (∑ u ∈ vertexLabels x n, ∑ v ∈ vertexLabels x n,
        ((if u = v then (1 : ℝ) else 0) +
          ∑ t ∈ Finset.Ioc i n, Reverse.coalescenceHazard x t)) /
          ((vertexLabels x n).card : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      exact fullLaw_coalescenceTime_ge_le_diag_add_sum x n i hn hu hv
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have hdiag : ∑ u ∈ vertexLabels x n, ∑ v ∈ vertexLabels x n,
          (if u = v then (1 : ℝ) else 0) = ((vertexLabels x n).card : ℝ) := by
        calc
          _ = ∑ _u ∈ vertexLabels x n, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro u hu
            simp [hu]
          _ = _ := by simp
      rw [hdiag]
      field_simp

end ReverseHistory
end Freezing1
