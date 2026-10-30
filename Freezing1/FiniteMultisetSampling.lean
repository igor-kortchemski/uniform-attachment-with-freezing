module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Tactic

/-!
# Uniform sampling of occurrences in a finite multiset

Repeated values retain their multiplicities. The measure is defined as the
normalized sum of Dirac masses, and its pushforward commutes with every
measurable map, including noninjective maps used to forget vertex names.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped ENNReal Classical

noncomputable def multisetUniform {α : Type*} [MeasurableSpace α]
    (m : Multiset α) : Measure α :=
  (m.card : ℝ≥0∞)⁻¹ • (m.map Measure.dirac).sum

theorem multiset_dirac_sum_apply {α : Type*} [MeasurableSpace α]
    (m : Multiset α) {E : Set α} (hE : MeasurableSet E) :
    (m.map Measure.dirac).sum E = ((m.filter (· ∈ E)).card : ℝ≥0∞) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    by_cases ha : a ∈ E <;>
      simp [ha, Measure.dirac_apply' _ hE, ih, add_comm]

theorem multisetUniform_apply {α : Type*} [MeasurableSpace α]
    (m : Multiset α) {E : Set α} (hE : MeasurableSet E) :
    multisetUniform m E = ((m.filter (· ∈ E)).card : ℝ≥0∞) / m.card := by
  rw [multisetUniform, Measure.smul_apply, smul_eq_mul, multiset_dirac_sum_apply m hE]
  exact ENNReal.div_eq_inv_mul.symm

theorem multisetUniform_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    (m : Multiset α) (hm : m ≠ 0) : IsProbabilityMeasure (multisetUniform m) := by
  constructor
  rw [multisetUniform_apply m MeasurableSet.univ]
  simp only [Set.mem_univ, Multiset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast (Multiset.card_pos.mpr hm).ne')
    (ENNReal.natCast_ne_top _)

/-- Every occurrence map transports the actual sampling measure exactly. -/
theorem map_multisetUniform {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (m : Multiset α) (f : α → β) (hf : Measurable f) :
    (multisetUniform m).map f = multisetUniform (m.map f) := by
  unfold multisetUniform
  rw [Measure.map_smul _ hf.aemeasurable, Multiset.card_map]
  congr 1
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Measure.map_add _ _ hf, ih]
    rw [Measure.map_dirac' hf]

theorem multisetUniform_finset {α : Type*} [MeasurableSpace α]
    (s : Finset α) : multisetUniform s.val = Measure.uniformOfFinset s := by
  unfold multisetUniform Measure.uniformOfFinset
  change (s.card : ℝ≥0∞)⁻¹ • (∑ a ∈ s, Measure.dirac a) = _
  rw [Finset.smul_sum]

theorem map_uniformFinset_eq_multisetUniform {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (s : Finset α) (f : α → β)
    (hf : Measurable f) :
    (Measure.uniformOfFinset s).map f = multisetUniform (s.val.map f) := by
  rw [← multisetUniform_finset]
  exact map_multisetUniform _ _ hf

theorem multisetUniform_ae_mem {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (m : Multiset α) :
    ∀ᵐ a ∂multisetUniform m, a ∈ m := by
  rw [ae_iff]
  have hE : MeasurableSet {a | a ∉ m} := by
    have he : {a | a ∉ m} = (m.toFinset : Set α)ᶜ := by ext a; simp
    rw [he]
    exact m.toFinset.finite_toSet.measurableSet.compl
  rw [multisetUniform_apply m hE]
  have hfilter : m.filter (fun a => a ∉ m) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro a ha
    exact not_not_intro ha
  simp [hfilter]

end Freezing1
