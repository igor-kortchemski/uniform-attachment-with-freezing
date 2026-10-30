module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Comparing atomic probability laws on an arbitrary measurable space

The ambient state type need not be countable. A probability concentrated on
its positive singleton atoms is determined by those masses: if a second
probability agrees on almost every first-law atom, the two laws coincide.
This will permit a one-sided support bridge for the two tree constructions.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped ENNReal

theorem probability_eq_of_ae_singleton_eq {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hatom : ∀ᵐ a ∂μ, μ {a} ≠ 0)
    (heq : ∀ᵐ a ∂μ, μ {a} = ν {a}) : μ = ν := by
  let atoms : Set Ω := {a | μ {a} ≠ 0}
  have hcount : atoms.Countable := by
    have hc := Measure.countable_meas_level_set_pos (μ := μ) (g := id) measurable_id
    simpa only [id_eq, Set.ofPred_eq_eq_singleton, pos_iff_ne_zero] using hc
  have hall : ∀ a ∈ atoms, μ {a} = ν {a} := by
    intro a ha
    by_contra hne
    apply ha
    apply measure_mono_null (t := {b | ¬ μ {b} = ν {b}}) _ (ae_iff.mp heq)
    intro b hb
    change ¬ μ {b} = ν {b}
    simpa only [Set.mem_singleton_iff.mp hb] using hne
  apply Measure.eq_of_le_of_isProbabilityMeasure
  intro E
  have hE : E ∩ atoms =ᵐ[μ] E := by
    filter_upwards [hatom] with a ha
    simp [atoms, ha]
  have hcE : (E ∩ atoms).Countable := hcount.mono Set.inter_subset_right
  have hμ : (∑' a : (E ∩ atoms : Set Ω), μ {a.val}) = μ (E ∩ atoms) := by
    simpa only [Set.preimage_id] using
      (tsum_measure_preimage_singleton (μ := μ) (f := id) hcE
        (fun _ _ => measurableSet_singleton _))
  have hν : (∑' a : (E ∩ atoms : Set Ω), ν {a.val}) = ν (E ∩ atoms) := by
    simpa only [Set.preimage_id] using
      (tsum_measure_preimage_singleton (μ := ν) (f := id) hcE
        (fun _ _ => measurableSet_singleton _))
  calc
    μ E = μ (E ∩ atoms) := (measure_congr hE).symm
    _ = ∑' a : (E ∩ atoms : Set Ω), μ {a.val} := hμ.symm
    _ = ∑' a : (E ∩ atoms : Set Ω), ν {a.val} := tsum_congr fun a => hall a a.property.2
    _ = ν (E ∩ atoms) := hν
    _ ≤ ν E := measure_mono Set.inter_subset_left

end Freezing1
