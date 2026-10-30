module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-! The one shared uniform variable used by the survival coupling. -/

@[expose] public section

namespace Freezing1.ConditionalSurvival

open Set MeasureTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def unitLaw : Measure ℝ := volume.restrict (Icc 0 1)

instance unitLaw_probability : IsProbabilityMeasure unitLaw := by
  constructor
  simp [unitLaw]

theorem unitLaw_Iic {a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    unitLaw (Iic a) = ENNReal.ofReal a := by
  rw [unitLaw, Measure.restrict_apply measurableSet_Iic]
  have he : Iic a ∩ Icc (0 : ℝ) 1 = Icc 0 a := by
    ext u
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans ha1⟩⟩
  rw [he, Real.volume_Icc, sub_zero]

theorem unitLaw_Ioi {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    unitLaw (Ioi a) = 1 - ENNReal.ofReal a := by
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _),
    unitLaw_Iic ha0 ha1, measure_univ]

theorem unitLaw_ae_lt_one : ∀ᵐ u ∂unitLaw, u < 1 := by
  apply ae_iff.mpr
  change unitLaw {u | ¬u < 1} = 0
  have he : {u : ℝ | ¬u < 1} ∩ Icc 0 1 = {1} := by
    ext u
    simp only [mem_inter_iff, mem_ofPred_eq, not_lt, mem_Icc, mem_singleton_iff]
    constructor
    · intro h; exact le_antisymm h.2.2 h.1
    · rintro rfl; norm_num
  rw [unitLaw, Measure.restrict_apply (by measurability), he, Real.volume_singleton]

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def chooseRow (a : ℝ) (z : ℝ × Ω × Ω) : Ω := if z.1 ≤ a then z.2.1 else z.2.2

theorem measurable_chooseRow (a : ℝ) : Measurable (chooseRow (Ω := Ω) a) :=
  Measurable.ite (measurableSet_le measurable_fst measurable_const)
    (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)

theorem map_chooseRow (ν ρ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (unitLaw.prod (ν.prod ρ)).map (chooseRow a) =
      ENNReal.ofReal a • ν + (1 - ENNReal.ofReal a) • ρ := by
  ext s hs
  rw [Measure.map_apply (measurable_chooseRow a) hs]
  have he : chooseRow a ⁻¹' s =
      (Iic a ×ˢ (s ×ˢ univ)) ∪ (Ioi a ×ˢ (univ ×ˢ s)) := by
    ext z
    simp only [mem_preimage, chooseRow, mem_union, mem_prod, mem_Iic, mem_Ioi,
      mem_univ, and_true, true_and]
    split_ifs with h
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  have hd : Disjoint (Iic a ×ˢ (s ×ˢ univ)) (Ioi a ×ˢ (univ ×ˢ s)) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (not_lt_of_ge hz.1) hz'.1
  rw [he, measure_union hd (measurableSet_Ioi.prod (MeasurableSet.univ.prod hs)),
    Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    measure_univ, measure_univ, mul_one, one_mul, unitLaw_Iic ha0 ha1, unitLaw_Ioi ha0 ha1,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rfl

end Freezing1.ConditionalSurvival
