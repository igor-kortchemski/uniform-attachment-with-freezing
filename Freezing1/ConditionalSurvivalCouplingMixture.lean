module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Exact conditional-law mixture for decreasing survival events

Zero residual events use an explicit probability fallback. The coefficient
of that fallback is proved to be zero; no zero measure is silently treated
as a probability distribution.
-/

@[expose] public section

namespace Freezing1.ConditionalSurvival

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def conditionalOr (μ : Measure Ω) (s : Set Ω) (fallback : Measure Ω) : Measure Ω :=
  if μ s = 0 then fallback else μ[|s]

instance conditionalOr_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Set Ω) (fallback : Measure Ω) [IsProbabilityMeasure fallback] :
    IsProbabilityMeasure (conditionalOr μ s fallback) := by
  unfold conditionalOr
  split_ifs with h
  · infer_instance
  · exact cond_isProbabilityMeasure h

theorem mass_smul_conditionalOr (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Set Ω) (fallback : Measure Ω) :
    μ s • conditionalOr μ s fallback = μ.restrict s := by
  by_cases h : μ s = 0
  · rw [h, zero_smul]
    exact (Measure.restrict_eq_zero.mpr h).symm
  · rw [conditionalOr, ite_eq_right h, ProbabilityTheory.cond, smul_smul,
      ENNReal.mul_inv_cancel h (measure_ne_top μ s), one_smul]

/-- Conditioning on a larger event is exactly a mixture of conditioning on
the smaller event and on the residual event, including a null residual. -/
theorem conditional_mixture (μ : Measure Ω) [IsFiniteMeasure μ]
    {s t : Set Ω} (ht : MeasurableSet t) (hts : t ⊆ s) (ht0 : μ t ≠ 0)
    (fallback : Measure Ω) :
    μ[|s] = (μ t / μ s) • μ[|t] +
      (μ (s \ t) / μ s) • conditionalOr μ (s \ t) fallback := by
  have hsmall := mass_smul_conditionalOr μ t fallback
  rw [conditionalOr, ite_eq_right ht0] at hsmall
  symm
  calc
    _ = (μ s)⁻¹ • (μ t • μ[|t] + μ (s \ t) • conditionalOr μ (s \ t) fallback) := by
      rw [smul_add, smul_smul, smul_smul]
      simp only [ENNReal.div_eq_inv_mul]
    _ = (μ s)⁻¹ • (μ.restrict t + μ.restrict (s \ t)) := by
      rw [hsmall, mass_smul_conditionalOr]
    _ = (μ s)⁻¹ • μ.restrict s := by
      rw [← Measure.restrict_inter_add_sdiff s ht, inter_eq_right.mpr hts]
    _ = _ := rfl

noncomputable def weight (μ : Measure Ω) (E : ℕ → Set Ω) (n : ℕ) : ℝ :=
  (μ (⋂ j, E j)).toReal / (μ (E n)).toReal

theorem intersection_mass_le (μ : Measure Ω) (E : ℕ → Set Ω) (n : ℕ) :
    μ (⋂ j, E j) ≤ μ (E n) :=
  measure_mono (iInter_subset E n)

theorem event_mass_ne_zero (μ : Measure Ω) (E : ℕ → Set Ω)
    (hpos : μ (⋂ j, E j) ≠ 0) (n : ℕ) : μ (E n) ≠ 0 :=
  ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hpos) (intersection_mass_le μ E n))

theorem weight_mem (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω)
    (hpos : μ (⋂ j, E j) ≠ 0) (n : ℕ) : weight μ E n ∈ Icc (0 : ℝ) 1 := by
  have hn : 0 < (μ (E n)).toReal :=
    ENNReal.toReal_pos (event_mass_ne_zero μ E hpos n) (measure_ne_top μ (E n))
  refine ⟨div_nonneg ENNReal.toReal_nonneg hn.le, ?_⟩
  apply (div_le_one hn).mpr
  exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mpr
    (intersection_mass_le μ E n)

theorem ofReal_weight (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω)
    (_hpos : μ (⋂ j, E j) ≠ 0) (n : ℕ) :
    ENNReal.ofReal (weight μ E n) = μ (⋂ j, E j) / μ (E n) := by
  rw [weight, ← ENNReal.toReal_div, ENNReal.ofReal_toReal]
  exact ne_top_of_le_ne_top (by simp) ((ENNReal.div_le_div_right
    (intersection_mass_le μ E n) _).trans ENNReal.div_self_le_one)

theorem weight_tendsto_one (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω)
    (hE : ∀ n, MeasurableSet (E n)) (hanti : Antitone E)
    (hpos : μ (⋂ j, E j) ≠ 0) : Tendsto (weight μ E) atTop (𝓝 1) := by
  have hmass := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hE n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top μ _⟩
  have hr := (ENNReal.tendsto_toReal (measure_ne_top μ (⋂ j, E j))).comp hmass
  have hne : (μ (⋂ j, E j)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hpos (measure_ne_top μ _)).ne'
  have hc : Tendsto (fun _ : ℕ => (μ (⋂ j, E j)).toReal) atTop
      (𝓝 (μ (⋂ j, E j)).toReal) := tendsto_const_nhds
  convert hc.div hr hne using 1
  · funext n
    rfl
  · rw [div_self hne]

theorem residual_weight (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω)
    (hE : ∀ n, MeasurableSet (E n)) (hpos : μ (⋂ j, E j) ≠ 0) (n : ℕ) :
    μ (E n \ ⋂ j, E j) / μ (E n) = 1 - ENNReal.ofReal (weight μ E n) := by
  have hsum : μ (⋂ j, E j) + μ (E n \ ⋂ j, E j) = μ (E n) := by
    simpa only [inter_eq_right.mpr (iInter_subset E n)] using
      measure_inter_add_sdiff (E n) (MeasurableSet.iInter hE)
  have hweights : ENNReal.ofReal (weight μ E n) + μ (E n \ ⋂ j, E j) / μ (E n) = 1 := by
    rw [ofReal_weight μ E hpos n, ENNReal.div_add_div_same, hsum,
      ENNReal.div_self (event_mass_ne_zero μ E hpos n) (measure_ne_top μ _)]
  exact (ENNReal.sub_eq_of_eq_add (by simp)
    (by simpa only [add_comm] using hweights.symm)).symm

end Freezing1.ConditionalSurvival
