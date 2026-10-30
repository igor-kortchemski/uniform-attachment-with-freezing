module

public import Freezing1.MainSIRUniformSamplesStrong
public import Freezing1.TwoPointMixtureLimit

/-! Joint actual survival gates and terminal uniform observations. -/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

noncomputable def gatedPlaneSampleKernel {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (K : Kernel PlaneForward.State α) (f : α → ℝ) :
    Kernel (ℕ × PlaneForward.State) (Bool × ℝ) where
  toFun z := (K z.2).map (fun a => (decide (0 < z.1), f a))
  measurable' := measurable_of_countable _

instance gatedPlaneSampleKernel_markov {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (K : Kernel PlaneForward.State α) [IsMarkovKernel K]
    (f : α → ℝ) : IsMarkovKernel (gatedPlaneSampleKernel K f) := by
  constructor
  intro z
  change IsProbabilityMeasure ((K z.2).map (fun a => (decide (0 < z.1), f a)))
  exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
    |>.mpr inferInstance

noncomputable def terminalJointSampleLaw {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (rate : ℝ≥0) (n a : ℕ)
    (K : Kernel PlaneForward.State α) [IsMarkovKernel K] (f : α → ℝ) :
    ProbabilityMeasure (Bool × ℝ) := by
  let g : (ℕ → TreeState) → ℕ × PlaneForward.State := fun H =>
    ((H a).counts.infectious, (H (2 * n + 1)).tree)
  have hg : Measurable g := by dsimp [g]; fun_prop
  have : IsProbabilityMeasure ((treeFullLaw rate n).map g) :=
    Measure.isProbabilityMeasure_map_iff hg.aemeasurable |>.mpr inferInstance
  exact ⟨((treeFullLaw rate n).map g).bind (gatedPlaneSampleKernel K f), inferInstance⟩

theorem terminalJointSampleLaw_apply {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (rate : ℝ≥0) (n a : ℕ)
    (K : Kernel PlaneForward.State α) [IsMarkovKernel K] (f : α → ℝ)
    (A : Set (Bool × ℝ)) (hA : MeasurableSet A) :
    (terminalJointSampleLaw rate n a K f : Measure (Bool × ℝ)) A =
      ∫⁻ H, K (H (2 * n + 1)).tree {v | (decide (0 < (H a).counts.infectious), f v) ∈ A}
        ∂treeFullLaw rate n := by
  change (((treeFullLaw rate n).map (fun H =>
    ((H a).counts.infectious, (H (2 * n + 1)).tree))).bind (gatedPlaneSampleKernel K f)) A = _
  rw [Measure.bind_map (by fun_prop) (gatedPlaneSampleKernel K f).aemeasurable]
  rw [Measure.bind_apply hA (show AEMeasurable
    (fun H : ℕ → TreeState => gatedPlaneSampleKernel K f
      ((H a).counts.infectious, (H (2 * n + 1)).tree)) (treeFullLaw rate n) from
        ((gatedPlaneSampleKernel K f).measurable.comp (by fun_prop)).aemeasurable)]
  apply lintegral_congr
  intro H
  exact Measure.map_apply (measurable_of_countable _) hA

theorem terminalJointSampleLaw_gate {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (rate : ℝ≥0) (n a : ℕ)
    (K : Kernel PlaneForward.State α) [IsMarkovKernel K] (f : α → ℝ) :
    (terminalJointSampleLaw rate n a K f : Measure (Bool × ℝ)) {z | z.1 = true} =
      countsFullLaw rate n {C | 0 < (C a).infectious} := by
  rw [terminalJointSampleLaw_apply _ _ _ _ _ _ (by measurability)]
  have hG : MeasurableSet {H : ℕ → TreeState | 0 < (H a).counts.infectious} := by measurability
  calc
    _ = ∫⁻ H, {H : ℕ → TreeState | 0 < (H a).counts.infectious}.indicator (fun _ => (1 : ℝ≥0∞)) H
        ∂treeFullLaw rate n := by
      apply lintegral_congr
      intro H
      by_cases h : 0 < (H a).counts.infectious <;> simp [h]
    _ = treeFullLaw rate n {H | 0 < (H a).counts.infectious} := by
      rw [lintegral_indicator hG]; simp
    _ = _ := by
      rw [← map_treeFullLaw_counts, Measure.map_apply (by fun_prop) (by measurability)]
      rfl

theorem terminalJointSampleLaw_bad_apply {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (rate : ℝ≥0) (n a : ℕ)
    (K : Kernel PlaneForward.State α) [IsMarkovKernel K] (f : α → ℝ) (c eps : ℝ) :
    (terminalJointSampleLaw rate n a K f : Measure (Bool × ℝ))
      {z | eps ≤ |z.2 - TwoPointMixture.gatedValue c z|} =
      ∫⁻ H, if 0 < (H a).counts.infectious then
        K (H (2 * n + 1)).tree {v | eps ≤ |f v - c|}
      else K (H (2 * n + 1)).tree {v | eps ≤ |f v|} ∂treeFullLaw rate n := by
  have hA : MeasurableSet {z : Bool × ℝ | eps ≤ |z.2 - TwoPointMixture.gatedValue c z|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp
      (measurable_snd.sub (TwoPointMixture.measurable_gatedValue c)))
  rw [terminalJointSampleLaw_apply _ _ _ _ _ _ hA]
  apply lintegral_congr
  intro H
  by_cases h : 0 < (H a).counts.infectious <;>
    simp [h, TwoPointMixture.gatedValue]

noncomputable def sirTerminalJointHeightLaw (rate : ℝ≥0) (n : ℕ) : ProbabilityMeasure (Bool × ℝ) :=
  terminalJointSampleLaw rate n (logLogStartupCutoff n) PlaneForward.vertexHeightKernel
    (fun h => (h : ℝ) / Real.log (n : ℝ))

noncomputable def sirTerminalJointDistanceLaw (rate : ℝ≥0) (n : ℕ) : ProbabilityMeasure (Bool × ℝ) :=
  terminalJointSampleLaw rate n (logLogStartupCutoff n) PlaneForward.pairDataKernel
    (fun z => (z.2.2 : ℝ) / Real.log (n : ℝ))

end Freezing1.SIR
