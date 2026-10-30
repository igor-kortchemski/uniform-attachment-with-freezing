module

public import Freezing1.SIRJointSampleLaw
public import Freezing1.MainSIRUniformDistanceStrong

/-!
# Scalar marginals of the actual terminal samples
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem terminalJointSampleLaw_snd {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (rate : ℝ≥0) (n a : ℕ)
    (K : Kernel PlaneForward.State α) [IsMarkovKernel K] (f : α → ℝ) :
    ((terminalJointSampleLaw rate n a K f).map Prod.snd : Measure ℝ) =
      (((treeFullLaw rate n).map (fun H => (H (2 * n + 1)).tree)).bind K).map f := by
  have hg : Measurable (fun H : ℕ → TreeState => (H (2 * n + 1)).tree) :=
    (measurable_of_countable TreeState.tree).comp (measurable_pi_apply _)
  ext A hA
  change (terminalJointSampleLaw rate n a K f : Measure (Bool × ℝ)).map Prod.snd A = _
  rw [Measure.map_apply measurable_snd hA,
    terminalJointSampleLaw_apply _ _ _ _ _ _ (hA.preimage measurable_snd),
    Measure.map_apply (measurable_of_countable f) hA,
    Measure.bind_map hg.aemeasurable K.measurable.aemeasurable]
  change (∫⁻ H, K (H (2 * n + 1)).tree (f ⁻¹' A) ∂treeFullLaw rate n) =
    ((treeFullLaw rate n).bind (fun H => K (H (2 * n + 1)).tree)) (f ⁻¹' A)
  exact (Measure.bind_apply (hA.preimage (measurable_of_countable f))
    (K.measurable.comp hg).aemeasurable).symm

noncomputable def terminalUniformHeightScaledLaw (rate : ℝ≥0) (n : ℕ) : ProbabilityMeasure ℝ :=
  (sirTerminalJointHeightLaw rate n).map Prod.snd

noncomputable def terminalUniformDistanceScaledLaw (rate : ℝ≥0) (n : ℕ) : ProbabilityMeasure ℝ :=
  (sirTerminalJointDistanceLaw rate n).map Prod.snd

theorem terminalUniformHeightScaledLaw_eq_sample (rate : ℝ≥0) (n : ℕ) :
    (terminalUniformHeightScaledLaw rate n : Measure ℝ) =
      (sirUniformHeightLaw rate n (2 * n + 1)).map
        (fun h : ℕ => (h : ℝ) / Real.log (n : ℝ)) :=
  terminalJointSampleLaw_snd rate n (logLogStartupCutoff n) _ _

theorem terminalUniformDistanceScaledLaw_eq_sample (rate : ℝ≥0) (n : ℕ) :
    (terminalUniformDistanceScaledLaw rate n : Measure ℝ) =
      (sirPairDataLaw rate n (2 * n + 1)).map
        (fun z : ℕ × ℕ × ℕ => (z.2.2 : ℝ) / Real.log (n : ℝ)) :=
  terminalJointSampleLaw_snd rate n (logLogStartupCutoff n) _ _

end Freezing1.SIR
