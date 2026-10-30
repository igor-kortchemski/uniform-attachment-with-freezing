module

public import Freezing1.MainSIRUniformHeightStrong
public import Freezing1.ForwardPlaneDistance

/-!
# The actual SIR uniform-pair distance at population time

The plane kernel draws two vertices independently conditional on the same
actual state. The exact chronological graph-distance bridge retains both
height coordinates and the pair diagonal.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory RandomEnvironment
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def sirPairDataLaw (rate : ℝ≥0) (n k : ℕ) : Measure (ℕ × ℕ × ℕ) :=
  ((treeFullLaw rate n).map (fun H => (H k).tree)).bind PlaneForward.pairDataKernel

theorem sirPairDataLaw_at_n_eq_environment (rate : ℝ≥0) (n : ℕ) :
    sirPairDataLaw rate n n = environmentPairDataLaw rate n := by
  rw [sirPairDataLaw, treeFullLaw_plane_original_word_mixture,
    Measure.bind_bind (measurable_of_countable _).aemeasurable PlaneForward.pairDataKernel.aemeasurable]
  change (signWordLaw rate n n).bind (fun w =>
    ((Forward.treeLaw (ForwardAnnealed.wordSchedule w) n).map Forward.State.toPlaneState).bind
      PlaneForward.pairDataKernel) = _
  simp_rw [Forward.planePairDataLaw_fixed]
  rw [environmentPairDataLaw, environmentTreeLaw,
    Measure.bind_bind (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable]
  rfl

theorem sir_time_n_uniform_distance_tendsto (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => sirPairDataLaw (rate n) n n
      {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2|}) atTop (nhds 0) := by
  simpa only [sirPairDataLaw_at_n_eq_environment] using
    strong_environment_uniform_distance rate hstrong heps

end Freezing1.SIR
