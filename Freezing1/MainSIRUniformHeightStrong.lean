module

public import Freezing1.SIRRandomEnvironmentTransferStrong
public import Freezing1.ForwardPlaneAddress

/-!
# Actual SIR plane-state observations at population time

The chronological address map is a bijection on the entire vertex set.
It preserves heights, conditional uniform sampling, and the maximum.
-/

@[expose] public section

namespace Freezing1.PlaneForward

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

noncomputable def vertexHeightKernel : Kernel State ℕ where
  toFun s := if s.vertices.Nonempty then (Measure.uniformOfFinset s.vertices).map List.length
    else Measure.dirac 0
  measurable' := measurable_of_countable _

instance vertexHeightKernel_markov : IsMarkovKernel vertexHeightKernel := by
  constructor
  intro s
  change IsProbabilityMeasure (if s.vertices.Nonempty then _ else _)
  split_ifs with hs
  · have hp : IsProbabilityMeasure (Measure.uniformOfFinset s.vertices) := by
      constructor
      rw [Measure.uniformOfFinset_apply]
      simp only [Set.mem_univ, Finset.filter_true]
      exact ENNReal.div_self (by exact_mod_cast hs.card_pos.ne') (by simp)
    have := hp
    exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
      |>.mpr inferInstance
  · infer_instance

end Freezing1.PlaneForward

namespace Freezing1.Forward

open MeasureTheory ProbabilityTheory
open scoped Classical

theorem ValidAt.toPlaneState_treeHeight {n : ℕ} {s : State} (hs : ValidAt n s) :
    s.toPlaneState.vertices.sup List.length = treeHeight s := by
  change (s.vertices.image (planeAddress s)).sup List.length = s.vertices.sup s.height
  rw [Finset.sup_image]
  apply Finset.sup_congr rfl
  intro v hv
  exact hs.planeAddress_length hv

theorem ValidAt.toPlaneState_vertexHeightKernel {n : ℕ} {s : State} (hs : ValidAt n s) :
    PlaneForward.vertexHeightKernel s.toPlaneState = vertexHeightKernel s := by
  have hsne : s.vertices.Nonempty := ⟨0, hs.root_mem⟩
  have hpne : s.toPlaneState.vertices.Nonempty := hsne.image (planeAddress s)
  change (if s.toPlaneState.vertices.Nonempty then _ else _) =
    (if s.vertices.Nonempty then _ else _)
  rw [ite_eq_left hpne, ite_eq_left hsne]
  have hmap : (Measure.uniformOfFinset s.vertices).map (planeAddress s) =
      Measure.uniformOfFinset s.toPlaneState.vertices := by
    exact map_uniformOfFinset_of_injOn s.vertices (planeAddress s)
      (measurable_of_countable _) (fun _ hu _ hv he => hs.planeAddress_injective hu hv he)
  rw [← hmap, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  apply Measure.map_congr
  have hae : ∀ᵐ v ∂Measure.uniformOfFinset s.vertices, v ∈ s.vertices := by
    rw [ae_iff]
    simp [Measure.uniformOfFinset_apply]
  filter_upwards [hae] with v hv
  exact hs.planeAddress_length hv

end Freezing1.Forward

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory RandomEnvironment
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

instance environmentTreeLaw_probability (rate : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (environmentTreeLaw rate n) := by
  unfold environmentTreeLaw
  exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Eventually.of_forall fun _ => inferInstance)

theorem environmentTreeLaw_valid (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ s ∂environmentTreeLaw rate n, Forward.ValidAt n s := by
  apply (ae_iff_prob_eq_one measurable_from_top).mpr
  rw [environmentTreeLaw, Measure.bind_apply (by trivial) (measurable_of_countable _).aemeasurable]
  calc
    _ = ∫⁻ _w, (1 : ℝ≥0∞) ∂signWordLaw rate n n := by
      apply lintegral_congr
      intro w
      exact (ae_iff_prob_eq_one measurable_from_top).mp (Forward.treeLaw_valid _ n)
    _ = _ := by simp

theorem environmentTreeLaw_map_plane (rate : ℝ≥0) (n : ℕ) :
    (environmentTreeLaw rate n).map Forward.State.toPlaneState =
      (treeFullLaw rate n).map (fun H => (H n).tree) := by
  rw [environmentTreeLaw, Measure.map_bind (measurable_of_countable _).aemeasurable
    Forward.measurable_toPlaneState.aemeasurable]
  exact (treeFullLaw_plane_original_word_mixture rate n n).symm

/-- A conditionally uniform sample from all vertices of the current actual
SIR tree, including its frozen vertices. -/
noncomputable def sirUniformHeightLaw (rate : ℝ≥0) (n k : ℕ) : Measure ℕ :=
  ((treeFullLaw rate n).map (fun H => (H k).tree)).bind PlaneForward.vertexHeightKernel

theorem sirUniformHeightLaw_at_n_eq_environment (rate : ℝ≥0) (n : ℕ) :
    sirUniformHeightLaw rate n n = environmentUniformHeightLaw rate n := by
  rw [sirUniformHeightLaw, ← environmentTreeLaw_map_plane,
    Measure.bind_map Forward.measurable_toPlaneState.aemeasurable PlaneForward.vertexHeightKernel.aemeasurable]
  change (environmentTreeLaw rate n).bind (fun s =>
    PlaneForward.vertexHeightKernel s.toPlaneState) =
      (environmentTreeLaw rate n).bind Forward.vertexHeightKernel
  apply Measure.bind_congr_right
  filter_upwards [environmentTreeLaw_valid rate n] with s hs
  exact hs.toPlaneState_vertexHeightKernel

theorem treeFullLaw_time_n_maximum_event_eq_environment (rate : ℝ≥0) (n : ℕ) (A : Set ℕ) :
    treeFullLaw rate n {H | (H n).tree.vertices.sup List.length ∈ A} =
      environmentTreeLaw rate n {s | Forward.treeHeight s ∈ A} := by
  calc
    _ = ((treeFullLaw rate n).map (fun H => (H n).tree))
        {s | s.vertices.sup List.length ∈ A} := by
      rw [Measure.map_apply (by fun_prop) (Set.to_countable _).measurableSet]
      rfl
    _ = ((environmentTreeLaw rate n).map Forward.State.toPlaneState)
        {s | s.vertices.sup List.length ∈ A} := by rw [environmentTreeLaw_map_plane]
    _ = environmentTreeLaw rate n {s | s.toPlaneState.vertices.sup List.length ∈ A} := by
      rw [Measure.map_apply Forward.measurable_toPlaneState (Set.to_countable _).measurableSet]
      rfl
    _ = _ := by
      apply measure_congr
      filter_upwards [environmentTreeLaw_valid rate n] with s hs
      exact propext (by rw [hs.toPlaneState_treeHeight])

theorem sir_time_n_uniform_height_tendsto (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => sirUniformHeightLaw (rate n) n n
      {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - 1|}) atTop (nhds 0) := by
  simpa only [sirUniformHeightLaw_at_n_eq_environment] using
    strong_environment_uniform_height rate hstrong heps

theorem sir_time_n_maximum_tendsto (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => treeFullLaw (rate n) n {H | eps ≤
      |(((H n).tree.vertices.sup List.length : ℕ) : ℝ) / Real.log (n : ℝ) - Real.exp 1|})
      atTop (nhds 0) := by
  convert strong_environment_maximum rate hstrong heps using 1
  funext n
  exact treeFullLaw_time_n_maximum_event_eq_environment (rate n) n
    {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - Real.exp 1|}

end Freezing1.SIR
