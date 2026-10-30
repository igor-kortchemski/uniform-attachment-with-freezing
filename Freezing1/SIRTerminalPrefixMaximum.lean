module

public import Freezing1.SIRLateMaximum
public import Freezing1.MainSIRUniformHeightStrong
public import Freezing1.ForwardPrefixEvents

/-!
# Actual terminal and earlier maximum-height marginals

Canonical truncation gives the correct earlier maximum even when extinction
occurred before the cut. The identities use the true adaptive word mixture.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem ValidAt.treeHeight_truncate_eq_of_le {T : ℕ} {s : State} (hs : ValidAt T s)
    {a : ℕ} (hTa : T ≤ a) : treeHeight (truncateAt s a) = treeHeight s := by
  apply le_antisymm (treeHeight_truncate_le s a)
  apply Finset.sup_le
  intro v hv
  have hva := (hs.vertices_le v hv).trans hTa
  have hm : v ∈ (truncateAt s a).vertices := Finset.mem_filter.mpr ⟨hv, hva⟩
  have hh := height_le_treeHeight hm
  simpa only [truncateAt, ite_eq_left hva] using hh

theorem treeLaw_truncated_height_event_after_extinction (x : SignSequence) {N a T : ℕ}
    (hτ : extinctionTime x = T) (hTN : T ≤ N) (A : Set ℕ) :
    treeLaw x N {s | treeHeight (truncateAt s a) ∈ A} = treeLaw x a {s | treeHeight s ∈ A} := by
  have hN := treeLaw_constant_after_extinction hτ (N - T)
  rw [show T + (N - T) = N by omega] at hN
  rw [hN]
  by_cases haT : a ≤ T
  · exact treeLaw_prefix_event x (by rw [hτ]) haT (fun s => treeHeight s ∈ A)
  · have ha := treeLaw_constant_after_extinction hτ (a - T)
    rw [show T + (a - T) = a by omega] at ha
    rw [ha]
    apply measure_congr
    filter_upwards [treeLaw_valid x T] with s hs
    exact propext (by rw [hs.treeHeight_truncate_eq_of_le (by omega)])

end Freezing1.Forward

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem terminalForwardLaw_valid (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ s ∂terminalForwardLaw rate n, Forward.ValidAt (2 * n + 1) s := by
  apply (ae_iff_prob_eq_one measurable_from_top).mpr
  rw [terminalForwardLaw, Measure.bind_apply (by trivial) (measurable_of_countable _).aemeasurable]
  calc
    _ = ∫⁻ _w, (1 : ℝ≥0∞) ∂signWordLaw rate n (2 * n + 1) := by
      apply lintegral_congr
      intro w
      exact (ae_iff_prob_eq_one measurable_from_top).mp (Forward.treeLaw_valid _ _)
    _ = _ := by simp

theorem terminalForwardLaw_map_plane (rate : ℝ≥0) (n : ℕ) :
    (terminalForwardLaw rate n).map Forward.State.toPlaneState =
      (treeFullLaw rate n).map (fun H => (H (2 * n + 1)).tree) := by
  rw [terminalForwardLaw, Measure.map_bind (measurable_of_countable _).aemeasurable
    Forward.measurable_toPlaneState.aemeasurable]
  exact (treeFullLaw_plane_original_word_mixture rate n (2 * n + 1)).symm

theorem terminalForwardLaw_maximum_event_eq_actual (rate : ℝ≥0) (n : ℕ) (A : Set ℕ) :
    terminalForwardLaw rate n {s | Forward.treeHeight s ∈ A} =
      treeFullLaw rate n {H | (H (2 * n + 1)).tree.vertices.sup List.length ∈ A} := by
  calc
    _ = terminalForwardLaw rate n {s | s.toPlaneState.vertices.sup List.length ∈ A} := by
      apply measure_congr
      filter_upwards [terminalForwardLaw_valid rate n] with s hs
      exact propext (by rw [hs.toPlaneState_treeHeight])
    _ = ((terminalForwardLaw rate n).map Forward.State.toPlaneState)
        {s | s.vertices.sup List.length ∈ A} := by
      rw [Measure.map_apply Forward.measurable_toPlaneState (Set.to_countable _).measurableSet]
      rfl
    _ = _ := by
      rw [terminalForwardLaw_map_plane, Measure.map_apply (by fun_prop) (Set.to_countable _).measurableSet]
      rfl

/-- The complete terminal mixture's canonical prefix maximum has the true
fixed-word earlier law. Extinct-before-cut words are included. -/
theorem terminalForwardLaw_prefix_maximum_event_eq_earlier_word (rate : ℝ≥0) (n : ℕ) (A : Set ℕ) :
    terminalForwardLaw rate n {s | Forward.treeHeight (Forward.truncateAt s n) ∈ A} =
      ((signWordLaw rate n (2 * n + 1)).bind
        (fun w => Forward.treeLaw (ForwardAnnealed.wordSchedule w) n)) {s | Forward.treeHeight s ∈ A} := by
  rw [terminalForwardLaw, Measure.bind_apply (by trivial) (measurable_of_countable _).aemeasurable,
    Measure.bind_apply (by trivial) (measurable_of_countable _).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [signWordLaw_feasible rate n (2 * n + 1)] with w hw
  obtain ⟨T, hT, hτ, _, _⟩ := terminal_word_first_extinction n w hw
  exact Forward.treeLaw_truncated_height_event_after_extinction _ hτ hT A

end Freezing1.SIR
