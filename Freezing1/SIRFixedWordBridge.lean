module

public import Freezing1.SIRTerminalWordMixture
public import Freezing1.ForwardPlaneLaw

/-!
# Original fixed-schedule forward laws in the terminal SIR mixture

The bridge uses the verified chronological projection of the original
uniform-choice kernel. It holds word by word, with absorption, so the
adaptive SIR environment can be mixed over the original forward tree laws.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem map_fixedWord_treeLaw_to_planeWordLaw {k : ℕ} (w : Fin k → Bool) :
    (Forward.treeLaw (ForwardAnnealed.wordSchedule w) k).map Forward.State.toPlaneState =
      planeWordLaw w := by
  induction k with
  | zero =>
    simp [Forward.treeLaw, planeWordLaw, Forward.toPlaneState_initial]
  | succ k ih =>
    conv_lhs => rw [← Fin.snoc_init_self w]
    rw [Forward.treeLaw, ForwardAnnealed.wordSchedule_snoc_last,
      Forward.treeLaw_eq_of_schedule_prefix
        (ForwardAnnealed.wordSchedule_snoc_prefix (Fin.init w) (w (Fin.last k))),
      Measure.map_bind measurable_from_top.aemeasurable
        Forward.measurable_toPlaneState.aemeasurable]
    change (Forward.treeLaw (ForwardAnnealed.wordSchedule (Fin.init w)) k).bind
      (fun s => (Forward.transitionLaw s (k + 1) (w (Fin.last k))).map Forward.State.toPlaneState) =
        (planeWordLaw (Fin.init w)).bind
          (fun s => PlaneForward.signedTransitionLaw s (w (Fin.last k)))
    rw [← ih (Fin.init w), Measure.bind_map Forward.measurable_toPlaneState.aemeasurable
      (measurable_of_countable _).aemeasurable]
    apply Measure.bind_congr_right
    filter_upwards [Forward.treeLaw_valid (ForwardAnnealed.wordSchedule (Fin.init w)) k]
      with s hs
    exact Forward.map_transitionLaw_toPlaneState hs (w (Fin.last k))

theorem planeWordTreeLaw_eq_original_forward {k : ℕ} (w : Fin k → Bool) :
    planeWordTreeLaw w = (Forward.treeLaw (ForwardAnnealed.wordSchedule w) k).map
      (fun s => PlaneForward.shape s.toPlaneState) := by
  rw [planeWordTreeLaw, ← map_fixedWord_treeLaw_to_planeWordLaw,
    Measure.map_map (measurable_of_countable _) Forward.measurable_toPlaneState]
  rfl

theorem treeFullLaw_plane_original_word_mixture (rate : ℝ≥0) (n k : ℕ) :
    (treeFullLaw rate n).map (fun H => (H k).tree) =
      (signWordLaw rate n k).bind (fun w =>
        (Forward.treeLaw (ForwardAnnealed.wordSchedule w) k).map Forward.State.toPlaneState) := by
  rw [treeFullLaw_plane_word_mixture_all]
  congr 1
  funext w
  exact (map_fixedWord_treeLaw_to_planeWordLaw w).symm

/-- The complete terminal SIR law is a mixture over the original fixed-sign
uniform attachment/freezing tree construction, with its actual adaptive
word weights. No fresh sign independence is postulated. -/
theorem embeddedTerminalTreeLaw_original_word_mixture (rate : ℝ≥0) (n : ℕ) :
    (embeddedTerminalTreeLaw rate n : Measure PlaneTree.Tree) =
      (signWordLaw rate n (2 * n + 1)).bind (fun w =>
        (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).map
          (fun s => PlaneForward.shape s.toPlaneState)) := by
  rw [embeddedTerminalTreeLaw_word_mixture]
  congr 1
  funext w
  exact planeWordTreeLaw_eq_original_forward w

end Freezing1.SIR
