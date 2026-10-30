module

public import Freezing1.ForwardPlaneUpdates
public import Freezing1.ForwardPlaneKernel
public import Freezing1.ForwardAnnealedHistory

/-!
# The chronological projection preserves the actual transition laws

The uniform choice of a birth ID becomes the uniform choice of its distinct
chronological address. Averaging the independent Bernoulli sign therefore
gives precisely the verified finite plane kernel.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

theorem measurable_toPlaneState : Measurable State.toPlaneState := measurable_from_top

theorem toPlaneState_active_card {n : ℕ} {s : State} (hs : ValidAt n s) :
    s.toPlaneState.active.card = s.active.card := by
  apply Finset.card_image_iff.mpr
  intro v hv w hw he
  exact hs.planeAddress_injective (hs.active_subset hv) (hs.active_subset hw) he

theorem map_transitionLaw_toPlaneState {n : ℕ} {s : State} (hs : ValidAt n s)
    (sign : Bool) :
    (transitionLaw s (n + 1) sign).map State.toPlaneState =
      PlaneForward.signedTransitionLaw s.toPlaneState sign := by
  classical
  ext A hA
  rw [Measure.map_apply measurable_toPlaneState hA]
  by_cases ha : s.active.Nonempty
  · have ha' : s.toPlaneState.active.Nonempty := ha.image _
    rw [transitionLaw_apply s (n + 1) sign ha,
      PlaneForward.signedTransitionLaw_apply s.toPlaneState sign ha']
    have hfilter : s.toPlaneState.active.filter (fun a =>
        PlaneForward.step s.toPlaneState sign a ∈ A) =
        (s.active.filter (fun v => (step s (n + 1) sign v).toPlaneState ∈ A)).image
          (planeAddress s) := by
      rw [show s.toPlaneState.active = s.active.image (planeAddress s) from rfl,
        Finset.filter_image]
      congr 1
      apply Finset.filter_congr
      intro v hv
      rw [toPlaneState_step hs sign (hs.active_subset hv)]
    rw [hfilter, toPlaneState_active_card hs]
    congr 2
    symm
    apply Finset.card_image_iff.mpr
    intro v hv w hw he
    exact hs.planeAddress_injective
      (hs.active_subset (Finset.mem_filter.mp hv).1)
      (hs.active_subset (Finset.mem_filter.mp hw).1) he
  · have he : s.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have he' : s.toPlaneState.active = ∅ := by simp [State.toPlaneState, he]
    rw [transitionLaw_eq_dirac_of_empty s (n + 1) sign he,
      PlaneForward.signedTransitionLaw_eq_dirac_of_empty s.toPlaneState sign he']
    rw [Measure.dirac_apply' _ (hA.preimage measurable_toPlaneState),
      Measure.dirac_apply' _ hA]
    rfl

theorem map_annealedTransition_toPlaneState {n : ℕ} {s : State} (hs : ValidAt n s)
    (p : unitInterval) :
    (ForwardAnnealed.transitionLaw p s (n + 1)).map State.toPlaneState =
      PlaneForward.transition p s.toPlaneState := by
  rw [ForwardAnnealed.transitionLaw, Measure.map_bind
    (measurable_of_countable _).aemeasurable measurable_toPlaneState.aemeasurable]
  change (ForwardAnnealed.signLaw p).bind
    (fun sign => (transitionLaw s (n + 1) sign).map State.toPlaneState) =
      (ForwardAnnealed.signLaw p).bind (PlaneForward.signedTransitionLaw s.toPlaneState)
  congr 1
  funext sign
  exact map_transitionLaw_toPlaneState hs sign

end Freezing1.Forward

namespace Freezing1.ForwardAnnealed

open Forward MeasureTheory ProbabilityTheory
open scoped Classical

theorem treeLaw_valid (p : unitInterval) (n : ℕ) :
    ∀ᵐ s ∂treeLaw p n, ValidAt n s := by
  rw [← map_eval]
  apply (ae_map_iff (measurable_pi_apply n).aemeasurable (by trivial)).mpr
  exact (fullLaw_valid p).mono fun H hH => hH n

theorem fullLaw_toPlaneState_valid (p : unitInterval) :
    ∀ᵐ H ∂fullLaw p, ∀ n, PlaneForward.Valid (H n).toPlaneState := by
  filter_upwards [fullLaw_initial p, fullLaw_valid p, fullLaw_legalOrHeld p]
    with H h0 hv hl
  intro n
  induction n with
  | zero => rw [h0, toPlaneState_initial]; exact PlaneForward.initial_valid
  | succ n ih =>
    obtain ⟨sign, hs⟩ := hl n
    rcases hs with ⟨_, he⟩ | ⟨v, ha, he⟩
    · rw [he]
      exact ih
    · rw [he, toPlaneState_step (hv n) sign ((hv n).active_subset ha)]
      exact ih.step sign _

theorem treeLaw_toPlaneState_valid (p : unitInterval) (n : ℕ) :
    ∀ᵐ s ∂treeLaw p n, PlaneForward.Valid s.toPlaneState := by
  rw [← map_eval]
  apply (ae_map_iff (measurable_pi_apply n).aemeasurable (by trivial)).mpr
  exact (fullLaw_toPlaneState_valid p).mono fun H hH => hH n

theorem map_treeLaw_toPlaneState (p : unitInterval) (n : ℕ) :
    (treeLaw p n).map State.toPlaneState =
      (PlaneForward.fullLaw p PlaneForward.initial).map (fun H => H n) := by
  induction n with
  | zero =>
    rw [treeLaw, Measure.map_dirac' measurable_toPlaneState,
      toPlaneState_initial, PlaneForward.fullLaw, CountableMarkovChain.map_eval_zero]
  | succ n ih =>
    simp only [PlaneForward.fullLaw] at ih
    rw [treeLaw, Measure.map_bind measurable_from_top.aemeasurable
      measurable_toPlaneState.aemeasurable]
    change _ = (CountableMarkovChain.fullLaw (PlaneForward.transition p)
      PlaneForward.initial).map (fun H => H (n + 1))
    rw [CountableMarkovChain.map_eval_succ, ← ih,
      Measure.bind_map measurable_toPlaneState.aemeasurable
        (PlaneForward.transition p).aemeasurable]
    apply Measure.bind_congr_right
    filter_upwards [treeLaw_valid p n] with s hs
    exact map_annealedTransition_toPlaneState hs p

end Freezing1.ForwardAnnealed
