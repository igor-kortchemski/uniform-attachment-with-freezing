module

public import Freezing1.PlaneFrozenBalls
public import Freezing1.ForwardAnnealedLifetime
public import Freezing1.ForwardPlaneHistory
public import Mathlib.MeasureTheory.Integral.Indicator

/-!
# The actual annealed plane chain has eventually frozen finite balls
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology ENNReal Classical

theorem Forward.ValidAt.toPlaneState_frozenBall {n : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt n s) {h : ℕ} (hf : Forward.BallFrozen s h) :
    PlaneForward.FrozenBall s.toPlaneState h := by
  intro u hu hlen ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  have hdepth : s.height v ≤ h := by
    rw [← hs.planeAddress_length hv]
    exact hlen
  exact hf v hv hdepth ((Forward.mem_toPlaneState_active hs hv).mp ha)

namespace PlaneForward

theorem fullLaw_eventually_frozenBall (p : unitInterval) (hp : (p : ℝ) < 1) (h : ℕ) :
    ∀ᵐ H ∂fullLaw p initial, ∃ a, ∀ k ≥ a, FrozenBall (H k) h := by
  have hm : MeasurableSet {H : ℕ → State | ∃ a, ∀ k ≥ a, FrozenBall (H k) h} := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.exists
    intro a
    apply Measurable.forall
    intro k
    exact measurable_const.imp ((measurable_of_countable (fun s : State => FrozenBall s h)).comp
      (measurable_pi_apply k))
  rw [← ForwardAnnealed.map_fullLaw_toPlaneState p]
  apply (ae_map_iff ForwardAnnealed.measurable_planeHistory.aemeasurable hm).mpr
  filter_upwards [ForwardAnnealed.fullLaw_valid p, ForwardAnnealed.fullLaw_legalOrHeld p,
    ForwardAnnealed.fullLaw_all_vertices_eventually_frozen p hp] with H hv hl hf
  obtain ⟨x, hlx⟩ := ForwardAnnealed.exists_schedule_of_legalOrHeld hl
  obtain ⟨a, ha⟩ := ForwardInfiniteHistory.all_balls_eventually_frozen hv hlx hf h
  refine ⟨a, fun k hk => ?_⟩
  exact (hv k).toPlaneState_frozenBall
    ((ForwardInfiniteHistory.ballFrozen_persists hv hlx ha k hk).1)

theorem fullLaw_not_frozenBall_tendsto_zero (p : unitInterval) (hp : (p : ℝ) < 1) (h : ℕ) :
    Tendsto (fun k => (fullLaw p initial).real {H | ¬FrozenBall (H k) h}) atTop (𝓝 0) := by
  have hm : ∀ k, MeasurableSet {H : ℕ → State | ¬FrozenBall (H k) h} := by
    intro k
    exact ((measurable_of_countable (fun s : State => ¬FrozenBall s h)).comp
      (measurable_pi_apply k)).setOf
  have he : ∀ᵐ H ∂fullLaw p initial, ∀ᶠ k in atTop, FrozenBall (H k) h := by
    filter_upwards [fullLaw_eventually_frozenBall p hp h] with H hH
    exact eventually_atTop.mpr hH
  have hh := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (μ := fullLaw p initial) (A := ∅) MeasurableSet.empty hm (by
      filter_upwards [he] with H hH
      filter_upwards [hH] with k hk
      simp only [Set.mem_empty_iff_false, iff_false, not_not]
      exact hk)
  simp only [measure_empty] at hh
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hh
  simpa only [measureReal_def, Function.comp_def, ENNReal.toReal_zero] using hr

end PlaneForward
end Freezing1
