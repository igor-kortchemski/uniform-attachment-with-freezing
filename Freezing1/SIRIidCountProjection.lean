module

public import Freezing1.SIRTreeWordMixture
public import Freezing1.SIRBiasedWalk

/-!
# The actual iid plane process and its absorbed count walk

The full chronological active-count history is projected from the genuine
plane-state chain. Fixed-prefix SIR extinction probabilities are then
compared with that actual walk using the adaptive finite-word estimates.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem planeFullLaw_valid (p : unitInterval) :
    ∀ᵐ H ∂PlaneForward.fullLaw p PlaneForward.initial,
      ∀ k, PlaneForward.Valid (H k) := by
  have hstep : ∀ s : PlaneForward.State, ∀ᵐ t ∂PlaneForward.transition p s,
      PlaneForward.Valid s → PlaneForward.Valid t := by
    intro s
    apply PlaneForward.transition_ae
    · intro _ hs
      exact hs
    · intro sign u _ hs
      exact hs.step sign u
  filter_upwards [CountableMarkovChain.fullLaw_initial (PlaneForward.transition p)
      PlaneForward.initial,
    CountableMarkovChain.fullLaw_steps (PlaneForward.transition p) PlaneForward.initial
      (fun s t => PlaneForward.Valid s → PlaneForward.Valid t) hstep] with H h0 hl
  intro k
  induction k with
  | zero => rw [h0]; exact PlaneForward.initial_valid
  | succ k ih => exact hl k ih

theorem plane_step_activeCard {s : PlaneForward.State} (hs : PlaneForward.Valid s)
    {u : PlaneTree.Address} (hu : u ∈ s.active) (b : Bool) :
    (PlaneForward.step s b u).active.card =
      if b then s.active.card + 1 else s.active.card - 1 := by
  cases b
  · simp [PlaneForward.step, hu, PlaneForward.freeze, Finset.card_erase_of_mem hu]
  · have hfresh : PlaneForward.newChild s u ∉ s.active := by
      intro h
      exact hs.newChild_not_mem (hs.active_subset hu) (hs.active_subset h)
    simp [PlaneForward.step, hu, PlaneForward.attach, Finset.card_insert_of_notMem hfresh]

theorem plane_signedTransitionLaw_activeCard (s : PlaneForward.State)
    (hs : PlaneForward.Valid s) (b : Bool) :
    (PlaneForward.signedTransitionLaw s b).map (fun t => t.active.card) =
      Measure.dirac (if s.active.card = 0 then 0 else
        if b then s.active.card + 1 else s.active.card - 1) := by
  have hsame : ∀ᵐ t ∂PlaneForward.signedTransitionLaw s b,
      t.active.card = if s.active.card = 0 then 0 else
        if b then s.active.card + 1 else s.active.card - 1 := by
    apply PlaneForward.signedTransitionLaw_ae
    · intro hempty
      simp [hempty]
    · intro u hu
      have hcard : s.active.card ≠ 0 := (Finset.card_pos.mpr ⟨u, hu⟩).ne'
      rw [ite_eq_right hcard, plane_step_activeCard hs hu]
  calc
    _ = (PlaneForward.signedTransitionLaw s b).map (fun _ =>
        if s.active.card = 0 then 0 else
          if b then s.active.card + 1 else s.active.card - 1) := Measure.map_congr hsame
    _ = _ := by rw [Measure.map_const]; simp

theorem plane_transition_activeCard (p : unitInterval) {s : PlaneForward.State}
    (hs : PlaneForward.Valid s) :
    (PlaneForward.transition p s).map (fun t => t.active.card) =
      BiasedWalk.transition p s.active.card := by
  change ((ForwardAnnealed.signLaw p).bind (PlaneForward.signedTransitionLaw s)).map
    (fun t => t.active.card) = _
  rw [Measure.map_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  simp_rw [plane_signedTransitionLaw_activeCard s hs]
  by_cases hcard : s.active.card = 0
  · rw [hcard]
    change (ForwardAnnealed.signLaw p).bind (fun _ => Measure.dirac 0) = Measure.dirac 0
    rw [Measure.bind_const, measure_univ, one_smul]
  · simp only [ite_eq_right hcard]
    rw [Measure.bind_dirac_eq_map _ (measurable_of_countable _)]
    change (bernoulliMeasure true false p).map
      (fun b => if b then s.active.card + 1 else s.active.card - 1) = _
    rw [map_bernoulliMeasure]
    simp [BiasedWalk.transition, hcard]

/-- Entire-history equality, rather than a premise about independent SIR
signs or a comparison of one-dimensional distributions alone. -/
theorem map_planeFullLaw_activeCard (p : unitInterval) :
    (PlaneForward.fullLaw p PlaneForward.initial).map
      (fun H k => (H k).active.card) = BiasedWalk.fullLaw p := by
  change (CountableMarkovChain.fullLaw (PlaneForward.transition p) PlaneForward.initial).map
    (fun H k => (H k).active.card) = CountableMarkovChain.fullLaw (BiasedWalk.transition p) 1
  rw [show (1 : ℕ) = PlaneForward.initial.active.card by simp [PlaneForward.initial]]
  apply CountableMarkovChain.map_fullLaw_of_ae_intertwining
    (PlaneForward.transition p) (BiasedWalk.transition p)
    (fun s : PlaneForward.State => s.active.card) PlaneForward.initial
  intro k
  filter_upwards [planeFullLaw_valid p] with H hH
  exact plane_transition_activeCard p (hH k)

theorem countsFullLaw_infectious_event_eq_tree (rate : ℝ≥0) (n k : ℕ) (A : Set ℕ) :
    (countsFullLaw rate n).real {H | (H k).infectious ∈ A} =
      ((treeFullLaw rate n).map (fun H => (H k).tree)).real
        {s | s.active.card ∈ A} := by
  unfold Measure.real
  congr 1
  rw [← map_treeFullLaw_counts, Measure.map_apply (by fun_prop) (by measurability),
    Measure.map_apply (by fun_prop) (Set.to_countable _).measurableSet]
  rfl

theorem planeFullLaw_activeCard_event_eq_walk (p : unitInterval) (k : ℕ) (A : Set ℕ) :
    ((PlaneForward.fullLaw p PlaneForward.initial).map (fun H => H k)).real
        {s | s.active.card ∈ A} =
      (BiasedWalk.fullLaw p).real {H | H k ∈ A} := by
  unfold Measure.real
  congr 1
  rw [← map_planeFullLaw_activeCard, Measure.map_apply (by fun_prop) (by measurability),
    Measure.map_apply (by fun_prop) (by measurability)]
  rfl

/-- Every fixed-time infectious-count event converges under the actual SIR
law to its probability for the actual iid absorbed walk. -/
theorem countsFullLaw_fixed_infectious_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (k : ℕ) (A : Set ℕ) :
    Tendsto (fun n => (countsFullLaw (rate n) n).real {H | (H k).infectious ∈ A})
      atTop (nhds ((BiasedWalk.fullLaw (infectionProbability lam 1)).real
        {H | H k ∈ A})) := by
  simp_rw [countsFullLaw_infectious_event_eq_tree, ← planeFullLaw_activeCard_event_eq_walk]
  apply Metric.tendsto_atTop.mpr
  intro e he
  apply eventually_atTop.mp
  filter_upwards [treeFullLaw_plane_events_tendsto rate lam hscaled k he] with n hn
  rw [Real.dist_eq]
  exact hn {s | s.active.card ∈ A}

theorem countsFullLaw_fixed_extinction_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (k : ℕ) :
    Tendsto (fun n => (countsFullLaw (rate n) n).real {H | (H k).infectious = 0})
      atTop (nhds ((BiasedWalk.fullLaw (infectionProbability lam 1)).real
        {H | H k = 0})) := by
  simpa only [Set.mem_singleton_iff] using
    countsFullLaw_fixed_infectious_tendsto rate lam hscaled k {0}

end Freezing1.SIR
