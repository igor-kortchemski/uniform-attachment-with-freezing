module

public import Freezing1.ForwardPlaneHistory
public import Freezing1.ForwardPlaneLimit
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The limit on the genuine plane-chain probability space

The exact whole-path transport gives convergence under the plane Markov
law itself. Its almost-everywhere measurable limit has the same law as the
ordered limit of the original annealed forward history.
-/

@[expose] public section

namespace Freezing1.PlaneForward

open Filter MeasureTheory
open scoped Topology Classical

noncomputable def chainLimit (H : ℕ → State) : PlaneTree.Tree :=
  if h : ∃ t : PlaneTree.Tree, Tendsto (fun n => shape (H n)) atTop (𝓝 t)
  then h.choose else PlaneTree.leaf

theorem measurable_shape_eval (n : ℕ) :
    Measurable (fun H : ℕ → State => shape (H n)) :=
  (measurable_of_countable shape).comp (measurable_pi_apply n)

theorem tendsto_chainLimit_of_exists {H : ℕ → State}
    (h : ∃ t : PlaneTree.Tree, Tendsto (fun n => shape (H n)) atTop (𝓝 t)) :
    Tendsto (fun n => shape (H n)) atTop (𝓝 (chainLimit H)) := by
  simp only [chainLimit, dite_eq_left h]
  exact h.choose_spec

theorem fullLaw_exists_limit (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ H ∂fullLaw p initial,
      ∃ t : PlaneTree.Tree, Tendsto (fun n => shape (H n)) atTop (𝓝 t) := by
  rw [← ForwardAnnealed.map_fullLaw_toPlaneState p]
  apply (ae_map_iff ForwardAnnealed.measurable_planeHistory.aemeasurable
    (measurableSet_exists_tendsto measurable_shape_eval)).mpr
  filter_upwards [ForwardAnnealed.fullLaw_tendsto_projectedShape p hp] with H hH
  exact ⟨ForwardAnnealed.planeLimit H, hH⟩

theorem fullLaw_tendsto_chainLimit (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ H ∂fullLaw p initial,
      Tendsto (fun n => shape (H n)) atTop (𝓝 (chainLimit H)) :=
  (fullLaw_exists_limit p hp).mono fun _ h => tendsto_chainLimit_of_exists h

theorem aemeasurable_chainLimit (p : unitInterval) (hp : (p : ℝ) < 1) :
    AEMeasurable chainLimit (fullLaw p initial) :=
  aemeasurable_of_tendsto_metrizable_ae'
    (fun n => (measurable_shape_eval n).aemeasurable) (fullLaw_tendsto_chainLimit p hp)

theorem chainLimit_planeHistory_eq_actual (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ H ∂ForwardAnnealed.fullLaw p,
      chainLimit (ForwardAnnealed.planeHistory H) = ForwardAnnealed.planeLimit H := by
  have hc : ∀ᵐ H ∂ForwardAnnealed.fullLaw p,
      Tendsto (fun n => shape (ForwardAnnealed.planeHistory H n)) atTop
        (𝓝 (chainLimit (ForwardAnnealed.planeHistory H))) := by
    have h := fullLaw_tendsto_chainLimit p hp
    rw [← ForwardAnnealed.map_fullLaw_toPlaneState p] at h
    exact ae_of_ae_map ForwardAnnealed.measurable_planeHistory.aemeasurable h
  filter_upwards [hc, ForwardAnnealed.fullLaw_tendsto_projectedShape p hp] with H hH ha
  exact tendsto_nhds_unique hH ha

theorem map_fullLaw_chainLimit (p : unitInterval) (hp : (p : ℝ) < 1) :
    (fullLaw p initial).map chainLimit =
      (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree) := by
  have hm : AEMeasurable chainLimit
      ((ForwardAnnealed.fullLaw p).map ForwardAnnealed.planeHistory) := by
    rw [ForwardAnnealed.map_fullLaw_toPlaneState p]
    exact aemeasurable_chainLimit p hp
  rw [← ForwardAnnealed.map_fullLaw_toPlaneState p,
    AEMeasurable.map_map_of_aemeasurable hm ForwardAnnealed.measurable_planeHistory.aemeasurable,
    ForwardAnnealed.planeLimitLaw_eq_map p hp]
  apply Measure.map_congr
  exact chainLimit_planeHistory_eq_actual p hp

end Freezing1.PlaneForward
