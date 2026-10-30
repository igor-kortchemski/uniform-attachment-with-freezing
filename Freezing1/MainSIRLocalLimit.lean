module

public import Freezing1.SIRTreeWordMixture
public import Freezing1.SIRFrozenBalls
public import Freezing1.PlaneFrozenLimit
public import Freezing1.PlaneTreeCylinders
public import Freezing1.MainGeometricLimit

/-!
# Local limit of the actual embedded finite-population SIR tree

Uniform finite-prefix comparison and persistence of frozen finite balls
transfer the real terminal tree, at the proved horizon 2n+1, to the annealed
limit. The continuous-time exponential/Poisson construction is a separate
source-identification obligation; it is not assumed in this theorem.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem embeddedTerminalTreeLaw_cylinder_real (rate : ℝ≥0) (n h : ℕ) (B : PlaneTree.Ball) :
    (embeddedTerminalTreeLaw rate n : Measure PlaneTree.Tree).real (PlaneTree.cylinder h B) =
      (treeFullLaw rate n).real {H |
        PlaneTree.ball (PlaneForward.shape (H (2 * n + 1)).tree) h = B} := by
  change ((treeFullLaw rate n).map
    (fun H : ℕ → TreeState => PlaneForward.shape (H (2 * n + 1)).tree)).real _ = _
  have hm : Measurable (fun H : ℕ → TreeState => PlaneForward.shape (H (2*n+1)).tree) :=
    (measurable_of_countable (fun z : TreeState => PlaneForward.shape z.tree)).comp
      (measurable_pi_apply (2*n+1))
  rw [measureReal_def, Measure.map_apply hm (PlaneTree.cylinder_isClopen h B).isOpen.measurableSet]
  rfl

theorem treeFullLaw_eval_tree_real (rate : ℝ≥0) (n k : ℕ) (A : Set PlaneForward.State) :
    ((treeFullLaw rate n).map (fun H => (H k).tree)).real A =
      (treeFullLaw rate n).real {H | (H k).tree ∈ A} := by
  have hm : Measurable (fun H : ℕ → TreeState => (H k).tree) :=
    (measurable_of_countable TreeState.tree).comp (measurable_pi_apply k)
  rw [measureReal_def, Measure.map_apply hm (Set.to_countable A).measurableSet]
  rfl

theorem planeFullLaw_eval_real (p : unitInterval) (k : ℕ) (A : Set PlaneForward.State) :
    ((PlaneForward.fullLaw p PlaneForward.initial).map (fun H => H k)).real A =
      (PlaneForward.fullLaw p PlaneForward.initial).real {H | H k ∈ A} := by
  rw [measureReal_def, Measure.map_apply
    (measurable_pi_apply k : Measurable (fun H : ℕ → PlaneForward.State => H k))
    (Set.to_countable A).measurableSet]
  rfl

theorem planeProbabilityLaw_cylinder_real (p : unitInterval) (k h : ℕ) (B : PlaneTree.Ball) :
    (ForwardAnnealed.planeProbabilityLaw p k : Measure PlaneTree.Tree).real
      (PlaneTree.cylinder h B) =
      (PlaneForward.fullLaw p PlaneForward.initial).real
        {H | PlaneTree.ball (PlaneForward.shape (H k)) h = B} := by
  have hm : Measurable (fun H : ℕ → PlaneForward.State => PlaneForward.shape (H k)) :=
    (measurable_of_countable PlaneForward.shape).comp (measurable_pi_apply k)
  rw [ForwardAnnealed.planeProbabilityLaw_eq_chainShape, measureReal_def,
    Measure.map_apply hm
      (PlaneTree.cylinder_isClopen h B).isOpen.measurableSet]
  rfl

theorem terminal_cylinder_error_le (rate : ℝ≥0) (n k h : ℕ) (hk : k ≤ n)
    (p : unitInterval) (B : PlaneTree.Ball) (b : ℝ) :
    |(embeddedTerminalTreeLaw rate n : Measure PlaneTree.Tree).real (PlaneTree.cylinder h B) - b| ≤
      (PlaneForward.fullLaw p PlaneForward.initial).real
        {H | ¬PlaneForward.FrozenBall (H k) h} + 2 * signWordError rate n p k +
      |(PlaneForward.fullLaw p PlaneForward.initial).real
        {H | PlaneTree.ball (PlaneForward.shape (H k)) h = B} - b| := by
  have hterminal := terminal_ball_event_difference_le rate n k h (by omega) {B}
  simp only [Set.mem_singleton_iff] at hterminal
  have hprefix := treeFullLaw_plane_event_error_le rate n k hk p
    {s | PlaneTree.ball (PlaneForward.shape s) h = B}
  have hfrozen := treeFullLaw_plane_event_error_le rate n k hk p
    {s | ¬PlaneForward.FrozenBall s h}
  rw [treeFullLaw_eval_tree_real, planeFullLaw_eval_real] at hprefix hfrozen
  simp only [Set.mem_setOf_eq] at hprefix hfrozen
  rw [embeddedTerminalTreeLaw_cylinder_real]
  have ht1 := abs_sub_le
    ((treeFullLaw rate n).real {H |
      PlaneTree.ball (PlaneForward.shape (H (2*n+1)).tree) h = B})
    ((treeFullLaw rate n).real {H | PlaneTree.ball (PlaneForward.shape (H k).tree) h = B}) b
  have ht2 := abs_sub_le
    ((treeFullLaw rate n).real {H | PlaneTree.ball (PlaneForward.shape (H k).tree) h = B})
    ((PlaneForward.fullLaw p PlaneForward.initial).real
      {H | PlaneTree.ball (PlaneForward.shape (H k)) h = B}) b
  have hn := (abs_le.mp hfrozen).2
  linarith

/-- The terminal horizon diverges, and fixed frozen prefixes suffice even
on paths that became absorbed much earlier. No survival premise is used. -/
theorem tendsto_embeddedTerminalTreeLaw (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ))) :
    Tendsto (fun n => embeddedTerminalTreeLaw (rate n) n) atTop
      (𝓝 (ForwardAnnealed.planeLimitLaw (infectionProbability lam 1))) := by
  let p := infectionProbability lam 1
  have hp : (p : ℝ) < 1 := infectionProbability_lt_one lam 1
  apply PlaneTree.tendsto_probabilityMeasure_of_cylinders
  intro h B
  have hprefix := NNReal.tendsto_coe.mpr
    (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
      (ForwardAnnealed.tendsto_planeProbabilityLaw p hp) (PlaneTree.cylinder_isClopen h B))
  simp only [← ProbabilityMeasure.measureReal_eq_coe_coeFn,
    planeProbabilityLaw_cylinder_real] at hprefix
  apply NNReal.tendsto_coe.mp
  simp only [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hquarter : 0 < ε / 4 := by positivity
  have hprefixError := (hprefix.sub (tendsto_const_nhds
    (x := (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree).real
      (PlaneTree.cylinder h B)))).abs
  simp only [sub_self, abs_zero] at hprefixError
  have hgoodPrefix := hprefixError.eventually (Iio_mem_nhds hquarter)
  have hgoodFrozen := (PlaneForward.fullLaw_not_frozenBall_tendsto_zero p hp h).eventually
    (Iio_mem_nhds hquarter)
  obtain ⟨k, hpk, hfk⟩ := (hgoodPrefix.and hgoodFrozen).exists
  have hword := (signWordError_tendsto_zero rate lam hrate k).eventually
    (Iio_mem_nhds hquarter)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hword.and (eventually_ge_atTop k))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hwn, hkn⟩ := hN n hn
  have hb := terminal_cylinder_error_le (rate n) n k h hkn p B
    ((ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree).real (PlaneTree.cylinder h B))
  simp only [Real.dist_eq]
  change |(embeddedTerminalTreeLaw (rate n) n : Measure PlaneTree.Tree).real
    (PlaneTree.cylinder h B) -
    (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree).real (PlaneTree.cylinder h B)| < ε
  linarith

noncomputable def geometricProbabilityLaw (p : unitInterval) : ProbabilityMeasure PlaneTree.Tree :=
  ⟨PlaneTree.geometricBienaymeLaw p, inferInstance⟩

/-- The geometric local limit for the constructed embedded SIR infection
tree, with the literal asymptotic-rate hypothesis and finite extinction. -/
theorem embedded_sir_geometric_local_limit (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ))) :
    Tendsto (fun n => embeddedTerminalTreeLaw (rate n) n) atTop
      (𝓝 (geometricProbabilityLaw (infectionProbability lam 1))) := by
  have he : ForwardAnnealed.planeLimitLaw (infectionProbability lam 1) =
      geometricProbabilityLaw (infectionProbability lam 1) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact ForwardAnnealed.planeLimitLaw_eq_geometricBienaymeLaw _
      (infectionProbability_lt_one lam 1)
  rw [← he]
  exact tendsto_embeddedTerminalTreeLaw rate lam hrate

end Freezing1.SIR
