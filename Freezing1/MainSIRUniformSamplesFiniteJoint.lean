module

public import Freezing1.MainSIRUniformSamplesFiniteTerminal
public import Freezing1.SIRJointSampleConcentration
public import Freezing1.SIREarlyTerminalSampling

/-!
# Joint terminal height and distance concentration in the finite regime

The Boolean coordinate is the actual common early-survival event. The
real coordinate is obtained by conditionally uniform sampling of all
terminal vertices, with independent sampling in the distance law.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory RandomEnvironment
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem sir_terminal_joint_height_concentrates (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (sirTerminalJointHeightLaw (rate n) n : Measure (Bool × ℝ))
      {z | eps ≤ |z.2 - TwoPointMixture.gatedValue ((lam : ℝ) / ((lam : ℝ) - 1)) z|})
      atTop (nhds 0) := by
  have hsmall := tendsto_natCutoff_div_nat_zero_of_sublog logLogStartupCutoff_sublog
  have hcut : ∀ᶠ n : ℕ in atTop, logLogStartupCutoff n ≤ 2 * n + 1 := by
    filter_upwards [sublinear_cutoff_eventually_le logLogStartupCutoff hsmall] with n hn
    omega
  apply terminalJointSampleLaw_concentrates_of_branches rate logLogStartupCutoff
    PlaneForward.vertexHeightKernel (fun n h => (h : ℝ) / Real.log (n : ℝ))
    ((lam : ℝ) / ((lam : ℝ) - 1))
    (fun n h => div_nonneg (Nat.cast_nonneg h) (Real.log_natCast_nonneg n)) ?_ ?_ heps
  · intro e he
    exact sir_sublinear_gate_terminal_uniform_height_tendsto rate lam hlam hrate
      logLogStartupCutoff logLogStartupCutoff_tendsto hsmall he
  · intro e he
    simpa only [TreeState.counts, Finset.card_eq_zero] using
      treeFullLaw_early_uniform_height_negligible rate logLogStartupCutoff
        logLogStartupCutoff_sublog hcut he

theorem sir_terminal_joint_distance_concentrates (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (sirTerminalJointDistanceLaw (rate n) n : Measure (Bool × ℝ))
      {z | eps ≤ |z.2 - TwoPointMixture.gatedValue (2 * (lam : ℝ) / ((lam : ℝ) - 1)) z|})
      atTop (nhds 0) := by
  have hsmall := tendsto_natCutoff_div_nat_zero_of_sublog logLogStartupCutoff_sublog
  have hcut : ∀ᶠ n : ℕ in atTop, logLogStartupCutoff n ≤ 2 * n + 1 := by
    filter_upwards [sublinear_cutoff_eventually_le logLogStartupCutoff hsmall] with n hn
    omega
  apply terminalJointSampleLaw_concentrates_of_branches rate logLogStartupCutoff
    PlaneForward.pairDataKernel (fun n z => (z.2.2 : ℝ) / Real.log (n : ℝ))
    (2 * (lam : ℝ) / ((lam : ℝ) - 1))
    (fun n z => div_nonneg (Nat.cast_nonneg z.2.2) (Real.log_natCast_nonneg n)) ?_ ?_ heps
  · intro e he
    exact sir_sublinear_gate_terminal_uniform_distance_tendsto rate lam hlam hrate
      logLogStartupCutoff logLogStartupCutoff_tendsto hsmall he
  · intro e he
    simpa only [TreeState.counts, Finset.card_eq_zero] using
      treeFullLaw_early_uniform_distance_negligible rate logLogStartupCutoff
        logLogStartupCutoff_sublog hcut he

theorem sir_terminal_joint_height_real_concentrates (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (sirTerminalJointHeightLaw (rate n) n : Measure (Bool × ℝ)).real
      {z | eps ≤ |z.2 - TwoPointMixture.gatedValue ((lam : ℝ) / ((lam : ℝ) - 1)) z|})
      atTop (nhds 0) :=
  (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mpr
    (sir_terminal_joint_height_concentrates rate lam hlam hrate heps)

theorem sir_terminal_joint_distance_real_concentrates (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (sirTerminalJointDistanceLaw (rate n) n : Measure (Bool × ℝ)).real
      {z | eps ≤ |z.2 - TwoPointMixture.gatedValue (2 * (lam : ℝ) / ((lam : ℝ) - 1)) z|})
      atTop (nhds 0) :=
  (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mpr
    (sir_terminal_joint_distance_concentrates rate lam hlam hrate heps)

theorem sir_terminal_joint_height_gate_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ))) :
    Tendsto (fun n => (sirTerminalJointHeightLaw (rate n) n : Measure (Bool × ℝ)).real
      {z | z.1 = true}) atTop (nhds (1 - 1 / (lam : ℝ))) := by
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (countsFullLaw_sublinear_extinction_tendsto rate lam hlam hrate logLogStartupCutoff
      logLogStartupCutoff_tendsto (tendsto_natCutoff_div_nat_zero_of_sublog logLogStartupCutoff_sublog))
  have hs : Tendsto (fun n => (countsFullLaw (rate n) n).real
      {C | 0 < (C (logLogStartupCutoff n)).infectious}) atTop (nhds (1 - 1 / (lam : ℝ))) := by
    simpa only [countsFullLaw_survival_probability_eq_one_sub] using hh
  simpa only [sirTerminalJointHeightLaw, Measure.real, terminalJointSampleLaw_gate] using hs

theorem sir_terminal_joint_distance_gate_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ))) :
    Tendsto (fun n => (sirTerminalJointDistanceLaw (rate n) n : Measure (Bool × ℝ)).real
      {z | z.1 = true}) atTop (nhds (1 - 1 / (lam : ℝ))) := by
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (countsFullLaw_sublinear_extinction_tendsto rate lam hlam hrate logLogStartupCutoff
      logLogStartupCutoff_tendsto (tendsto_natCutoff_div_nat_zero_of_sublog logLogStartupCutoff_sublog))
  have hs : Tendsto (fun n => (countsFullLaw (rate n) n).real
      {C | 0 < (C (logLogStartupCutoff n)).infectious}) atTop (nhds (1 - 1 / (lam : ℝ))) := by
    simpa only [countsFullLaw_survival_probability_eq_one_sub] using hh
  simpa only [sirTerminalJointDistanceLaw, Measure.real, terminalJointSampleLaw_gate] using hs

end Freezing1.SIR
