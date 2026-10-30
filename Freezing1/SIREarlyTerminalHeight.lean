module

public import Freezing1.SIRSublinearExtinction
public import Freezing1.MainSIRUniformHeightStrong

/-!
# Terminal trees of epidemics extinct before a small cutoff

The actual tree is held after extinction. Before event k its height is at
most k, so extinction before a sublogarithmic cutoff makes the entire
terminal tree negligible on the logarithmic height scale.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem treeFullLaw_maximum_le_time (rate : ℝ≥0) (n k : ℕ) :
    ∀ᵐ H ∂treeFullLaw rate n, (H k).tree.vertices.sup List.length ≤ k := by
  have hb : ∀ᵐ s ∂((treeFullLaw rate n).map (fun H => (H k).tree)),
      s.vertices.sup List.length ≤ k := by
    rw [treeFullLaw_plane_original_word_mixture]
    have : IsProbabilityMeasure ((signWordLaw rate n k).bind (fun w =>
        (Forward.treeLaw (ForwardAnnealed.wordSchedule w) k).map
          Forward.State.toPlaneState)) := by
      apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      exact Filter.Eventually.of_forall fun _ =>
        Measure.isProbabilityMeasure_map_iff Forward.measurable_toPlaneState.aemeasurable
          |>.mpr inferInstance
    apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
    rw [Measure.bind_apply (by trivial) (measurable_of_countable _).aemeasurable]
    calc
      _ = ∫⁻ _w, (1 : ℝ≥0∞) ∂signWordLaw rate n k := by
        apply lintegral_congr
        intro w
        apply (ae_iff_prob_eq_one (measurable_of_countable _)).mp
        apply (ae_map_iff Forward.measurable_toPlaneState.aemeasurable (by trivial)).mpr
        filter_upwards [Forward.treeLaw_valid (ForwardAnnealed.wordSchedule w) k] with s hs
        rw [hs.toPlaneState_treeHeight]
        apply Finset.sup_le
        intro v hv
        exact (hs.height_le_id v hv).trans (hs.vertices_le v hv)
      _ = 1 := by simp
  exact (ae_map_iff ((measurable_of_countable TreeState.tree).comp
    (measurable_pi_apply k)).aemeasurable (by trivial)).mp hb

theorem treeFullLaw_absorbed_persists (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂treeFullLaw rate n, ∀ a k : ℕ, a ≤ k →
      (H a).tree.active = ∅ → H k = H a := by
  filter_upwards [treeFullLaw_held rate n] with H hh
  intro a k hak ha
  induction k, hak using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [hh k (by rw [ih]; exact ha), ih]

theorem treeFullLaw_early_terminal_height_bound (rate : ℝ≥0) (n k : ℕ)
    (hk : k ≤ 2 * n + 1) :
    ∀ᵐ H ∂treeFullLaw rate n, (H k).tree.active = ∅ →
      (H (2 * n + 1)).tree.vertices.sup List.length ≤ k := by
  filter_upwards [treeFullLaw_maximum_le_time rate n k,
    treeFullLaw_absorbed_persists rate n] with H hb hh he
  rw [hh k (2 * n + 1) hk he]
  exact hb

theorem treeFullLaw_early_terminal_height_negligible (rate : ℕ → ℝ≥0)
    (cutoff : ℕ → ℕ)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0))
    (hcut : ∀ᶠ n : ℕ in atTop, cutoff n ≤ 2 * n + 1)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => treeFullLaw (rate n) n
      {H | (H (cutoff n)).tree.active = ∅ ∧ eps ≤
        (((H (2 * n + 1)).tree.vertices.sup List.length : ℕ) : ℝ) /
          Real.log (n : ℝ)}) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hsmall.eventually (eventually_lt_nhds heps), hcut,
    eventually_ge_atTop 2] with n hn hcn hn2
  symm
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [treeFullLaw_early_terminal_height_bound (rate n) n (cutoff n) hcn]
    with H hb hbad
  have hh : (((H (2 * n + 1)).tree.vertices.sup List.length : ℕ) : ℝ) ≤ cutoff n := by
    exact_mod_cast hb hbad.1
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have hdiv := div_le_div_of_nonneg_right hh hl.le
  exact (not_lt_of_ge (hbad.2.trans hdiv)) hn

theorem treeFullLaw_extinction_event_eq_counts (rate : ℝ≥0) (n k : ℕ) :
    treeFullLaw rate n {H | (H k).tree.active = ∅} =
      countsFullLaw rate n {H | (H k).infectious = 0} := by
  rw [← map_treeFullLaw_counts]
  rw [Measure.map_apply (by fun_prop) (by measurability)]
  congr 1
  ext H
  simp [TreeState.counts]

theorem treeFullLaw_sublinear_extinction_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (treeFullLaw (rate n) n).real
      {H | (H (cutoff n)).tree.active = ∅}) atTop (𝓝 (1 / (lam : ℝ))) := by
  simpa only [Measure.real, treeFullLaw_extinction_event_eq_counts] using
    countsFullLaw_sublinear_extinction_tendsto rate lam hlam hscaled cutoff hcutoff hsmall

theorem treeFullLaw_logLog_extinction_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ))) :
    Tendsto (fun n : ℕ => (treeFullLaw (rate n) n).real
      {H | (H (logLogStartupCutoff n)).tree.active = ∅})
      atTop (𝓝 (1 / (lam : ℝ))) := by
  exact treeFullLaw_sublinear_extinction_tendsto rate lam hlam hscaled _
    logLogStartupCutoff_tendsto
    (tendsto_natCutoff_div_nat_zero_of_sublog RandomEnvironment.logLogStartupCutoff_sublog)

theorem treeFullLaw_logLog_early_terminal_height_negligible (rate : ℕ → ℝ≥0)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => treeFullLaw (rate n) n
      {H | (H (logLogStartupCutoff n)).tree.active = ∅ ∧ eps ≤
        (((H (2 * n + 1)).tree.vertices.sup List.length : ℕ) : ℝ) /
          Real.log (n : ℝ)}) atTop (𝓝 0) := by
  apply treeFullLaw_early_terminal_height_negligible rate _
    RandomEnvironment.logLogStartupCutoff_sublog _ heps
  filter_upwards [sublinear_cutoff_eventually_le _
    (tendsto_natCutoff_div_nat_zero_of_sublog RandomEnvironment.logLogStartupCutoff_sublog)]
    with n hn
  omega

end Freezing1.SIR
