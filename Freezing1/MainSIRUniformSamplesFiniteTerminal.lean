module

public import Freezing1.MainSIRUniformSamplesFinitePrefix
public import Freezing1.SIRFiniteRateTerminalAverage

/-!
# Complete terminal uniform samples on the finite-rate surviving branch

Terminal capture is integrated with the actual adaptive word law. Earlier
count gates are preserved by exact word projectivity, and the uniform
sample restriction retains all vertices and conditional independent pairs.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory RandomEnvironment
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem preFluid_horizon_le_terminal {lam t : ℝ} (hlam : 1 < lam)
    (htt : t < fluidExtinctionTime lam) (n : ℕ) : ⌊t * (n : ℝ)⌋₊ ≤ 2 * n + 1 := by
  have ht2 : t ≤ 2 := (htt.trans (fluidExtinctionTime_spec hlam).2.1).le
  apply Nat.floor_le_of_le
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem longer_word_sublinear_gate_prefix_height_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (nhds 0))
    {t eps : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam) (heps : 0 < eps) :
    Tendsto (fun n => ∫⁻ w, if 0 < (wordCountsAt n w (cutoff n)).infectious then
      Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) ⌊t * (n : ℝ)⌋₊
        {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - (lam : ℝ) / ((lam : ℝ) - 1)|}
      else 0 ∂signWordLaw (rate n) n (2 * n + 1)) atTop (nhds 0) := by
  apply (sir_sublinear_gate_prefix_uniform_height_tendsto rate lam hlam hrate
    cutoff hcutoff hsmall ht htt heps).congr'
  filter_upwards [sublinear_cutoff_eventually_le_fraction cutoff hsmall ht] with n hn
  rw [lintegral_treeFullLaw_gated_height_word _ _ _ _ hn]
  exact (longer_word_gated_height_projectivity (rate n) n (2 * n + 1) _ (cutoff n)
    (preFluid_horizon_le_terminal hlam htt n) hn _).symm

theorem longer_word_sublinear_gate_prefix_distance_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (nhds 0))
    {t eps : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam) (heps : 0 < eps) :
    Tendsto (fun n => ∫⁻ w, if 0 < (wordCountsAt n w (cutoff n)).infectious then
      CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) ⌊t * (n : ℝ)⌋₊
        {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2 * (lam : ℝ) / ((lam : ℝ) - 1)|}
      else 0 ∂signWordLaw (rate n) n (2 * n + 1)) atTop (nhds 0) := by
  apply (sir_sublinear_gate_prefix_uniform_distance_tendsto rate lam hlam hrate
    cutoff hcutoff hsmall ht htt heps).congr'
  filter_upwards [sublinear_cutoff_eventually_le_fraction cutoff hsmall ht] with n hn
  rw [lintegral_treeFullLaw_gated_pair_word _ _ _ _ hn]
  exact (longer_word_gated_pair_projectivity (rate n) n (2 * n + 1) _ (cutoff n)
    (preFluid_horizon_le_terminal hlam htt n) hn _).symm

theorem sir_sublinear_gate_terminal_uniform_height_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (nhds 0))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => ∫⁻ H, if 0 < (H (cutoff n)).counts.infectious then
      PlaneForward.vertexHeightKernel (H (2 * n + 1)).tree
        {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - (lam : ℝ) / ((lam : ℝ) - 1)|}
      else 0 ∂treeFullLaw (rate n) n) atTop (nhds 0) := by
  let A : ℕ → Set ℕ := fun n => {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - (lam : ℝ) / ((lam : ℝ) - 1)|}
  have hh := finiteRate_terminal_average_tendsto_zero rate hlam hrate
    (fun n w => if 0 < (wordCountsAt n w (cutoff n)).infectious then
      Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1) (A n) else 0)
    (fun t n w => if 0 < (wordCountsAt n w (cutoff n)).infectious then
      Forward.uniformHeightLaw (ForwardAnnealed.wordSchedule w) ⌊t * (n : ℝ)⌋₊ (A n) else 0)
    (fun n w => by split_ifs; exact prob_le_one; exact bot_le)
    (fun t ht htt => longer_word_sublinear_gate_prefix_height_tendsto rate lam hlam hrate
      cutoff hcutoff hsmall ht htt heps)
    (fun n t ht htt w hw eta heta hrelative => by
      have hbound := (word_uniform_samples_relative_bound n w hw
        (preFluid_horizon_le_terminal hlam htt n) heta.le hrelative (A n) ∅).1
      split_ifs
      · exact hbound
      · exact bot_le)
  apply hh.congr'
  filter_upwards [sublinear_cutoff_eventually_le cutoff hsmall] with n hn
  symm
  exact lintegral_treeFullLaw_gated_height_word (rate n) n (2 * n + 1) (cutoff n)
    (by omega) (A n)

theorem sir_sublinear_gate_terminal_uniform_distance_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 1 < (lam : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (nhds 0))
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => ∫⁻ H, if 0 < (H (cutoff n)).counts.infectious then
      PlaneForward.pairDataKernel (H (2 * n + 1)).tree
        {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2 * (lam : ℝ) / ((lam : ℝ) - 1)|}
      else 0 ∂treeFullLaw (rate n) n) atTop (nhds 0) := by
  let A : ℕ → Set (ℕ × ℕ × ℕ) := fun n =>
    {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - 2 * (lam : ℝ) / ((lam : ℝ) - 1)|}
  have hbound (n : ℕ) (w : Fin (2 * n + 1) → Bool) :
      (if 0 < (wordCountsAt n w (cutoff n)).infectious then
        CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1) (A n) else 0) ≤ 1 := by
    have := original_pair_probability (ForwardAnnealed.wordSchedule w) (2 * n + 1)
    split_ifs
    · exact prob_le_one
    · exact bot_le
  have hh := finiteRate_terminal_average_tendsto_zero rate hlam hrate
    (fun n w => if 0 < (wordCountsAt n w (cutoff n)).infectious then
      CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1) (A n) else 0)
    (fun t n w => if 0 < (wordCountsAt n w (cutoff n)).infectious then
      CanonicalTree.forwardPairDataLaw (ForwardAnnealed.wordSchedule w) ⌊t * (n : ℝ)⌋₊ (A n) else 0)
    hbound
    (fun t ht htt => longer_word_sublinear_gate_prefix_distance_tendsto rate lam hlam hrate
      cutoff hcutoff hsmall ht htt heps)
    (fun n t ht htt w hw eta heta hrelative => by
      have hb := (word_uniform_samples_relative_bound n w hw
        (preFluid_horizon_le_terminal hlam htt n) heta.le hrelative ∅ (A n)).2
      split_ifs
      · exact hb
      · exact bot_le)
  apply hh.congr'
  filter_upwards [sublinear_cutoff_eventually_le cutoff hsmall] with n hn
  symm
  exact lintegral_treeFullLaw_gated_pair_word (rate n) n (2 * n + 1) (cutoff n)
    (by omega) (A n)

end Freezing1.SIR
