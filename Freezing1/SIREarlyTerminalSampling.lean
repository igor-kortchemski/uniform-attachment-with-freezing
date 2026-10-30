module

public import Freezing1.SIREarlyTerminalHeight
public import Freezing1.PlaneSamplingBounds

/-!
# Small-epidemic contribution to terminal uniform-sampling laws

These are unnormalized probabilities on the actual early-extinction event.
The two samples in the distance kernel remain independent conditional on
the same terminal tree. No survival conditioning is introduced.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

theorem treeFullLaw_early_uniform_height_negligible (rate : ℕ → ℝ≥0)
    (cutoff : ℕ → ℕ)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0))
    (hcut : ∀ᶠ n : ℕ in atTop, cutoff n ≤ 2 * n + 1)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => ∫⁻ H, if (H (cutoff n)).tree.active = ∅ then
      PlaneForward.vertexHeightKernel (H (2 * n + 1)).tree
        {h | eps ≤ (h : ℝ) / Real.log (n : ℝ)} else 0
      ∂treeFullLaw (rate n) n) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hsmall.eventually (eventually_lt_nhds heps), hcut,
    eventually_ge_atTop 2] with n hn hcn hn2
  symm
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [treeFullLaw_early_terminal_height_bound (rate n) n (cutoff n) hcn]
    with H hb
  split_ifs with he
  · have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    apply PlaneForward.vertexHeightKernel_upper_tail_eq_zero _ hl
    have hh : (((H (2 * n + 1)).tree.vertices.sup List.length : ℕ) : ℝ) ≤ cutoff n := by
      exact_mod_cast hb he
    exact (div_le_div_of_nonneg_right hh hl.le).trans_lt hn
  · rfl

theorem treeFullLaw_early_uniform_distance_negligible (rate : ℕ → ℝ≥0)
    (cutoff : ℕ → ℕ)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0))
    (hcut : ∀ᶠ n : ℕ in atTop, cutoff n ≤ 2 * n + 1)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ => ∫⁻ H, if (H (cutoff n)).tree.active = ∅ then
      PlaneForward.pairDataKernel (H (2 * n + 1)).tree
        {z | eps ≤ (z.2.2 : ℝ) / Real.log (n : ℝ)} else 0
      ∂treeFullLaw (rate n) n) atTop (𝓝 0) := by
  have hdouble : Tendsto (fun n : ℕ => 2 * (cutoff n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hsmall.const_mul 2
  apply tendsto_const_nhds.congr'
  filter_upwards [hdouble.eventually (eventually_lt_nhds heps), hcut,
    eventually_ge_atTop 2] with n hn hcn hn2
  symm
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [treeFullLaw_early_terminal_height_bound (rate n) n (cutoff n) hcn,
    treeFullLaw_valid (rate n) n] with H hb hv
  split_ifs with he
  · have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    apply (hv (2 * n + 1)).1.pairDataKernel_distance_upper_tail_eq_zero hl
    have hh : (((H (2 * n + 1)).tree.vertices.sup List.length : ℕ) : ℝ) ≤ cutoff n := by
      exact_mod_cast hb he
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num)) hl.le).trans_lt hn
  · rfl

end Freezing1.SIR
