module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

/-!
# Numerical obstruction to the printed SIR stochastic Grönwall criterion

At source lines 2162--2176, the proposed drift bound uses the maximum over
the entire time horizon, rather than the maximum up to the current step.
The deterministic family Xⁿₖ = k, with horizon t=1 and constant C=1, satisfies
the printed numerical bounds, starts at zero, but its normalized maximum is
one. Thus adding an initial-value assumption alone cannot repair that bound.

This file checks the deterministic specialization explicitly; it makes no
unproved assertion about conditional expectations or a probability model.
-/

@[expose] public section

namespace Freezing1.SIRSourceChecks

open Filter
open scoped Topology

def linearFluctuation (_n k : ℕ) : ℝ := k

def horizonMaximum (n : ℕ) : ℕ := (Finset.range (n + 1)).sup id

theorem horizonMaximum_eq (n : ℕ) : horizonMaximum n = n := by
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  · exact Finset.le_sup (f := id) (Finset.mem_range.mpr (Nat.lt_succ_self n))

theorem linearFluctuation_initial (n : ℕ) : linearFluctuation n 0 = 0 := by
  simp [linearFluctuation]

theorem linearFluctuation_increment (n k : ℕ) :
    linearFluctuation n (k + 1) - linearFluctuation n k = 1 := by
  simp only [linearFluctuation, Nat.cast_add, Nat.cast_one]
  ring

theorem horizonMaximum_characterization (n : ℕ) :
    (∀ k ≤ n, |linearFluctuation n k| ≤ (horizonMaximum n : ℝ)) ∧
      |linearFluctuation n n| = (horizonMaximum n : ℝ) := by
  rw [horizonMaximum_eq]
  constructor
  · intro k hk
    unfold linearFluctuation
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)]
    exact_mod_cast hk
  · simp [linearFluctuation]

theorem printed_drift_bound (n k : ℕ) (hn : 0 < n) :
    |linearFluctuation n (k + 1) - linearFluctuation n k| ≤
      (1 : ℝ) / n * (1 + (horizonMaximum n : ℝ)) := by
  rw [linearFluctuation_increment, abs_one, horizonMaximum_eq,
    div_mul_eq_mul_div, one_mul]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ hnR).mpr
  linarith

theorem printed_second_moment_bound (n k : ℕ) :
    (linearFluctuation n (k + 1) - linearFluctuation n k) ^ 2 ≤ 1 := by
  rw [linearFluctuation_increment]
  norm_num

noncomputable def normalizedMaximum (n : ℕ) : ℝ := (horizonMaximum n : ℝ) / n

theorem normalizedMaximum_eq_one {n : ℕ} (hn : 0 < n) : normalizedMaximum n = 1 := by
  rw [normalizedMaximum, horizonMaximum_eq]
  exact div_self (by exact_mod_cast (Nat.ne_of_gt hn))

theorem normalizedMaximum_tendsto_one :
    Tendsto normalizedMaximum atTop (𝓝 (1 : ℝ)) := by
  have he : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop] normalizedMaximum := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (normalizedMaximum_eq_one (by omega)).symm
  exact tendsto_const_nhds.congr' he

theorem normalizedMaximum_not_tendsto_zero :
    ¬Tendsto normalizedMaximum atTop (𝓝 (0 : ℝ)) := by
  intro hzero
  have he := tendsto_nhds_unique normalizedMaximum_tendsto_one hzero
  norm_num at he

/-- The deterministic numerical specialization of all printed bounds at
t=1,C=1, together with failure of its claimed normalized conclusion. -/
theorem printed_global_max_criterion_counterexample :
    (∀ n, linearFluctuation n 0 = 0) ∧
      (∀ n : ℕ, 0 < n → ∀ k ≤ n,
        |linearFluctuation n (k + 1) - linearFluctuation n k| ≤
          (1 : ℝ) / n * (1 + (horizonMaximum n : ℝ)) ∧
        (linearFluctuation n (k + 1) - linearFluctuation n k) ^ 2 ≤ 1) ∧
      ¬Tendsto normalizedMaximum atTop (𝓝 (0 : ℝ)) := by
  refine ⟨linearFluctuation_initial, ?_, normalizedMaximum_not_tendsto_zero⟩
  intro n hn k _
  exact ⟨printed_drift_bound n k hn, printed_second_moment_bound n k⟩

end Freezing1.SIRSourceChecks
