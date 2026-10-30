module

public import Freezing1.MainSIRLocalLimit
public import Freezing1.SIRStrongLocalNonTightness

/-!
# The two SIR local conclusions for the genuine embedded model

The rate assumptions are stated in the source's ratio form. Identification
of this embedded tree law with the independently specified continuous-time
Poisson contact process remains a separate, recorded source obligation.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory
open scoped Topology NNReal

theorem scaled_rate_of_source_ratio (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 0 < lam)
    (h : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)) := by
  have hh := h.mul_const (lam : ℝ)
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hl0 : (lam : ℝ) ≠ 0 := by exact_mod_cast hlam.ne'
  field_simp

theorem scaled_rate_atTop_of_source_ratio (rate : ℕ → ℝ≥0)
    (h : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop := by
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem embedded_sir_geometric_local_limit_of_source_ratio (rate : ℕ → ℝ≥0)
    (lam : ℝ≥0) (hlam : 0 < lam)
    (h : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n => embeddedTerminalTreeLaw (rate n) n) atTop
      (𝓝 (geometricProbabilityLaw (infectionProbability lam 1))) :=
  embedded_sir_geometric_local_limit rate lam (scaled_rate_of_source_ratio rate lam hlam h)

theorem embedded_sir_not_tight_of_source_ratio (rate : ℕ → ℝ≥0)
    (h : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop) :
    ¬IsTightMeasureSet (Set.range fun n =>
      (embeddedTerminalTreeLaw (rate n) n : Measure PlaneTree.Tree)) :=
  embeddedTerminalTreeLaw_not_tight rate (scaled_rate_atTop_of_source_ratio rate h)

end Freezing1.SIR
