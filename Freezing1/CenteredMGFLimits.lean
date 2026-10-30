module

public import Freezing1.MaximumMGFLimits

/-!
# Exponential moment upgrade around an arbitrary deterministic limit

This is the varying-measure version needed when height is divided by `log n`
and the limiting constant is the positive linear-regime slope factor.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

/-- Uniform normalized exponential moments and convergence in probability
imply every finite real `Lp` limit, with an arbitrary fixed center. -/
theorem centered_tendsto_Lp_of_eventual_exp_bound
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    {ν : ∀ n, Measure (Ξ n)} [∀ n, IsProbabilityMeasure (ν n)]
    {Z : ∀ n, Ξ n → ℝ} {a : ℕ → ℝ} {B center : ℝ}
    (hZ : ∀ n, Measurable (Z n))
    (h_int : ∀ n θ, Integrable (fun ω ↦ Real.exp (θ * Z n ω)) (ν n))
    (h_nonneg : ∀ n, ∀ᵐ ω ∂ν n, 0 ≤ Z n ω)
    (h_exp : ∀ᶠ n in atTop, mgf (Z n) (ν n) 1 ≤ Real.exp (B * a n))
    (ha : Tendsto a atTop atTop)
    (h_tail : ∀ ε > 0, Tendsto (fun n ↦ ν n {ω | ε ≤ |Z n ω / a n - center|})
      atTop (𝓝 0)) {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n ↦ eLpNorm (fun ω ↦ Z n ω / a n - center)
      (ENNReal.ofReal r) (ν n)) atTop (𝓝 0) := by
  let K : ℝ≥0∞ := ENNReal.ofReal (((r + 1) ^ (r + 1) *
    (Real.exp B + 1)) ^ (r + 1)⁻¹)
  have hq : 0 < r + 1 := by linarith
  apply tendsto_eLpNorm_of_tail_and_higher_moment (fun n ↦ by fun_prop)
    hr (lt_add_one r) (C := K + ENNReal.ofReal |center|) (by finiteness)
  · filter_upwards [ha.eventually_ge_atTop 1, h_exp] with n hn hexp
    have hconst : eLpNorm (fun _ : Ξ n ↦ center) (ENNReal.ofReal (r + 1)) (ν n) =
        ENNReal.ofReal |center| := by
      rw [eLpNorm_const' _ (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top]
      simp [Real.enorm_eq_ofReal_abs]
    calc
      _ ≤ eLpNorm (fun ω ↦ Z n ω / a n) (ENNReal.ofReal (r + 1)) (ν n) +
          eLpNorm (fun _ : Ξ n ↦ center) (ENNReal.ofReal (r + 1)) (ν n) :=
        eLpNorm_sub_le (by simpa using ENNReal.ofReal_le_ofReal (show 1 ≤ r + 1 by linarith))
      _ ≤ K + ENNReal.ofReal |center| := by
        rw [hconst]
        exact add_le_add (normalized_eLpNorm_le_of_exp_bound
          (hZ n) (h_int n) (h_nonneg n) hn hexp hq) le_rfl
  · intro ε hε
    simpa only [Real.norm_eq_abs] using h_tail ε hε

end Freezing1
