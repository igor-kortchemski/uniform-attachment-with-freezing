module

public import Freezing1.TangentFormalSeries

/-! The formal exponential identity giving tangent's Bernoulli coefficients. -/

@[expose] public section

namespace Freezing1.BinaryBijection

open PowerSeries

set_option backward.isDefEq.respectTransparency false

noncomputable def rescaledBernoulliSeries (a : ℂ) : PowerSeries ℂ :=
  rescale a (bernoulliPowerSeries ℂ)

theorem rescaledBernoulliSeries_identity (a : ℂ) :
    rescaledBernoulliSeries a * (rescale a (PowerSeries.exp ℂ) - 1) = C a * X := by
  have hh := congrArg (rescale a) (bernoulliPowerSeries_mul_exp_sub_one ℂ)
  simpa only [rescaledBernoulliSeries, map_mul, map_sub, map_one, rescale_X] using hh

theorem tangentExponential_square :
    tangentExponential ^ 2 = rescale (4 * Complex.I) (PowerSeries.exp ℂ) := by
  rw [tangentExponential, pow_two, exp_mul_exp_eq_exp_add]
  rw [show (2 : ℂ) * Complex.I + 2 * Complex.I = 4 * Complex.I by ring]

theorem tangentExponential_sub_one_ne_zero : tangentExponential - 1 ≠ 0 := by
  intro he
  have hh := congrArg (PowerSeries.coeff 1) he
  have hc : PowerSeries.coeff 1 (tangentExponential - 1) = 2 * Complex.I := by
    norm_num [tangentExponential]
  rw [hc, map_zero] at hh
  exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) Complex.I_ne_zero) hh

theorem bernoulliSeries_difference :
    rescaledBernoulliSeries (2 * Complex.I) - rescaledBernoulliSeries (4 * Complex.I) =
      C (2 * Complex.I) * X * tangentDenominatorInverse := by
  have h2 := rescaledBernoulliSeries_identity (2 * Complex.I)
  change rescaledBernoulliSeries (2 * Complex.I) * (tangentExponential - 1) =
    C (2 * Complex.I) * X at h2
  have h4 := rescaledBernoulliSeries_identity (4 * Complex.I)
  rw [← tangentExponential_square] at h4
  have hC4 : (C (4 * Complex.I) : PowerSeries ℂ) = 2 * C (2 * Complex.I) := by
    rw [show (4 : ℂ) * Complex.I = 2 * Complex.I + 2 * Complex.I by ring, map_add]
    ring
  rw [hC4] at h4
  have hm : (rescaledBernoulliSeries (2 * Complex.I) -
      rescaledBernoulliSeries (4 * Complex.I)) * (tangentExponential + 1) =
        C (2 * Complex.I) * X := by
    apply mul_right_cancel₀ tangentExponential_sub_one_ne_zero
    linear_combination (tangentExponential + 1) * h2 - h4
  calc
    _ = (rescaledBernoulliSeries (2 * Complex.I) - rescaledBernoulliSeries (4 * Complex.I)) *
        ((tangentExponential + 1) * tangentDenominatorInverse) := by
      rw [tangentDenominatorInverse_identity, mul_one]
    _ = _ := by rw [← mul_assoc, hm]

theorem X_mul_tangentFormalSeries :
    X * tangentFormalSeries = rescaledBernoulliSeries (2 * Complex.I) -
      rescaledBernoulliSeries (4 * Complex.I) - C Complex.I * X := by
  have hC2 : (C (2 * Complex.I) : PowerSeries ℂ) = 2 * C Complex.I := by
    rw [show (2 : ℂ) * Complex.I = Complex.I + Complex.I by ring, map_add]
    ring
  rw [bernoulliSeries_difference, hC2, tangentFormalSeries]
  ring

theorem tangentFormalSeries_coeff_bernoulli (n : ℕ) (hn : 0 < n) :
    PowerSeries.coeff n tangentFormalSeries =
      ((2 * Complex.I) ^ (n + 1) - (4 * Complex.I) ^ (n + 1)) *
        algebraMap ℚ ℂ (bernoulli (n + 1) / (n + 1).factorial) := by
  have hh := congrArg (PowerSeries.coeff (n + 1)) X_mul_tangentFormalSeries
  have hleft : PowerSeries.coeff (n + 1) (X * tangentFormalSeries) =
      PowerSeries.coeff n tangentFormalSeries := by
    rw [mul_comm, ← pow_one (X : PowerSeries ℂ)]
    exact coeff_mul_X_pow tangentFormalSeries 1 n
  have hnx : n + 1 ≠ 1 := by omega
  rw [hleft, map_sub, map_sub, coeff_C_mul, coeff_X, ite_eq_right hnx, mul_zero, sub_zero] at hh
  simp only [rescaledBernoulliSeries, coeff_rescale, bernoulliPowerSeries, coeff_mk] at hh
  rw [hh]
  ring

end Freezing1.BinaryBijection
