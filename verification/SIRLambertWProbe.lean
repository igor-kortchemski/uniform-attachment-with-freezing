module

public import Freezing1.SIRLambertW

/-! Independent exact-value and domain probes for the SIR Lambert formula. -/

@[expose] public section

namespace Freezing1.SIRLambertWProbe

open Freezing1.SIR

theorem principal_endpoint : principalLambertW (-Real.exp (-1)) = -1 :=
  principalLambertW_left_endpoint

theorem principal_positive_point : principalLambertW (Real.exp 1) = 1 := by
  apply principalLambertW_eq_of_characterization (by norm_num)
  simp [lambertMap]

theorem principal_negative_point :
    principalLambertW ((-1 / 2 : ℝ) * Real.exp (-1 / 2)) = -1 / 2 := by
  apply principalLambertW_eq_of_characterization (by norm_num)
  rfl

theorem derivative_at_zero : deriv principalLambertW 0 = 1 :=
  principalLambertW_hasDerivAt_zero.deriv

/-- The printed quotient must exclude zero: Lean's totalized quotient is
zero there, whereas the actual derivative is one. -/
theorem printed_quotient_fails_at_zero :
    deriv principalLambertW 0 ≠
      principalLambertW 0 / (0 * (1 + principalLambertW 0)) := by
  rw [derivative_at_zero]
  norm_num

theorem profile_lambert_argument_positive {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    0 < lam * Real.exp lam * Real.exp (-lam * t) :=
  mul_pos (mul_pos hlam (Real.exp_pos _)) (Real.exp_pos _)

theorem profile_formula_initial_value {lam : ℝ} (hlam : 0 < lam) :
    (1 / lam) * principalLambertW (lam * Real.exp lam * Real.exp (-lam * 0)) = 1 := by
  rw [← fluidProfile_lambertW hlam 0, fluidProfile_zero hlam]

theorem profile_formula_negative_time {lam : ℝ} (hlam : 0 < lam) :
    fluidProfile lam (-1) =
      (1 / lam) * principalLambertW (lam * Real.exp lam * Real.exp (-lam * (-1))) :=
  fluidProfile_lambertW hlam (-1)

end Freezing1.SIRLambertWProbe
