module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Tactic

/-! Rational derivative polynomials for the tangent function. -/

@[expose] public section

namespace Freezing1.BinaryBijection

open Polynomial Filter
open scoped Topology

noncomputable def tangentDerivativePolynomial : ℕ → Polynomial ℚ
  | 0 => X
  | n + 1 => (1 + X ^ 2) * (tangentDerivativePolynomial n).derivative

@[simp] theorem tangentDerivativePolynomial_zero : tangentDerivativePolynomial 0 = X := rfl

@[simp] theorem tangentDerivativePolynomial_succ (n : ℕ) :
    tangentDerivativePolynomial (n + 1) =
      (1 + X ^ 2) * (tangentDerivativePolynomial n).derivative := rfl

theorem hasDerivAt_tan_polynomial {x : ℝ} (hx : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (1 + Real.tan x ^ 2) x := by
  convert Real.hasDerivAt_tan hx using 1
  have hh := Real.sin_sq_add_cos_sq x
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith

theorem tangentDerivativePolynomial_realization (n : ℕ) {x : ℝ} (hx : Real.cos x ≠ 0) :
    (aeval (Real.tan x) (tangentDerivativePolynomial n) : ℝ) = iteratedDeriv n Real.tan x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have he : (fun y : ℝ => aeval (Real.tan y) (tangentDerivativePolynomial n)) =ᶠ[𝓝 x]
        iteratedDeriv n Real.tan := by
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne hx] with y hy
      exact ih hy
    have hd := ((tangentDerivativePolynomial n).hasDerivAt_aeval (Real.tan x)).comp x
      (hasDerivAt_tan_polynomial hx)
    rw [tangentDerivativePolynomial_succ, map_mul, map_add, map_one, map_pow, aeval_X,
      iteratedDeriv_succ, ← he.deriv_eq]
    exact (by simpa only [Function.comp_def, mul_comm] using hd.deriv.symm)

theorem tangentDerivativePolynomial_constant (n : ℕ) :
    ((tangentDerivativePolynomial n).coeff 0 : ℝ) = iteratedDeriv n Real.tan 0 := by
  have hh := tangentDerivativePolynomial_realization n (x := 0) (by simp)
  rw [Real.tan_zero, ← Polynomial.coeff_zero_eq_aeval_zero'] at hh
  exact hh

end Freezing1.BinaryBijection
