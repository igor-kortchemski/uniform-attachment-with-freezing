module

public import Freezing1.TangentFormalSeries
public import Mathlib.Algebra.Polynomial.Derivation

/-! Derivative polynomials recover the coefficients of the formal tangent. -/

@[expose] public section

namespace Freezing1.BinaryBijection

open Polynomial PowerSeries

set_option backward.isDefEq.respectTransparency false

noncomputable def tangentPolynomialSeries (n : ℕ) : PowerSeries ℂ :=
  aeval tangentFormalSeries ((tangentDerivativePolynomial n).map (algebraMap ℚ ℂ))

theorem tangentPolynomialSeries_derivative (n : ℕ) :
    PowerSeries.derivative (tangentPolynomialSeries n) = tangentPolynomialSeries (n + 1) := by
  rw [tangentPolynomialSeries, Derivation.comp_aeval_eq, smul_eq_mul,
    tangentFormalSeries_riccati]
  simp only [tangentPolynomialSeries, tangentDerivativePolynomial_succ,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.map_one, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.derivative_map, map_mul, map_add, map_one,
    map_pow, Polynomial.aeval_X]
  ring

theorem tangentFormalSeries_iterate_derivative (n : ℕ) :
    (PowerSeries.derivative : PowerSeries ℂ → PowerSeries ℂ)^[n] tangentFormalSeries =
      tangentPolynomialSeries n := by
  induction n with
  | zero => simp [tangentPolynomialSeries]
  | succ n ih => rw [Function.iterate_succ_apply', ih, tangentPolynomialSeries_derivative]

theorem tangentPolynomialSeries_constant (n : ℕ) :
    PowerSeries.constantCoeff (tangentPolynomialSeries n) =
      ((tangentDerivativePolynomial n).coeff 0 : ℂ) := by
  rw [tangentPolynomialSeries]
  have hh := Polynomial.map_aeval_eq_aeval_map
    (R := ℂ) (S := PowerSeries ℂ) (T := ℂ) (U := ℂ)
    (φ := RingHom.id ℂ) (ψ := PowerSeries.constantCoeff)
    (by ext z; simp) ((tangentDerivativePolynomial n).map (algebraMap ℚ ℂ)) tangentFormalSeries
  rw [tangentFormalSeries_constant, ← Polynomial.coeff_zero_eq_aeval_zero'] at hh
  simp only [Polynomial.map_id, Polynomial.coeff_map, Algebra.algebraMap_self, RingHom.id_apply] at hh
  convert hh using 1
  exact (map_ratCast (algebraMap ℚ ℂ) ((tangentDerivativePolynomial n).coeff 0)).symm

theorem tangentFormalSeries_coefficient (n : ℕ) :
    (n.factorial : ℂ) * PowerSeries.coeff n tangentFormalSeries =
      ((tangentDerivativePolynomial n).coeff 0 : ℂ) := by
  rw [← PowerSeries.constantCoeff_iterate_derivative,
    tangentFormalSeries_iterate_derivative, tangentPolynomialSeries_constant]

end Freezing1.BinaryBijection
