module

public import Freezing1.TangentDerivativePolynomial
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.NumberTheory.Bernoulli

/-!
# The formal tangent series from the exponential series

Its differential equation is proved algebraically. The connection with
Bernoulli coefficients is a separate step in the enumeration argument.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open PowerSeries
open scoped PowerSeries

theorem formal_derivative_rescale {R : Type*} [CommRing R] (a : R) (f : PowerSeries R) :
    PowerSeries.derivative (rescale a f) = C a * rescale a (PowerSeries.derivative f) := by
  ext n
  simp only [coeff_derivative, coeff_rescale, coeff_C_mul]
  rw [pow_succ]
  ring

noncomputable def tangentExponential : PowerSeries ℂ := rescale (2 * Complex.I) (PowerSeries.exp ℂ)

noncomputable def tangentDenominatorInverse : PowerSeries ℂ := (tangentExponential + 1)⁻¹

noncomputable def tangentFormalSeries : PowerSeries ℂ :=
  C Complex.I * (2 * tangentDenominatorInverse - 1)

theorem tangentExponential_constant : constantCoeff tangentExponential = 1 := by
  simp [tangentExponential, ← coeff_zero_eq_constantCoeff_apply]

theorem tangentExponential_derivative :
    PowerSeries.derivative tangentExponential = C (2 * Complex.I) * tangentExponential := by
  rw [tangentExponential, formal_derivative_rescale, derivative_exp]

theorem tangentDenominatorInverse_identity :
    (tangentExponential + 1) * tangentDenominatorInverse = 1 := by
  apply PowerSeries.mul_inv_cancel
  simp [tangentExponential_constant]

theorem tangentDenominatorInverse_constant : constantCoeff tangentDenominatorInverse = 1 / 2 := by
  norm_num [tangentDenominatorInverse, tangentExponential_constant]

theorem tangentFormalSeries_constant : constantCoeff tangentFormalSeries = 0 := by
  have htwo : constantCoeff (2 : PowerSeries ℂ) = 2 := by
    rw [show (2 : PowerSeries ℂ) = 1 + 1 by ring, map_add, map_one]
    ring
  rw [tangentFormalSeries, map_mul, constantCoeff_C, map_sub, map_mul, htwo,
    tangentDenominatorInverse_constant, map_one]
  ring

theorem tangentFormalSeries_riccati :
    PowerSeries.derivative tangentFormalSeries = 1 + tangentFormalSeries ^ 2 := by
  have hI : (C Complex.I : PowerSeries ℂ) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hCtwo : (C (2 : ℂ) : PowerSeries ℂ) = 2 := by
    rw [show (2 : ℂ) = 1 + 1 by ring, map_add, map_one]
    ring
  have h2 : C (2 * Complex.I) = (2 : PowerSeries ℂ) * C Complex.I := by
    rw [map_mul, hCtwo]
  have hv := tangentDenominatorInverse_identity
  have hv2 : tangentExponential * tangentDenominatorInverse ^ 2 +
      tangentDenominatorInverse ^ 2 = tangentDenominatorInverse := by
    linear_combination tangentDenominatorInverse * hv
  have hdv : PowerSeries.derivative tangentDenominatorInverse =
      -tangentDenominatorInverse ^ 2 * (2 * C Complex.I * tangentExponential) := by
    rw [tangentDenominatorInverse, derivative_inv', map_add, derivative_one, add_zero,
      tangentExponential_derivative, h2]
  have hd2 : PowerSeries.derivative (2 : PowerSeries ℂ) = 0 := by
    rw [show (2 : PowerSeries ℂ) = 1 + 1 by ring, map_add, derivative_one, add_zero]
  rw [tangentFormalSeries]
  simp only [map_sub, Derivation.leibniz, derivative_C, hd2, derivative_one,
    smul_eq_mul, mul_zero, add_zero, sub_zero, hdv]
  linear_combination -4 * (C Complex.I : PowerSeries ℂ) ^ 2 * hv2 - hI

end Freezing1.BinaryBijection
