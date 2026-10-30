module

import Freezing1.TangentEnumeration

open Freezing1.BinaryBijection

namespace TangentEnumerationStatementAudit

example (m : ℕ) (x : ℝ) (hx : Real.cos x ≠ 0) :
    (Polynomial.aeval (Real.tan x) (tangentDerivativePolynomial m) : ℝ) =
      iteratedDeriv m Real.tan x := tangentDerivativePolynomial_realization m hx

example (m : ℕ) :
    ((tangentDerivativePolynomial m).coeff 0 : ℝ) = iteratedDeriv m Real.tan 0 :=
  tangentDerivativePolynomial_constant m

example : PowerSeries.constantCoeff tangentFormalSeries = 0 ∧
    PowerSeries.derivative tangentFormalSeries = 1 + tangentFormalSeries ^ 2 :=
  ⟨tangentFormalSeries_constant, tangentFormalSeries_riccati⟩

example (m : ℕ) :
    (m.factorial : ℂ) * PowerSeries.coeff m tangentFormalSeries =
      ((tangentDerivativePolynomial m).coeff 0 : ℂ) := tangentFormalSeries_coefficient m

example (n : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff (2 * n - 1) tangentFormalSeries =
      ((2 * Complex.I) ^ (2 * n) - (4 * Complex.I) ^ (2 * n)) *
        algebraMap ℚ ℂ (bernoulli (2 * n) / (2 * n).factorial) := by
  have hh := tangentFormalSeries_coeff_bernoulli (2 * n - 1) (by omega : 0 < 2 * n - 1)
  simpa only [show 2 * n - 1 + 1 = 2 * n by omega] using hh

example (n : ℕ) (hn : 1 ≤ n) :
    ((iteratedDeriv (2 * n - 1) Real.tan 0 : ℝ) : ℂ) =
      ((2 * n - 1).factorial : ℂ) *
        ((2 * Complex.I) ^ (2 * n) - (4 * Complex.I) ^ (2 * n)) *
          algebraMap ℚ ℂ (bernoulli (2 * n) / (2 * n).factorial) :=
  tangent_derivative_bernoulli_identity n (by omega)

example (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv (2 * n - 1) Real.tan 0 =
      (4 : ℝ) ^ n * ((4 : ℝ) ^ n - 1) * |(bernoulli (2 * n) : ℝ)| / (2 * n) :=
  tangent_derivative_bernoulli n (by omega)

/-- Literal C01: actual unordered class, positive source size, both equalities. -/
example (n : ℕ) (hn : 1 ≤ n) :
    (Nat.card (UnorderedIncreasingClass 0 n (Finset.Icc 1 (2 * n - 1))) : ℝ) =
        (4 : ℝ) ^ n * ((4 : ℝ) ^ n - 1) * |(bernoulli (2 * n) : ℝ)| / (2 * n) ∧
    (Nat.card (UnorderedIncreasingClass 0 n (Finset.Icc 1 (2 * n - 1))) : ℝ) =
      iteratedDeriv (2 * n - 1) Real.tan 0 :=
  source_fullyFrozen_card_formula n (by omega)

example : (Nat.card (UnorderedIncreasingClass 0 1 (Finset.Icc 1 1)) : ℝ) = 1 := by
  have hh := source_fullyFrozen_card_bernoulli 1 (by decide)
  norm_num [bernoulli_two] at hh ⊢
  exact hh

#print axioms tangentDerivativePolynomial_realization
#print axioms tangentDerivativePolynomial_constant
#print axioms tangentDenominatorInverse_identity
#print axioms tangentFormalSeries_constant
#print axioms tangentFormalSeries_riccati
#print axioms tangentFormalSeries_iterate_derivative
#print axioms tangentPolynomialSeries_constant
#print axioms tangentFormalSeries_coefficient
#print axioms rescaledBernoulliSeries_identity
#print axioms tangentExponential_sub_one_ne_zero
#print axioms bernoulliSeries_difference
#print axioms X_mul_tangentFormalSeries
#print axioms tangentFormalSeries_coeff_bernoulli
#print axioms tangent_derivative_bernoulli_identity
#print axioms tangent_derivative_bernoulli
#print axioms source_fullyFrozen_card_formula

end TangentEnumerationStatementAudit
