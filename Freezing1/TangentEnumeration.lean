module

public import Freezing1.TangentBernoulliSeries
public import Freezing1.TangentFormalDerivatives
public import Freezing1.TangentBernoulliAlgebra
public import Freezing1.TreeGrowthPolynomial

/-! The source's full tangent/Bernoulli enumeration, with no counting premise. -/

@[expose] public section

namespace Freezing1.BinaryBijection

set_option backward.isDefEq.respectTransparency false

theorem tangent_derivative_bernoulli_identity (n : ℕ) (hn : 0 < n) :
    ((iteratedDeriv (2 * n - 1) Real.tan 0 : ℝ) : ℂ) =
      ((2 * n - 1).factorial : ℂ) *
        ((2 * Complex.I) ^ (2 * n) - (4 * Complex.I) ^ (2 * n)) *
          algebraMap ℚ ℂ (bernoulli (2 * n) / (2 * n).factorial) := by
  have hc := tangentFormalSeries_coeff_bernoulli (2 * n - 1) (by omega)
  rw [show 2 * n - 1 + 1 = 2 * n by omega] at hc
  have hd : ((iteratedDeriv (2 * n - 1) Real.tan 0 : ℝ) : ℂ) =
      ((tangentDerivativePolynomial (2 * n - 1)).coeff 0 : ℂ) := by
    rw [← tangentDerivativePolynomial_constant]
    norm_cast
  rw [hd, ← tangentFormalSeries_coefficient, hc]
  ring

theorem tangent_derivative_bernoulli (n : ℕ) (hn : 0 < n) :
    iteratedDeriv (2 * n - 1) Real.tan 0 =
      (4 : ℝ) ^ n * ((4 : ℝ) ^ n - 1) * |(bernoulli (2 * n) : ℝ)| / (2 * n) :=
  tangent_bernoulli_absolute_formula n hn _ (tangent_iteratedDeriv_zero_nonneg _)
    (tangent_derivative_bernoulli_identity n hn)

theorem source_fullyFrozen_card_bernoulli (n : ℕ) (hn : 0 < n) :
    (Nat.card (UnorderedIncreasingClass 0 n (Finset.Icc 1 (2 * n - 1))) : ℝ) =
      (4 : ℝ) ^ n * ((4 : ℝ) ^ n - 1) * |(bernoulli (2 * n) : ℝ)| / (2 * n) := by
  rw [source_fullyFrozen_card_tangent n hn, tangent_derivative_bernoulli n hn]

/-- Corollary C01 for the actual increasing unordered source class. -/
theorem source_fullyFrozen_card_formula (n : ℕ) (hn : 0 < n) :
    (Nat.card (UnorderedIncreasingClass 0 n (Finset.Icc 1 (2 * n - 1))) : ℝ) =
        (4 : ℝ) ^ n * ((4 : ℝ) ^ n - 1) * |(bernoulli (2 * n) : ℝ)| / (2 * n) ∧
    (Nat.card (UnorderedIncreasingClass 0 n (Finset.Icc 1 (2 * n - 1))) : ℝ) =
      iteratedDeriv (2 * n - 1) Real.tan 0 :=
  ⟨source_fullyFrozen_card_bernoulli n hn, source_fullyFrozen_card_tangent n hn⟩

end Freezing1.BinaryBijection
