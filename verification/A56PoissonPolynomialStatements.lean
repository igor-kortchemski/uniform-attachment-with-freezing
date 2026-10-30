module

import Freezing1.PoissonSourcePolynomialScale
import Freezing1.PoissonSourcePolynomialChecks
import Freezing1.PoissonSourcePolynomialSlackChecks

/-! Author-created expanded A56 quantitative and source-defect checks.
Final imported-file verification is required after sole-root integration. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open Freezing1

set_option backward.isDefEq.respectTransparency false

example (rate : ℝ≥0) (hr : 0 < rate) (t : ℝ) (ht : 1 < t) :
    Real.exp (-(rate : ℝ) * ((1 + (t - 1)) * Real.log (1 + (t - 1)) - (t - 1))) *
        (rate : ℝ) / (Real.exp 1 * ((rate : ℝ) * t + 1) ^ 2) ≤
      (poissonMeasure rate).real {k : ℕ | (rate : ℝ) * t < (k : ℝ)} :=
  poisson_strict_tail_rounding_lower rate hr ht

example (rate : ℝ≥0) (hr : (2 : ℝ) < rate) (t : ℝ) (ht : 1 < t) :
    Real.exp (-(rate : ℝ) * bennettRate (t - 1)) / ((rate : ℝ) * t) ^ 3 ≤
      (poissonMeasure rate).real {k : ℕ | (rate : ℝ) * t < (k : ℝ)} :=
  poisson_strict_tail_cubic_lower rate hr ht

example (rate : ℝ≥0) (hr2 : (2 : ℝ) ≤ rate) (hr3 : (rate : ℝ) ≤ 3) :
    (1 / 8 : ℝ) ≤ (poissonMeasure rate).real {3} :=
  poisson_three_mass_lower rate hr2 hr3

example (K t c L₀ : ℝ) (hK : 0 < K) (ht : 1 < t) (hc : 0 < c)
    (hrate : K * bennettRate (t - 1) < 1) :
    ∃ C : ℕ, 1 < C ∧ L₀ ≤ Real.log (C : ℝ) ∧ 2 < K * Real.log (C : ℝ) ∧
      (K * t) ^ 3 ≤ Real.log (C : ℝ) ∧
      6 / (c * C) ≤ Real.exp (-(K * Real.log (C : ℝ)) * bennettRate (t - 1)) /
        Real.log (C : ℝ) ^ 4 ∧
      Real.exp (-(K * Real.log (C : ℝ)) * bennettRate (t - 1)) / Real.log (C : ℝ) ^ 4 ≤
        (poissonMeasure (logarithmicPoissonRate K hK.le C)).real
          {k : ℕ | K * Real.log (C : ℝ) * t < (k : ℝ)} :=
  exists_poisson_polynomial_scale hK ht hc hrate L₀

example (c : LinearRegimeParameter) (η : ℝ) (hη : 0 < η)
    (ht : 1 < linearHeightFactor c - η) :
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      2 < (linearPoissonRate c C : ℝ) ∧
      6 / ((c : ℝ) * C) ≤
        Real.exp (-(linearPoissonRate c C : ℝ) * bennettRate (linearHeightFactor c - 1 - η)) /
          Real.log (C : ℝ) ^ 4 ∧
      Real.exp (-(linearPoissonRate c C : ℝ) * bennettRate (linearHeightFactor c - 1 - η)) /
          Real.log (C : ℝ) ^ 4 ≤
        (poissonMeasure (linearPoissonRate c C)).real
          {k : ℕ | (linearPoissonRate c C : ℝ) * (linearHeightFactor c - η) < (k : ℝ)} :=
  exists_linear_poisson_polynomial_scale c hη ht

example (c : LinearRegimeParameter) (η : ℝ) (hη : 0 < η) :
    let t := max ((linearHeightFactor c + 1) / 2) (linearHeightFactor c - η)
    ∃ C : ℕ, 1 < C ∧
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
      2 < (linearPoissonRate c C : ℝ) ∧
      6 / ((c : ℝ) * C) ≤
        Real.exp (-(linearPoissonRate c C : ℝ) * bennettRate (t - 1)) / Real.log (C : ℝ) ^ 4 ∧
      Real.exp (-(linearPoissonRate c C : ℝ) * bennettRate (t - 1)) / Real.log (C : ℝ) ^ 4 ≤
        (poissonMeasure (linearPoissonRate c C)).real
          {k : ℕ | (linearPoissonRate c C : ℝ) * (linearHeightFactor c - η) < (k : ℝ)} :=
  exists_linear_poisson_polynomial_scale_all_margins c hη

example : (2 : ℝ) ≤ 21 / 10 ∧
    (21 / 10 : ℝ) ^ 3 * Real.rpow ((21 / 10) / Real.exp 1) (21 / 10) <
      ((Nat.ceil (21 / 10 : ℝ)).factorial : ℝ) :=
  printed_real_ceiling_factorial_counterexample

example : ∃ c : LinearRegimeParameter, linearHeightFactor c = 5 / 4 ∧
    (0 : ℝ) < 3 / 4 ∧ (3 / 4 : ℝ) < 1 ∧
    1 - (((c : ℝ) + 1) / (2 * (c : ℝ))) *
      bennettRate (linearHeightFactor c - 1 - 3 / 4) < 0 :=
  printed_all_margin_rate_slack_counterexample

example (q : ℝ) (hq : q < 1) :
    Tendsto (fun C : ℕ => (C : ℝ) *
      (Real.exp (-q * Real.log (C : ℝ)) / Real.log (C : ℝ) ^ 4)) atTop atTop :=
  tendsto_nat_mul_log_polynomial_atTop hq

#print axioms poisson_strict_log_singleton_rounding_lower
#print axioms poisson_strict_tail_rounding_lower
#print axioms poisson_three_mass_lower
#print axioms poisson_strict_tail_cubic_lower
#print axioms logarithmicPoisson_polynomial_lower
#print axioms tendsto_nat_mul_log_polynomial_atTop
#print axioms exists_poisson_polynomial_scale
#print axioms linear_source_rate_slack
#print axioms exists_linear_poisson_polynomial_scale
#print axioms exists_linear_poisson_polynomial_scale_all_margins
#print axioms printed_real_ceiling_factorial_counterexample
#print axioms printed_all_margin_rate_slack_counterexample
