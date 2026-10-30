module

import Freezing1.PoissonLowerTail

open MeasureTheory ProbabilityTheory Filter Freezing1
open scoped Topology NNReal

-- The strict event retains its actual Poisson measure, including integer thresholds.
example (coefficient threshold : ℝ) (hcoefficient : 0 < coefficient)
    (hthreshold : 1 < threshold)
    (hrate : coefficient * bennettRate (threshold - 1) < 1) :
    Tendsto (fun scale : ℕ => (scale : ℝ) *
      (poissonMeasure (logarithmicPoissonRate coefficient hcoefficient.le scale)).real
        {value : ℕ | coefficient * Real.log (scale : ℝ) * threshold < (value : ℝ)})
      atTop atTop :=
  tendsto_nat_mul_poisson_strict_tail_atTop hcoefficient hthreshold hrate

-- This reconstructs the scalar block-scale choice with the source constant six.
example (slope : LinearRegimeParameter) (margin : ℝ) (hmargin : 0 < margin) :
    ∃ scale : ℕ, 1 < scale ∧
      (((slope : ℝ) + 1) / (2 * (slope : ℝ))) * (linearHeightFactor slope - margin) ≤
        Real.log (scale : ℝ) ∧
      (2 : ℝ) < linearPoissonRate slope scale ∧
      6 / ((slope : ℝ) * scale) ≤ (poissonMeasure (linearPoissonRate slope scale)).real
        {value : ℕ | (linearPoissonRate slope scale : ℝ) *
          (linearHeightFactor slope - margin) < (value : ℝ)} :=
  exists_linear_poisson_tail_scale slope hmargin

#print axioms Freezing1.log_factorial_le_entropy_add_log

#print axioms Freezing1.poisson_log_singleton_lower

#print axioms Freezing1.logarithmicPoissonRate

#print axioms Freezing1.logarithmicPoissonRate_coe

#print axioms Freezing1.strictPoissonCutoff

#print axioms Freezing1.threshold_lt_strictPoissonCutoff

#print axioms Freezing1.strictPoissonCutoff_le

#print axioms Freezing1.poisson_singleton_le_strict_tail

#print axioms Freezing1.tendsto_strictPoissonCutoff_div_log

#print axioms Freezing1.tendsto_log_div_log_of_div_log_limit

#print axioms Freezing1.tendsto_nat_mul_poisson_strict_tail_atTop

#print axioms Freezing1.linearPoissonRate

#print axioms Freezing1.linear_poisson_strict_tail_atTop

#print axioms Freezing1.exists_linear_poisson_tail_scale
