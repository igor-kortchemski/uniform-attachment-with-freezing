module

import Freezing1.PoissonSourcePolynomialScale
import Freezing1.PoissonSourcePolynomialChecks
import Freezing1.PoissonSourcePolynomialSlackChecks

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

noncomputable section

namespace Freezing1.A56IndependentStatementAudit

set_option backward.isDefEq.respectTransparency false

/-- Source lambda and t are real, and the event is the literal strict tail. -/
example (lam t : ℝ) (hlam : 2 < lam) (ht : 1 < t) :
    Real.exp (-lam * (t * Real.log t - t + 1)) / (lam * t) ^ 3 ≤
      (poissonMeasure (⟨lam, by linarith⟩ : ℝ≥0)).real {k : ℕ | lam * t < (k : ℝ)} := by
  have hg : bennettRate (t - 1) = t * Real.log t - t + 1 := by
    unfold bennettRate
    rw [show 1 + (t - 1) = t by ring]
    ring
  let rate : ℝ≥0 := ⟨lam, by linarith⟩
  have hcoe : (rate : ℝ) = lam := rfl
  have hh := poisson_strict_tail_cubic_lower rate (by rwa [hcoe]) ht
  rw [hcoe, hg] at hh
  exact hh

/-- Integral thresholds are included; the strict witness is the next integer. -/
example : strictPoissonCutoff 3 2 = 7 ∧
    ¬ (3 : ℝ) * 2 < (Nat.ceil ((3 : ℝ) * 2) : ℝ) := by
  norm_num [strictPoissonCutoff]

example : Real.exp (-(3 : ℝ) * ((2 : ℝ) * Real.log 2 - 2 + 1)) / ((3 : ℝ) * 2) ^ 3 ≤
    (poissonMeasure 3).real {k : ℕ | (6 : ℝ) < (k : ℝ)} := by
  have hg : bennettRate ((2 : ℝ) - 1) = (2 : ℝ) * Real.log 2 - 2 + 1 := by
    norm_num [bennettRate]
    ring
  simpa [hg, show (3 : ℝ) * 2 = 6 by norm_num] using
    poisson_strict_tail_cubic_lower 3 (by norm_num) (by norm_num : (1 : ℝ) < 2)

/-- The finite logarithmic conversion keeps the rounding constraint visible. -/
example (K t : ℝ) (hK : 0 < K) (ht : 1 < t) (C : ℕ) (hC : 1 < C)
    (hlam : 2 < K * Real.log (C : ℝ)) (hround : (K * t) ^ 3 ≤ Real.log (C : ℝ)) :
    Real.exp (-(K * Real.log (C : ℝ)) * bennettRate (t - 1)) / Real.log (C : ℝ) ^ 4 ≤
      (poissonMeasure (⟨K * Real.log (C : ℝ), by
        exact mul_nonneg hK.le (Real.log_natCast_nonneg C)⟩ : ℝ≥0)).real
          {k : ℕ | K * Real.log (C : ℝ) * t < (k : ℝ)} :=
  logarithmicPoisson_polynomial_lower hK ht C hC hlam hround

/-- The sufficient finite constraints are obtained, not assumed, at the chosen scale. -/
example (K t c L : ℝ) (hK : 0 < K) (ht : 1 < t) (hc : 0 < c)
    (hq : K * bennettRate (t - 1) < 1) :
    ∃ C : ℕ, 1 < C ∧ L ≤ Real.log (C : ℝ) ∧ 2 < K * Real.log (C : ℝ) ∧
      (K * t) ^ 3 ≤ Real.log (C : ℝ) ∧
      6 / (c * C) ≤ Real.exp (-(K * Real.log (C : ℝ)) * bennettRate (t - 1)) /
        Real.log (C : ℝ) ^ 4 ∧
      Real.exp (-(K * Real.log (C : ℝ)) * bennettRate (t - 1)) / Real.log (C : ℝ) ^ 4 ≤
        (poissonMeasure (⟨K * Real.log (C : ℝ),
          mul_nonneg hK.le (Real.log_natCast_nonneg C)⟩ : ℝ≥0)).real
            {k : ℕ | K * Real.log (C : ℝ) * t < (k : ℝ)} :=
  exists_poisson_polynomial_scale hK ht hc hq L

/-- Reconstruct the source's delta and both displayed C inequalities on
the admissible small-margin branch; no slack hypothesis is imported. -/
theorem source_small_margin_scale (c : LinearRegimeParameter) (η : ℝ)
    (hη : 0 < η) (ht : 1 < linearHeightFactor c - η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      δ = 1 - (((c : ℝ) + 1) / (2 * (c : ℝ))) *
        bennettRate (linearHeightFactor c - 1 - η) ∧
      ∃ C : ℕ, 1 < C ∧
        (((c : ℝ) + 1) / (2 * (c : ℝ))) * (linearHeightFactor c - η) ≤ Real.log (C : ℝ) ∧
        6 / ((c : ℝ) * C) ≤ Real.exp (-(1 - δ) * Real.log (C : ℝ)) / Real.log (C : ℝ) ^ 4 ∧
        Real.exp (-(1 - δ) * Real.log (C : ℝ)) / Real.log (C : ℝ) ^ 4 ≤
          (poissonMeasure (linearPoissonRate c C)).real
            {k : ℕ | (linearPoissonRate c C : ℝ) * (linearHeightFactor c - η) < (k : ℝ)} := by
  let K : ℝ := ((c : ℝ) + 1) / (2 * (c : ℝ))
  let g : ℝ := bennettRate (linearHeightFactor c - 1 - η)
  let δ : ℝ := 1 - K * g
  have hc := c.property.1
  have hK : 0 < K := by dsimp [K]; positivity
  have hgp : 0 < g := bennettRate_pos (by linarith)
  have hq : K * g < 1 := by
    simpa only [K, g, show linearHeightFactor c - η - 1 =
      linearHeightFactor c - 1 - η by ring] using
        linear_source_rate_slack c ht (by linarith : linearHeightFactor c - η < linearHeightFactor c)
  obtain ⟨C, hC, hlog, _, hlo, hhi⟩ := exists_linear_poisson_polynomial_scale c hη ht
  have he : -(1 - δ) * Real.log (C : ℝ) =
      -(linearPoissonRate c C : ℝ) * bennettRate (linearHeightFactor c - 1 - η) := by
    have hrate : (linearPoissonRate c C : ℝ) = K * Real.log (C : ℝ) := rfl
    rw [hrate]
    change -(1 - δ) * Real.log (C : ℝ) = -(K * Real.log (C : ℝ)) * g
    dsimp [δ]
    ring
  refine ⟨δ, by dsimp [δ]; linarith, by
    have hp := mul_pos hK hgp
    dsimp [δ]
    linarith, rfl, C, hC, hlog, ?_, ?_⟩
  · rwa [he]
  · rwa [he]

/-- Every positive margin, hence the entire source interval (0,1), has
a scale witness retaining the original probability threshold. -/
example (c : LinearRegimeParameter) (η : ℝ) (hη : 0 < η) :
    let t := max ((linearHeightFactor c + 1) / 2) (linearHeightFactor c - η)
    1 < t ∧ t < linearHeightFactor c ∧ linearHeightFactor c - η ≤ t ∧
      0 < 1 - (((c : ℝ) + 1) / (2 * (c : ℝ))) * bennettRate (t - 1) ∧
      1 - (((c : ℝ) + 1) / (2 * (c : ℝ))) * bennettRate (t - 1) < 1 := by
  let t := max ((linearHeightFactor c + 1) / 2) (linearHeightFactor c - η)
  have hf := one_lt_linearHeightFactor c
  have hc := c.property.1
  have ht : 1 < t := lt_of_lt_of_le (by linarith : 1 < (linearHeightFactor c + 1) / 2)
    (le_max_left _ _)
  have htf : t < linearHeightFactor c := by apply max_lt <;> linarith
  have hslack := linear_source_rate_slack c ht htf
  have hK : 0 < ((c : ℝ) + 1) / (2 * (c : ℝ)) := by positivity
  have hg := bennettRate_pos (by linarith : 0 < t - 1)
  have hp := mul_pos hK hg
  exact ⟨ht, htf, le_max_right _ _, by linarith, by linarith⟩

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

/-- An actual counterexample to the printed factorial estimate, with
the Poisson regime inequalities explicitly checked at the same value. -/
example : (2 : ℝ) < 41 / 20 ∧ (1 : ℝ) < 42 / 41 ∧
    (41 / 20 : ℝ) * (42 / 41) = 21 / 10 ∧
    (2 : ℝ) ≤ 21 / 10 ∧
    (21 / 10 : ℝ) ^ 3 * Real.rpow ((21 / 10) / Real.exp 1) (21 / 10) <
      ((Nat.ceil (21 / 10 : ℝ)).factorial : ℝ) := by
  obtain ⟨hlam, ht, hprod⟩ := ceiling_factorial_counterexample_is_source_admissible
  obtain ⟨hu, hfail⟩ := printed_real_ceiling_factorial_counterexample
  exact ⟨hlam, ht, hprod, hu, hfail⟩

/-- The rate-slack counterexample lies in all original source domains. -/
example : ∃ c : LinearRegimeParameter,
    (0 : ℝ) < c ∧ (c : ℝ) ≤ 1 ∧ linearHeightFactor c = 5 / 4 ∧
      (0 : ℝ) < 3 / 4 ∧ (3 / 4 : ℝ) < 1 ∧
      1 - (((c : ℝ) + 1) / (2 * (c : ℝ))) *
        (((linearHeightFactor c - 3 / 4) * Real.log (linearHeightFactor c - 3 / 4)) -
          (linearHeightFactor c - 1 - 3 / 4)) < 0 := by
  obtain ⟨c, hf, hη0, hη1, hδ⟩ := printed_all_margin_rate_slack_counterexample
  refine ⟨c, c.property.1, c.property.2, hf, hη0, hη1, ?_⟩
  simpa only [bennettRate, show 1 + (linearHeightFactor c - 1 - 3 / 4) =
    linearHeightFactor c - 3 / 4 by ring] using hδ

#print axioms log_factorial_le_entropy_add_log
#print axioms poisson_strict_log_singleton_rounding_lower
#print axioms poisson_strict_tail_rounding_lower
#print axioms poisson_rounding_prefactor_ge_cubic
#print axioms poisson_three_mass_lower
#print axioms poisson_strict_tail_cubic_lower
#print axioms logarithmicPoisson_polynomial_lower
#print axioms tendsto_nat_mul_log_polynomial_atTop
#print axioms exists_poisson_polynomial_scale
#print axioms linear_source_rate_slack
#print axioms exists_linear_poisson_polynomial_scale
#print axioms exists_linear_poisson_polynomial_scale_all_margins
#print axioms source_small_margin_scale
#print axioms printed_real_ceiling_factorial_counterexample
#print axioms printed_all_margin_rate_slack_counterexample

end Freezing1.A56IndependentStatementAudit
