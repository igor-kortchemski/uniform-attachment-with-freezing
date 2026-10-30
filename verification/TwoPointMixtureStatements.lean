module

import Freezing1.SIRGeometricSurvivalScalar

/-!
Development exact-type checks of the root-authored scalar aggregation.
This is self-review; the final finite-rate main theorem needs its own
independent source review after the geometric inputs are integrated.
-/

open Freezing1 Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

example (nu : ℕ → ProbabilityMeasure (Bool × ℝ)) (p : unitInterval) (c : ℝ)
    (hgate : Tendsto (fun n => (nu n : Measure (Bool × ℝ)).real {z | z.1 = true})
      atTop (𝓝 (p : ℝ)))
    (hjoint : ∀ eps > 0, Tendsto (fun n => (nu n : Measure (Bool × ℝ)).real
      {z | eps ≤ |z.2 - (if z.1 then c else 0)|}) atTop (𝓝 0)) :
    Tendsto (fun n => (nu n).map Prod.snd) atTop
      (𝓝 (⟨bernoulliMeasure c 0 p, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  TwoPointMixture.marginal_tendsto nu p c hgate hjoint

example (lam : ℝ≥0) (hlam : (1 : ℝ) < lam) (c : ℝ) :
    SIR.geometricSurvivalScalarLaw lam c =
      (⟨bernoulliMeasure c 0 (SIR.sirSurvivalParameter lam), inferInstance⟩ :
        ProbabilityMeasure ℝ) :=
  SIR.geometricSurvivalScalarLaw_eq_twoPoint lam hlam c

#print axioms Freezing1.TwoPointMixture.test_control
#print axioms Freezing1.TwoPointMixture.integral_error_bound
#print axioms Freezing1.TwoPointMixture.marginal_tendsto
#print axioms Freezing1.SIR.geometricSurvivalScalarLaw_eq_twoPoint
