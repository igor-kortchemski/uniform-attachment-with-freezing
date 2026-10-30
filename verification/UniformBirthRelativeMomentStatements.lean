module

import Freezing1.UniformBirthMomentConclusions

open Freezing1 Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology Classical ProbabilityTheory

namespace UniformBirthRelativeMomentAudit

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (hbulk : BulkLowerBound rows) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => ∫ z,
      |UniformBirth.randomSum (rows n) z / UniformBirth.randomMean (rows n) n (hrows n) z - 1| ^ q
      ∂UniformBirth.auxiliaryLaw (rows n) n (hrows n)) atTop (nhds 0) :=
  UniformBirth.randomRelativeError_real_moment_tendsto rows hrows hbulk hq

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (hbulk : BulkLowerBound rows) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => ∫ z,
      |(UniformBirth.randomSum (rows n) z - UniformBirth.randomMean (rows n) n (hrows n) z) /
        heightScale (rows n) n| ^ q
      ∂UniformBirth.auxiliaryLaw (rows n) n (hrows n)) atTop (nhds 0) :=
  UniformBirth.centeredScaleError_real_moment_tendsto rows hrows hbulk hq

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (hbulk : BulkLowerBound rows) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm
      (fun z => UniformBirth.randomSum (rows n) z / heightScale (rows n) n - 1)
      (ENNReal.ofReal p) (UniformBirth.auxiliaryLaw (rows n) n (hrows n))) atTop (nhds 0) :=
  UniformBirth.randomSum_normalized_tendsto_Lp rows hrows hbulk hp

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (hbulk : BulkLowerBound rows) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => ∫⁻ z,
      bennettMomentIntegral q (UniformBirth.randomMean (rows n) n (hrows n) z)
      ∂UniformBirth.auxiliaryLaw (rows n) n (hrows n)) atTop (nhds 0) :=
  UniformBirth.expected_bennettMomentIntegral_tendsto rows hrows hbulk hq

#print axioms bernoulli_normalized_closed_deviation_le
#print axioms bennettMomentIntegral_add_nat_tendsto
#print axioms UniformBirth.relativeMoment_condExp_layercake
#print axioms UniformBirth.relativeTail_condExp_bennett
#print axioms UniformBirth.expected_bennettMomentIntegral_tendsto
#print axioms UniformBirth.randomRelativeError_real_moment_tendsto
#print axioms UniformBirth.centeredScaleError_real_moment_le_relative
#print axioms UniformBirth.centeredScaleError_real_moment_tendsto
#print axioms UniformBirth.randomSum_normalized_tendsto_Lp

end UniformBirthRelativeMomentAudit
