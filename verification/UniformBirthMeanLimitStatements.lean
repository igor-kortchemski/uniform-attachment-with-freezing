module

import Freezing1.UniformBirthMeanLimit
import Freezing1.UniformBirthLogTail

open Freezing1 Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology Classical

namespace UniformBirthMeanLimitAudit

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (hbulk : BulkLowerBound rows) {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => (UniformBirth.auxiliaryLaw (rows n) n (hrows n)).real
      {z | eps ≤ |UniformBirth.randomMean (rows n) n (hrows n) z /
        heightScale (rows n) n - 1|}) atTop (nhds 0) :=
  UniformBirth.randomMean_normalized_real_probability rows hrows hbulk heps

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (hbulk : BulkLowerBound rows) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm
      (fun z => UniformBirth.randomMean (rows n) n (hrows n) z / heightScale (rows n) n - 1)
      (ENNReal.ofReal p) (UniformBirth.auxiliaryLaw (rows n) n (hrows n)))
        atTop (nhds 0) :=
  UniformBirth.randomMean_normalized_tendsto_Lp rows hrows hbulk hp

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    {delta : ℝ} (hd : 0 < delta) :
    Tendsto (fun n => (UniformBirth.auxiliaryLaw (rows n) n (hrows n)).real
      {z | delta * Real.log ((n : ℝ) / 2) < Real.log ((n : ℝ) / z.1)}) atTop (nhds 0) :=
  UniformBirth.auxiliary_log_birth_tendsto_zero rows hrows hd

#print axioms UniformBirth.auxiliary_log_birth_exact_CDF
#print axioms UniformBirth.auxiliary_log_birth_tendsto_zero
#print axioms UniformBirth.bulk_late_scale_over_full_tendsto
#print axioms UniformBirth.randomMean_normalized_probability
#print axioms UniformBirth.randomMean_normalized_tendsto_Lp

end UniformBirthMeanLimitAudit
