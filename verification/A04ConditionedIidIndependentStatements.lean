module

import Freezing1.IidLinearConditionedRows
import Freezing1.IidLinearMaximumRatio

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace Freezing1

example (p : unitInterval) (hp : (1 : ℝ) / 2 < p) (n : ℕ) :
    HasLaw (ForwardAnnealed.conditionedIidRow p hp n)
      ((ForwardAnnealed.iidSignLaw p)[|{x : SignSequence | (n : ℕ∞) < extinctionTime x}])
      (ForwardAnnealed.conditionedIidRowsLaw p hp) :=
  ForwardAnnealed.conditionedIidRow_hasLaw p hp n

example (p : unitInterval) (hp : (1 : ℝ) / 2 < p) (hp1 : (p : ℝ) < 1)
    (A : ℕ → ℝ) (hApos : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hAlog : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0)) :
    ∃ μ : Measure (ℝ × SignSequence × (ℕ → SignSequence)), IsProbabilityMeasure μ ∧
      ∃ rows : ℕ → (ℝ × SignSequence × (ℕ → SignSequence)) → SignSequence,
        ∃ survivor : (ℝ × SignSequence × (ℕ → SignSequence)) → SignSequence,
          (∀ n, HasLaw (rows n)
            ((ForwardAnnealed.iidSignLaw p)[|{x : SignSequence | (n : ℕ∞) < extinctionTime x}]) μ) ∧
          HasLaw survivor ((ForwardAnnealed.iidSignLaw p)[|{x | extinctionTime x = ⊤}]) μ ∧
          ∀ᵐ z ∂μ, (∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n z)) ∧
            (∀ᶠ n in atTop, rows n z = survivor z) ∧
            Tendsto (fun ε : ℝ => limsup
              (nearOriginMaximum (fun n => rows n z) A (2 * (p : ℝ) - 1) ε) atTop)
              (𝓝[>] 0) (𝓝 0) ∧
            (∀ ε : ℝ, 0 < ε → ε < 1 →
              0 < liminf (bulkMinimum (fun n => rows n z) ε) atTop) :=
  ForwardAnnealed.exists_conditioned_iid_linear_coupling p hp hp1 A hApos hAinf hAlog

example (p : unitInterval) (hp : (1 : ℝ) / 2 < p)
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop) :
    ∀ᵐ z ∂ForwardAnnealed.conditionedIidRowsLaw p hp,
      Tendsto (nearOriginMaximum (fun n => ForwardAnnealed.conditionedIidRow p hp n z)
        A (2 * (p : ℝ) - 1) 1) atTop (𝓝 0) := by
  filter_upwards [ForwardAnnealed.conditionedIidRows_uniformTailRatio p hp A hA] with z hz
  exact uniformTailRatio_iff_maximum_tendsto.mp hz

example (rows : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (h : Tendsto (nearOriginMaximum rows A c 1) atTop (𝓝 0))
    (hc : 0 < c) (hc1 : c ≤ 1) (hApos : ∀ n, 0 < A n)
    (hAlog : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hs : ∀ n, PositiveThrough (rows n) n) :
    NearOriginLimsup rows A c ∧ BulkLiminf rows :=
  sourceAssumptions_of_uniformMaximum h hc hc1 hApos hAlog hs

#print axioms ConditionalSurvival.conditional_mixture
#print axioms ConditionalSurvival.weight_tendsto_one
#print axioms ConditionalSurvival.System.map_row
#print axioms ConditionalSurvival.System.eventually_row_eq_survivor
#print axioms ForwardAnnealed.iid_survival_positive
#print axioms ForwardAnnealed.iInter_survivesThrough
#print axioms uniformTailRatio_of_eventually_eq_path
#print axioms uniformTailRatio_iff_maximum_tendsto
#print axioms sourceAssumptions_of_uniformMaximum
#print axioms ForwardAnnealed.conditionedIidRows_sourceAssumptions
#print axioms ForwardAnnealed.exists_conditioned_iid_linear_coupling

end Freezing1
