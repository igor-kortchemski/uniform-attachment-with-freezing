module

public import Freezing1.UniformBirthSourceHeightLimit
public import Freezing1.UniformBirthRealBennettIntegral
public import Freezing1.UniformBirthHarmonicTail

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open Freezing1 Freezing1.UniformBirth

/- Authored expanded-type checks. Independent review is recorded separately. -/

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (hbulk : BulkLowerBound rows) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => ∫ z : ℕ × (Fin n → ℕ),
      |(truncatedSum (rows n) z.1 z.2 : ℝ) / truncatedMean (rows n) n (hrows n) z.1 - 1| ^ q
      ∂auxiliaryLaw (rows n) n (hrows n)) atTop (nhds 0) :=
  randomRelativeError_real_moment_tendsto rows hrows hbulk hq

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (hbulk : BulkLowerBound rows) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => ∫ z : ℕ × (Fin n → ℕ),
      |((truncatedSum (rows n) z.1 z.2 : ℝ) - truncatedMean (rows n) n (hrows n) z.1) /
        heightScale (rows n) n| ^ q
      ∂auxiliaryLaw (rows n) n (hrows n)) atTop (nhds 0) :=
  centeredScaleError_real_moment_tendsto rows hrows hbulk hq

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (hbulk : BulkLowerBound rows) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm (fun z : ℕ × (Fin n → ℕ) =>
      (truncatedSum (rows n) z.1 z.2 : ℝ) / heightScale (rows n) n - 1)
      (ENNReal.ofReal p) (auxiliaryLaw (rows n) n (hrows n))) atTop (nhds 0) :=
  randomSum_normalized_tendsto_Lp rows hrows hbulk hp

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) {q : ℝ} (hq : 0 ≤ q) :
    (auxiliaryLaw x n h)[(fun z : ℕ × (Fin n → ℕ) =>
      |(truncatedSum x z.1 z.2 : ℝ) / truncatedMean x n h z.1 - 1| ^ q) |
        (inferInstance : MeasurableSpace ℕ).comap Prod.fst] =ᵐ[auxiliaryLaw x n h]
      (fun z => ∫ Y, |(truncatedSum x z.1 Y : ℝ) / truncatedMean x n h z.1 - 1| ^ q
        ∂bernoulliProductLaw (reciprocalParameter x n h)) :=
  relativeMoment_condExp x n h hq

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    HasLaw (fun z : ℕ × (Fin n → ℕ) => truncatedSum x z.1 z.2)
      (Forward.uniformHeightLaw x n) (auxiliaryLaw x n h) :=
  auxiliary_uniformHeight_hasLaw x n h

example {q m : ℝ} (hq : 0 < q) (hm : 0 < m) :
    (bennettMomentIntegral q m).toReal =
      ∫ u in Set.Ioi (0 : ℝ), Real.exp (-m * bennettRate u) * u ^ (q - 1) := by
  rw [bennettMomentIntegral_eq_ofReal hq hm, ENNReal.toReal_ofReal]
  · rfl
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact bennettMomentDensity_nonneg hu.le q m

#print axioms Freezing1.UniformBirth.relativeMoment_integrable
#print axioms Freezing1.UniformBirth.relativeMoment_condExp
#print axioms Freezing1.UniformBirth.relativeMoment_condExp_layercake
#print axioms Freezing1.UniformBirth.relativeTail_condExp_bennett
#print axioms Freezing1.UniformBirth.randomRelativeError_bennett_integral_bound
#print axioms Freezing1.UniformBirth.randomRelativeError_moment_tendsto
#print axioms Freezing1.UniformBirth.randomRelativeError_tendsto_Lp
#print axioms Freezing1.UniformBirth.centeredScaleError_tendsto_Lp
#print axioms Freezing1.UniformBirth.randomRelativeError_real_moment_tendsto
#print axioms Freezing1.UniformBirth.centeredScaleError_real_moment_le_relative
#print axioms Freezing1.UniformBirth.centeredScaleError_real_moment_tendsto
#print axioms Freezing1.UniformBirth.randomSum_normalized_tendsto_Lp
#print axioms Freezing1.UniformBirth.expected_bennettMomentIntegral_ne_top
#print axioms Freezing1.UniformBirth.realBennettIntegral_integrable
#print axioms Freezing1.UniformBirth.randomRelativeError_real_bennett_bound
#print axioms Freezing1.UniformBirth.expected_realBennettIntegral_tendsto
#print axioms Freezing1.UniformBirth.eventual_mean_tail_normalized_le_log
#print axioms Freezing1.UniformBirth.auxiliary_uniformHeight_hasLaw
#print axioms Freezing1.UniformBirth.linear_uniform_height_via_random_mean
