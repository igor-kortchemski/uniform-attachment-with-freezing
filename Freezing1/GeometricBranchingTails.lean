module

public import Freezing1.MainGeometricLimit

/-!
# The literal geometric offspring-tail recurrence

The first-child decomposition proves the recurrence directly for every
fixed-point law, as used in the manuscript's proof of Lemma L05.
-/

@[expose] public section

namespace Freezing1.FirstChildStructure

open MeasureTheory
open scoped ENNReal Classical

variable {T : Type*} [MeasurableSpace T]

theorem degree_tail_recurrence_of_fixedPoint (D : FirstChildStructure T)
    (mu : Measure T) [IsProbabilityMeasure mu] (q r : ℝ≥0∞)
    (hmu : mu = q • Measure.dirac D.leaf + r • (mu.prod mu).map D.graft) (k : ℕ) :
    mu {t | k + 1 ≤ D.degree t} = r * mu {t | k ≤ D.degree t} := by
  have hm : MeasurableSet {t | k + 1 ≤ D.degree t} :=
    measurableSet_le measurable_const D.measurable_degree
  have hp : D.graft ⁻¹' {t | k + 1 ≤ D.degree t} =
      Set.univ ×ˢ {t | k ≤ D.degree t} := by
    ext ab
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, D.degree_graft,
      Nat.add_le_add_iff_right, Set.mem_prod, Set.mem_univ, true_and]
  conv_lhs => rw [hmu]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hm,
    Measure.map_apply D.measurable_graft hm, hp, Measure.prod_prod]
  simp [D.degree_leaf]

theorem degree_tail_of_fixedPoint (D : FirstChildStructure T)
    (mu : Measure T) [IsProbabilityMeasure mu] (q r : ℝ≥0∞)
    (hmu : mu = q • Measure.dirac D.leaf + r • (mu.prod mu).map D.graft) (k : ℕ) :
    mu {t | k ≤ D.degree t} = r ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [D.degree_tail_recurrence_of_fixedPoint mu q r hmu k, ih, pow_succ]
    exact mul_comm _ _

end Freezing1.FirstChildStructure

namespace Freezing1.ForwardAnnealed

open MeasureTheory
open scoped ENNReal Classical

theorem planeLimitLaw_offspring_tail (p : unitInterval) (hp : (p : ℝ) < 1) (k : ℕ) :
    (planeLimitLaw p : Measure PlaneTree.Tree) {T | k ≤ PlaneTree.degree T} =
      ENNReal.ofReal ((p : ℝ) ^ k) := by
  have hh := PlaneTree.firstChildStructure.degree_tail_of_fixedPoint
    (planeLimitLaw p : Measure PlaneTree.Tree)
    (ENNReal.ofReal (1 - (p : ℝ))) (ENNReal.ofReal (p : ℝ))
    (planeLimitLaw_fixedPoint p hp) k
  change (planeLimitLaw p : Measure PlaneTree.Tree) {T | k ≤ PlaneTree.degree T} =
    ENNReal.ofReal (p : ℝ) ^ k at hh
  simpa only [ENNReal.ofReal_pow p.2.1] using hh

theorem planeLimitLaw_offspring_tail_recurrence (p : unitInterval) (hp : (p : ℝ) < 1)
    (k : ℕ) :
    (planeLimitLaw p : Measure PlaneTree.Tree) {T | k + 1 ≤ PlaneTree.degree T} =
      ENNReal.ofReal (p : ℝ) *
        (planeLimitLaw p : Measure PlaneTree.Tree) {T | k ≤ PlaneTree.degree T} :=
  PlaneTree.firstChildStructure.degree_tail_recurrence_of_fixedPoint
    (planeLimitLaw p : Measure PlaneTree.Tree)
    (ENNReal.ofReal (1 - (p : ℝ))) (ENNReal.ofReal (p : ℝ))
    (planeLimitLaw_fixedPoint p hp) k

end Freezing1.ForwardAnnealed
