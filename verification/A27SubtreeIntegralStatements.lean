module

import Freezing1.FirstChildSourceInduction
import Freezing1.MainGeometricLimit

/-! Author-created source-expanded checks for A27. The functions are
nonnegative and may be unbounded; expectations are extended integrals. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical BigOperators
open Freezing1

set_option backward.isDefEq.respectTransparency false

example (μ : Measure PlaneTree.Tree) [IsProbabilityMeasure μ]
    (hsplit : μ {T | 0 < PlaneTree.degree T} ≠ 0 →
      (μ[|{T | 0 < PlaneTree.degree T}]).map
        (fun T => (PlaneTree.child T 1, PlaneTree.dropFirst T)) = μ.prod μ)
    (n : ℕ) (hk : μ {T | PlaneTree.degree T = n + 1} ≠ 0)
    (f : Fin (n + 1) → PlaneTree.Tree → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    let g := fun T => ({T | PlaneTree.degree T = n}.indicator
      (fun T => ∏ i : Fin n, f i.succ (PlaneTree.child T (i.val + 1))) T) *
        (μ {T | 0 < PlaneTree.degree T} / μ {T | PlaneTree.degree T = n + 1})
    ((∫⁻ T, ∏ i : Fin (n + 1), f i (PlaneTree.child T (i.val + 1))
        ∂μ[|{T | PlaneTree.degree T = n + 1}]) =
      ∫⁻ T, f 0 (PlaneTree.child T 1) * g (PlaneTree.dropFirst T)
        ∂μ[|{T | 0 < PlaneTree.degree T}]) ∧
    ((∫⁻ T, g T ∂μ) = ∫⁻ T, ∏ i : Fin n,
      f i.succ (PlaneTree.child T (i.val + 1)) ∂μ[|{T | PlaneTree.degree T = n}]) ∧
    ((∫⁻ T, ∏ i : Fin (n + 1), f i (PlaneTree.child T (i.val + 1))
        ∂μ[|{T | PlaneTree.degree T = n + 1}]) =
      (∫⁻ T, f 0 T ∂μ) * ∫⁻ T, g T ∂μ) := by
  simpa only [FirstChildStructure.sourceInductionIntegrand, PlaneTree.firstChildStructure]
    using PlaneTree.firstChildStructure.source_induction_expectation_identities
      PlaneTree.dropFirst PlaneTree.continuous_dropFirst.measurable
      (fun _ ht => PlaneTree.eq_leaf_of_degree_zero ht)
      (fun _ ht => PlaneTree.graft_child_dropFirst ht) μ hsplit n hk f hf

example (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (k : ℕ)
    (f : Fin k → PlaneTree.Tree → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ T, ∏ i : Fin k, f i (PlaneTree.child T (i.val + 1))
      ∂(ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree)[|{T | PlaneTree.degree T = k}]) =
      ∏ i : Fin k, ∫⁻ T, f i T ∂(ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree) := by
  have hk : (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree)
      {T | PlaneTree.degree T = k} ≠ 0 := by
    rw [ForwardAnnealed.planeLimitLaw_offspring_mass p hp1 k]
    exact (ENNReal.ofReal_pos.mpr (mul_pos (by linarith) (pow_pos hp0 k))).ne'
  exact PlaneTree.firstChildStructure.lintegral_children_product_cond
    (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree)
    (ENNReal.ofReal (1 - (p : ℝ))) (ENNReal.ofReal (p : ℝ))
    (ForwardAnnealed.planeLimitLaw_fixedPoint p hp1) k hk f hf

example (f : Fin 1 → PlaneTree.Tree → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ T in {T | PlaneTree.degree T = 1}, ∏ i : Fin 1,
      f i (PlaneTree.child T (i.val + 1)) ∂Measure.dirac PlaneTree.leaf) = 0 := by
  simpa [PlaneTree.firstChildStructure] using PlaneTree.firstChildStructure.lintegral_degree_children_product
    (Measure.dirac PlaneTree.leaf) 1 0 (by simp [PlaneTree.firstChildStructure]) 1 f hf

#print axioms FirstChildStructure.source_induction_expectation_identities
#print axioms FirstChildStructure.source_first_split_integral
#print axioms FirstChildStructure.sourceInductionIntegrand_expectation_eq_cond
#print axioms FirstChildStructure.induction_normalizing_ratio
#print axioms FirstChildStructure.positive_degree_measure_of_fixedPoint
#print axioms FirstChildStructure.lintegral_children_product_cond
#print axioms FirstChildStructure.restrict_childrenLaw_of_fixedPoint
