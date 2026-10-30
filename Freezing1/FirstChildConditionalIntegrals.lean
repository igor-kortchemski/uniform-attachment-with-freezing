module

public import Freezing1.GeometricBranching
public import Mathlib.Probability.Independence.Integration

/-! The source's nonnegative conditional expectation factorization, including
unbounded test functions, from the actual finite-child law. -/

@[expose] public section

namespace Freezing1.FirstChildStructure

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

variable {T : Type*} [MeasurableSpace T]

theorem lintegral_product_pi {I : Type*} [Fintype I] (μ : Measure T) [IsProbabilityMeasure μ]
    (f : I → T → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ z : I → T, ∏ i, f i (z i) ∂Measure.pi (fun _ : I => μ)) =
      ∏ i, ∫⁻ t, f i t ∂μ := by
  have hind := iIndepFun_pi (μ := fun _ : I => μ) (X := f) (fun i => (hf i).aemeasurable)
  calc
    _ = ∏ i, ∫⁻ z : I → T, f i (z i) ∂Measure.pi (fun _ : I => μ) :=
      lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
        (fun (i : I) (z : I → T) => f i (z i)) hind
        (fun i => (hf i).comp (measurable_pi_apply i))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact (measurePreserving_eval (fun _ : I => μ) i).lintegral_comp (hf i)

theorem lintegral_children_product_cond (D : FirstChildStructure T)
    (μ : Measure T) [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft)
    (k : ℕ) (hk : μ {t | D.degree t = k} ≠ 0)
    (f : Fin k → T → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ t, ∏ i : Fin k, f i (D.child t i.val) ∂μ[|{t | D.degree t = k}]) =
      ∏ i : Fin k, ∫⁻ t, f i t ∂μ := by
  have hvec : Measurable (fun t (i : Fin k) => D.child t i.val) :=
    Measurable.of_eval fun i => D.measurable_child i.val
  have hprod : Measurable (fun z : Fin k → T => ∏ i : Fin k, f i (z i)) :=
    Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
  calc
    _ = ∫⁻ z : Fin k → T, ∏ i, f i (z i)
        ∂(μ[|{t | D.degree t = k}]).map (fun t (i : Fin k) => D.child t i.val) :=
      (lintegral_map hprod hvec).symm
    _ = _ := by
      rw [D.conditional_childrenLaw_of_fixedPoint μ q r hμ k hk]
      exact lintegral_product_pi μ f hf

/-- The unnormalized finite-child law remains valid when the conditioning
event is null. This avoids assigning a probability law to a null event. -/
theorem restrict_childrenLaw_of_fixedPoint (D : FirstChildStructure T)
    (μ : Measure T) [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft) (k : ℕ) :
    (μ.restrict {t | D.degree t = k}).map (fun t (i : Fin k) => D.child t i.val) =
      μ {t | D.degree t = k} • Measure.pi (fun _ : Fin k => μ) := by
  by_cases hk : μ {t | D.degree t = k} = 0
  · rw [Measure.restrict_eq_zero.mpr hk]
    simp [hk]
  · have hh := congrArg (fun ν : Measure (Fin k → T) => μ {t | D.degree t = k} • ν)
      (D.conditional_childrenLaw_of_fixedPoint μ q r hμ k hk)
    have hvec : Measurable (fun t (i : Fin k) => D.child t i.val) :=
      Measurable.of_eval fun i => D.measurable_child i.val
    rw [ProbabilityTheory.cond, Measure.map_smul _ hvec.aemeasurable, smul_smul,
      ENNReal.mul_inv_cancel hk (measure_ne_top _ _), one_smul] at hh
    exact hh

theorem lintegral_degree_children_product (D : FirstChildStructure T)
    (μ : Measure T) [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft)
    (k : ℕ) (f : Fin k → T → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ t in {t | D.degree t = k}, ∏ i : Fin k, f i (D.child t i.val) ∂μ) =
      (q * r ^ k) * ∏ i : Fin k, ∫⁻ t, f i t ∂μ := by
  have hvec : Measurable (fun t (i : Fin k) => D.child t i.val) :=
    Measurable.of_eval fun i => D.measurable_child i.val
  have hprod : Measurable (fun z : Fin k → T => ∏ i : Fin k, f i (z i)) :=
    Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
  calc
    _ = ∫⁻ z : Fin k → T, ∏ i, f i (z i)
        ∂(μ.restrict {t | D.degree t = k}).map (fun t (i : Fin k) => D.child t i.val) :=
      (lintegral_map hprod hvec).symm
    _ = _ := by
      rw [D.restrict_childrenLaw_of_fixedPoint μ q r hμ k, lintegral_smul_measure,
        D.degree_measure_of_fixedPoint μ q r hμ k, lintegral_product_pi μ f hf]
      rfl

end Freezing1.FirstChildStructure
