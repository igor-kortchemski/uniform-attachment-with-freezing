module

public import Freezing1.FirstChildConditionalIntegrals

/-! The literal nonnegative expectation identities in the source's
first-child induction. Conditioning is normalized only on positive events. -/

@[expose] public section

namespace Freezing1.FirstChildStructure

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

set_option backward.isDefEq.respectTransparency false

variable {T : Type*} [MeasurableSpace T]

theorem positive_degree_measure_of_fixedPoint (D : FirstChildStructure T)
    (μ : Measure T) [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft) :
    μ {t | 0 < D.degree t} = r := by
  have hm : MeasurableSet {t | 0 < D.degree t} :=
    D.measurable_degree (by trivial)
  have hp : D.graft ⁻¹' {t | 0 < D.degree t} = Set.univ := by
    ext ab
    simp [D.degree_graft]
  conv_lhs => rw [hμ]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hm, Measure.map_apply D.measurable_graft hm, hp]
  simp [D.degree_leaf]

noncomputable def sourceInductionIntegrand (D : FirstChildStructure T) (μ : Measure T)
    (r : ℝ≥0∞) (n : ℕ) (f : Fin (n + 1) → T → ℝ≥0∞) (t : T) : ℝ≥0∞ :=
  ({t | D.degree t = n}.indicator
    (fun t => ∏ i : Fin n, f i.succ (D.child t i.val)) t) *
    (r / μ {t | D.degree t = n + 1})

theorem measurable_sourceInductionIntegrand (D : FirstChildStructure T) (μ : Measure T)
    (r : ℝ≥0∞) (n : ℕ) (f : Fin (n + 1) → T → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    Measurable (D.sourceInductionIntegrand μ r n f) := by
  apply Measurable.mul_const
  apply Measurable.indicator _ (D.measurable_degree (measurableSet_singleton n))
  exact Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (D.measurable_child i.val))

theorem degree_measure_succ (D : FirstChildStructure T) (μ : Measure T) [IsProbabilityMeasure μ]
    (q r : ℝ≥0∞) (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft)
    (n : ℕ) : μ {t | D.degree t = n + 1} = μ {t | D.degree t = n} * r := by
  rw [D.degree_measure_of_fixedPoint μ q r hμ (n + 1),
    D.degree_measure_of_fixedPoint μ q r hμ n, pow_succ]
  ac_rfl

theorem induction_normalizing_ratio (D : FirstChildStructure T) (μ : Measure T)
    [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft)
    (n : ℕ) (hk : μ {t | D.degree t = n + 1} ≠ 0) :
    μ {t | D.degree t = n} * (r / μ {t | D.degree t = n + 1}) = 1 := by
  rw [div_eq_mul_inv, ← mul_assoc, ← D.degree_measure_succ μ q r hμ n]
  exact ENNReal.mul_inv_cancel hk (measure_ne_top _ _)

theorem lintegral_sourceInductionIntegrand (D : FirstChildStructure T)
    (μ : Measure T) [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft)
    (n : ℕ) (hk : μ {t | D.degree t = n + 1} ≠ 0)
    (f : Fin (n + 1) → T → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ t, D.sourceInductionIntegrand μ r n f t ∂μ) =
      ∏ i : Fin n, ∫⁻ t, f i.succ t ∂μ := by
  have hm : Measurable (fun t => ∏ i : Fin n, f i.succ (D.child t i.val)) :=
    Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (D.measurable_child i.val))
  have hA : MeasurableSet {t | D.degree t = n} :=
    D.measurable_degree (measurableSet_singleton n)
  unfold sourceInductionIntegrand
  rw [lintegral_mul_const (r / μ {t | D.degree t = n + 1}) (hm.indicator hA),
    lintegral_indicator hA,
    D.lintegral_degree_children_product μ q r hμ n (fun i => f i.succ) (fun i => hf i.succ),
    ← D.degree_measure_of_fixedPoint μ q r hμ n]
  calc
    _ = (μ {t | D.degree t = n} * (r / μ {t | D.degree t = n + 1})) *
        ∏ i : Fin n, ∫⁻ t, f i.succ t ∂μ := by ac_rfl
    _ = _ := by rw [D.induction_normalizing_ratio μ q r hμ n hk, one_mul]

theorem sourceInductionIntegrand_expectation_eq_cond (D : FirstChildStructure T)
    (μ : Measure T) [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft)
    (n : ℕ) (hk : μ {t | D.degree t = n + 1} ≠ 0)
    (f : Fin (n + 1) → T → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ t, D.sourceInductionIntegrand μ r n f t ∂μ) =
      ∫⁻ t, ∏ i : Fin n, f i.succ (D.child t i.val) ∂μ[|{t | D.degree t = n}] := by
  have hn : μ {t | D.degree t = n} ≠ 0 := by
    intro hz
    rw [D.degree_measure_succ μ q r hμ n, hz, zero_mul] at hk
    exact hk rfl
  rw [D.lintegral_sourceInductionIntegrand μ q r hμ n hk f hf,
    D.lintegral_children_product_cond μ q r hμ n hn (fun i => f i.succ) (fun i => hf i.succ)]

theorem source_induction_factorization (D : FirstChildStructure T)
    (μ : Measure T) [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft)
    (n : ℕ) (hk : μ {t | D.degree t = n + 1} ≠ 0)
    (f : Fin (n + 1) → T → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ t, ∏ i : Fin (n + 1), f i (D.child t i.val) ∂μ[|{t | D.degree t = n + 1}]) =
      (∫⁻ t, f 0 t ∂μ) * ∫⁻ t, D.sourceInductionIntegrand μ r n f t ∂μ := by
  rw [D.lintegral_children_product_cond μ q r hμ (n + 1) hk f hf,
    D.lintegral_sourceInductionIntegrand μ q r hμ n hk f hf, Fin.prod_univ_succ]

theorem source_first_split_integral (D : FirstChildStructure T)
    (μ : Measure T) [IsProbabilityMeasure μ] (q r : ℝ≥0∞)
    (hμ : μ = q • Measure.dirac D.leaf + r • (μ.prod μ).map D.graft)
    (rest : T → T) (hrest : Measurable rest)
    (hsplit : (μ[|{t | 0 < D.degree t}]).map (fun t => (D.child t 0, rest t)) = μ.prod μ)
    (n : ℕ) (hk : μ {t | D.degree t = n + 1} ≠ 0)
    (f : Fin (n + 1) → T → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ t, ∏ i : Fin (n + 1), f i (D.child t i.val) ∂μ[|{t | D.degree t = n + 1}]) =
      ∫⁻ t, f 0 (D.child t 0) * D.sourceInductionIntegrand μ r n f (rest t)
        ∂μ[|{t | 0 < D.degree t}] := by
  have hg := D.measurable_sourceInductionIntegrand μ r n f hf
  have hfun : Measurable (fun ab : T × T => f 0 ab.1 * D.sourceInductionIntegrand μ r n f ab.2) :=
    ((hf 0).comp measurable_fst).mul (hg.comp measurable_snd)
  calc
    _ = (∫⁻ t, f 0 t ∂μ) * ∫⁻ t, D.sourceInductionIntegrand μ r n f t ∂μ :=
      D.source_induction_factorization μ q r hμ n hk f hf
    _ = ∫⁻ ab : T × T, f 0 ab.1 * D.sourceInductionIntegrand μ r n f ab.2 ∂μ.prod μ :=
      (lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable).symm
    _ = _ := by
      rw [← hsplit, lintegral_map hfun ((D.measurable_child 0).prodMk hrest)]

end Freezing1.FirstChildStructure
