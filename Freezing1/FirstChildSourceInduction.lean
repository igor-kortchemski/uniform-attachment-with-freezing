module

public import Freezing1.FirstChildInductionIntegrals
public import Freezing1.FirstChildFixedPoint

/-! Source A27 with its genuine conditional first-child split as input.
The finite-child fixed point and all normalizing identities are conclusions. -/

@[expose] public section

namespace Freezing1.FirstChildStructure

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

variable {T : Type*} [MeasurableSpace T]

theorem source_induction_expectation_identities (D : FirstChildStructure T)
    (rest : T → T) (hrest : Measurable rest)
    (hzero : ∀ t, D.degree t = 0 → t = D.leaf)
    (hinverse : ∀ t, 0 < D.degree t → D.graft (D.child t 0, rest t) = t)
    (μ : Measure T) [IsProbabilityMeasure μ]
    (hsplit : μ {t | 0 < D.degree t} ≠ 0 →
      (μ[|{t | 0 < D.degree t}]).map (fun t => (D.child t 0, rest t)) = μ.prod μ)
    (n : ℕ) (hk : μ {t | D.degree t = n + 1} ≠ 0)
    (f : Fin (n + 1) → T → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    let g := D.sourceInductionIntegrand μ (μ {t | 0 < D.degree t}) n f
    ((∫⁻ t, ∏ i : Fin (n + 1), f i (D.child t i.val) ∂μ[|{t | D.degree t = n + 1}]) =
      ∫⁻ t, f 0 (D.child t 0) * g (rest t) ∂μ[|{t | 0 < D.degree t}]) ∧
    ((∫⁻ t, g t ∂μ) =
      ∫⁻ t, ∏ i : Fin n, f i.succ (D.child t i.val) ∂μ[|{t | D.degree t = n}]) ∧
    ((∫⁻ t, ∏ i : Fin (n + 1), f i (D.child t i.val) ∂μ[|{t | D.degree t = n + 1}]) =
      (∫⁻ t, f 0 t ∂μ) * ∫⁻ t, g t ∂μ) := by
  let q := μ {t | D.degree t = 0}
  let r := μ {t | 0 < D.degree t}
  have hμ := D.fixedPoint_of_conditional_split rest hrest hzero hinverse μ q r rfl rfl hsplit
  have hr : r ≠ 0 := by
    intro hz
    have hle : μ {t | D.degree t = n + 1} ≤ r := by
      apply measure_mono
      intro t ht
      change D.degree t = n + 1 at ht
      change 0 < D.degree t
      omega
    rw [hz] at hle
    exact hk (le_antisymm hle bot_le)
  dsimp only
  exact ⟨D.source_first_split_integral μ q r hμ rest hrest (hsplit hr) n hk f hf,
    D.sourceInductionIntegrand_expectation_eq_cond μ q r hμ n hk f hf,
    D.source_induction_factorization μ q r hμ n hk f hf⟩

end Freezing1.FirstChildStructure
