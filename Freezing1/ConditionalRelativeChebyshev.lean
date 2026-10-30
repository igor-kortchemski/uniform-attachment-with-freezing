module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! Conditional Chebyshev with a genuinely random measurable center. -/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def relativeLowerIndicator {Ω : Type*} (X E : Ω → ℝ) (θ : ℝ) (ω : Ω) : ℝ :=
  if 0 < E ω ∧ X ω < (1 - θ) * E ω then 1 else 0

theorem relativeLowerIndicator_bounds {Ω : Type*} (X E : Ω → ℝ) (θ : ℝ) (ω : Ω) :
    0 ≤ relativeLowerIndicator X E θ ω ∧ relativeLowerIndicator X E θ ω ≤ 1 := by
  unfold relativeLowerIndicator
  split_ifs <;> norm_num

/-- A positive observation-measurable center may be used in conditional
Chebyshev; the inequality is obtained before dividing by that center. -/
theorem condExp_relativeLowerIndicator_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X E M : Ω → ℝ} (hX : @Measurable Ω ℝ mΩ inferInstance X) (hE : StronglyMeasurable[m] E)
    (hE2 : Integrable (fun ω => (E ω) ^ 2) μ)
    (hY : Integrable (fun ω => (X ω - E ω) ^ 2) μ)
    {θ : ℝ} (hθ : 0 < θ)
    (hvar : μ[(fun ω => (X ω - E ω) ^ 2) | m] ≤ᵐ[μ] fun ω => M ω * E ω) :
    ∀ᵐ ω ∂μ, 0 < E ω →
      μ[relativeLowerIndicator X E θ | m] ω ≤ M ω / (θ ^ 2 * E ω) := by
  let I := relativeLowerIndicator X E θ
  have hEa : @Measurable Ω ℝ mΩ inferInstance E := (hE.mono hm).measurable
  have hI : @Measurable Ω ℝ mΩ inferInstance I := by
    exact measurable_const.ite ((measurableSet_lt measurable_const hEa).inter
      (measurableSet_lt hX (measurable_const.mul hEa))) measurable_const
  have hIb : ∀ ω, ‖I ω‖ ≤ 1 := fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (relativeLowerIndicator_bounds X E θ ω).1]
    exact (relativeLowerIndicator_bounds X E θ ω).2
  have hi : Integrable I μ := Integrable.of_bound hI.aestronglyMeasurable 1 (ae_of_all _ hIb)
  let W := fun ω => (θ * E ω) ^ 2
  have hW : StronglyMeasurable[m] W := (stronglyMeasurable_const.mul hE).pow 2
  have hw : Integrable W μ := by
    simpa only [W, mul_pow] using hE2.const_mul (θ ^ 2)
  have hwi : Integrable (W * I) μ := hw.mul_bdd hI.aestronglyMeasurable (ae_of_all _ hIb)
  have hpoint : W * I ≤ᵐ[μ] fun ω => (X ω - E ω) ^ 2 := by
    apply ae_of_all
    intro ω
    dsimp only [Pi.mul_apply, W, I, relativeLowerIndicator]
    split_ifs with h
    · have hdiff : θ * E ω ≤ -(X ω - E ω) := by linarith only [h.2]
      have h0 : 0 ≤ θ * E ω := mul_nonneg hθ.le h.1.le
      have hs := mul_self_le_mul_self h0 hdiff
      nlinarith only [hs]
    · simp only [mul_zero]
      exact sq_nonneg _
  have hpull := condExp_mul_of_stronglyMeasurable_left hW hwi hi
  have hmono := condExp_mono (m := m) hwi hY hpoint
  filter_upwards [hpull, hmono, hvar] with ω hp hmω hv hpos
  have hden : 0 < θ ^ 2 * E ω := mul_pos (sq_pos_of_pos hθ) hpos
  apply (le_div_iff₀ hden).mpr
  have hbound : (θ * E ω) ^ 2 * μ[I | m] ω ≤ M ω * E ω := by
    calc
      _ = μ[W * I | m] ω := by simpa only [Pi.mul_apply, W] using hp.symm
      _ ≤ _ := hmω.trans hv
  have hcancel : (μ[I | m] ω * (θ ^ 2 * E ω)) * E ω ≤ M ω * E ω := by
    convert hbound using 1; ring
  exact (mul_le_mul_iff_left₀ hpos).mp hcancel

/-- The corrected source growth step: a mean at least three times the old
target still controls failure to double, with constant $3M/b$. -/
theorem condExp_growthIndicator_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X E M : Ω → ℝ} (hX : @Measurable Ω ℝ mΩ inferInstance X) (hE : StronglyMeasurable[m] E)
    (hE2 : Integrable (fun ω => (E ω) ^ 2) μ)
    (hY : Integrable (fun ω => (X ω - E ω) ^ 2) μ)
    (hvar : μ[(fun ω => (X ω - E ω) ^ 2) | m] ≤ᵐ[μ] fun ω => M ω * E ω)
    {b : ℝ} (hb : 0 < b) (hM : 0 ≤ᵐ[μ] M) :
    ∀ᵐ ω ∂μ, 3 * b ≤ E ω →
      μ[(fun u => if X u < 2 * b then (1 : ℝ) else 0) | m] ω ≤ 3 * M ω / b := by
  let I : Ω → ℝ := fun u => if X u < 2 * b then 1 else 0
  let A : Set Ω := {ω | 3 * b ≤ E ω}
  have hI : @Measurable Ω ℝ mΩ inferInstance I :=
    measurable_const.ite (measurableSet_lt hX measurable_const) measurable_const
  have hi : Integrable I μ := by
    apply Integrable.of_bound hI.aestronglyMeasurable 1
    exact ae_of_all _ (fun ω => by dsimp only [I]; split_ifs <;> norm_num)
  have hA : MeasurableSet[m] A := measurableSet_le measurable_const hE.measurable
  have hAi : Integrable (A.indicator I) μ := hi.indicator (hm _ hA)
  have hrel : @Measurable Ω ℝ mΩ inferInstance (relativeLowerIndicator X E (1 / 3)) := by
    have he := (hE.mono hm).measurable
    exact measurable_const.ite ((measurableSet_lt measurable_const he).inter
      (measurableSet_lt hX (measurable_const.mul he))) measurable_const
  have hirel : Integrable (relativeLowerIndicator X E (1 / 3)) μ := by
    apply Integrable.of_bound hrel.aestronglyMeasurable 1
    exact ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (relativeLowerIndicator_bounds X E (1 / 3) ω).1]
      exact (relativeLowerIndicator_bounds X E (1 / 3) ω).2)
  have hpoint : A.indicator I ≤ᵐ[μ] relativeLowerIndicator X E (1 / 3) := by
    apply ae_of_all
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      dsimp only [I, relativeLowerIndicator]
      split_ifs with hbad hgood
      · exact le_rfl
      · have hmean : 3 * b ≤ E ω := hω
        exfalso
        apply hgood
        constructor <;> linarith only [hmean, hb, hbad]
      · exact zero_le_one
      · exact le_rfl
    · rw [Set.indicator_of_notMem hω]
      exact (relativeLowerIndicator_bounds X E (1 / 3) ω).1
  have hmono := condExp_mono (m := m) hAi hirel hpoint
  have hpull := condExp_indicator hi hA
  have hcheb := condExp_relativeLowerIndicator_le (mΩ := mΩ) hm hX hE hE2 hY
    (θ := (1 / 3 : ℝ)) (by norm_num) hvar
  filter_upwards [hmono, hpull, hcheb, hM] with ω hmω hp hc hMω hmean
  have hpos : 0 < E ω := by linarith only [hb, hmean]
  have hω : ω ∈ A := hmean
  have hbound : μ[I | m] ω ≤ M ω / ((1 / 3 : ℝ) ^ 2 * E ω) := by
    rw [Set.indicator_of_mem hω] at hp
    rw [← hp]
    exact hmω.trans (hc hpos)
  apply hbound.trans
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hpos) hb).mpr
  nlinarith only [mul_nonneg hMω (sub_nonneg.mpr hmean)]

end Freezing1
