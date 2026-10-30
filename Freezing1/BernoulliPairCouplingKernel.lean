module

public import Freezing1.ReversePairHeightKernel
public import Freezing1.ReversePairHeightBlocks
public import Freezing1.UniformPairDistance
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! Augment the genuine history transition with the source independent coin. -/

@[expose] public section

namespace Freezing1.BernoulliPairCoupling

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

abbrev Base := ReverseHistory.History

structure StepSample where
  history : Base
  auxiliary : ℕ

instance : MeasurableSpace StepSample := ⊤
instance : DiscreteMeasurableSpace StepSample := ⟨fun _ => trivial⟩

/-- Fill an unobserved auxiliary coin independently when the actual first
increment is one, or when the roots already coincide. In the remaining case
the auxiliary is the actual second increment. -/
noncomputable def augmentLaw (μ : Measure Base) (already : Prop) (X Z : Base → ℕ)
    (q : unitInterval) : Measure StepSample :=
  μ.bind fun H => if already ∨ X H = 1 then
    (bernoulliMeasure (1 : ℕ) 0 q).map (fun ξ => (⟨H, ξ⟩ : StepSample))
  else Measure.dirac ⟨H, Z H⟩

instance augmentLaw_probability (μ : Measure Base) [IsProbabilityMeasure μ]
    (already : Prop) (X Z : Base → ℕ) (q : unitInterval) :
    IsProbabilityMeasure (augmentLaw μ already X Z q) := by
  unfold augmentLaw
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  apply ae_of_all
  intro H
  split_ifs <;> infer_instance

/-- Augmentation never changes the actual complete history marginal. -/
theorem augmentLaw_map_history (μ : Measure Base) (already : Prop) (X Z : Base → ℕ)
    (q : unitInterval) : (augmentLaw μ already X Z q).map StepSample.history = μ := by
  rw [augmentLaw, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  calc
    _ = μ.bind (fun H => Measure.dirac H) := by
      congr 1
      funext H
      split_ifs
      · rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
        simp
      · simp
    _ = _ := Measure.bind_dirac

theorem bernoulli_support {μ : Measure Base} {X : Base → ℕ} {p : unitInterval}
    (hX : HasLaw X (bernoulliMeasure (1 : ℕ) 0 p) μ) :
    ∀ᵐ H ∂μ, X H = 0 ∨ X H = 1 := by
  apply ae_of_ae_map (f := X) (p := fun j : ℕ => j = 0 ∨ j = 1) hX.aemeasurable
  rw [hX.map_eq]
  apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
  simp

theorem bernoulli_test_integral {μ : Measure Base} {X : Base → ℕ} {p : unitInterval}
    (hX : HasLaw X (bernoulliMeasure (1 : ℕ) 0 p) μ) (f : ℕ → ℝ) :
    (∫ H, f (X H) ∂μ) = (p : ℝ) * f 1 + (1 - (p : ℝ)) * f 0 := by
  have h := hX.integral_comp (measurable_of_countable f).aestronglyMeasurable
  simpa only [Function.comp_def, integral_bernoulliMeasure, smul_eq_mul] using h

/-- The exact one-step factorization. It uses genuine exclusive increments
and the scalar relation $(1-p)q=p$, not a conditional independence premise. -/
theorem augmentLaw_integral_product (μ : Measure Base) [IsProbabilityMeasure μ]
    (already : Prop) (X Z : Base → ℕ) (p q : unitInterval)
    (hX : HasLaw X (bernoulliMeasure (1 : ℕ) 0 p) μ)
    (hZ : HasLaw Z (bernoulliMeasure (1 : ℕ) 0 p) μ)
    (hex : ¬already → ∀ᵐ H ∂μ, X H = 0 ∨ Z H = 0)
    (hpq : (1 - (p : ℝ)) * (q : ℝ) = p)
    (f g : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1) (hg : ∀ j, 0 ≤ g j ∧ g j ≤ 1) :
    (∫ s, f (X s.history) * g s.auxiliary ∂augmentLaw μ already X Z q) =
      ((p : ℝ) * f 1 + (1 - (p : ℝ)) * f 0) *
        ((q : ℝ) * g 1 + (1 - (q : ℝ)) * g 0) := by
  let G := (q : ℝ) * g 1 + (1 - (q : ℝ)) * g 0
  have hint : Integrable (fun s : StepSample => f (X s.history) * g s.auxiliary)
      (augmentLaw μ already X Z q) :=
    integrable_unitInterval_function _ measurable_from_top (fun s =>
      ⟨mul_nonneg (hf _).1 (hg _).1, (mul_le_mul (hf _).2 (hg _).2 (hg _).1 zero_le_one).trans_eq (one_mul _)⟩)
  rw [augmentLaw, integral_bind_of_integrable _ _ measurable_from_top hint]
  have hinner (H : Base) :
      (∫ s : StepSample, f (X s.history) * g s.auxiliary ∂
        (if already ∨ X H = 1 then (bernoulliMeasure (1 : ℕ) 0 q).map (fun ξ => (⟨H, ξ⟩ : StepSample))
          else Measure.dirac ⟨H, Z H⟩)) =
        if already ∨ X H = 1 then f (X H) * G else f (X H) * g (Z H) := by
    split_ifs
    · rw [integral_map (measurable_of_countable _).aemeasurable measurable_from_top.aestronglyMeasurable,
        integral_bernoulliMeasure]
      dsimp only [G]
      simp only [smul_eq_mul]
      ring
    · simp
  simp_rw [hinner]
  have hif : Integrable (fun H => f (X H)) μ :=
    hX.integrable_fun_comp (integrable_bernoulliMeasure _ _ _ f)
  by_cases ha : already
  · simp only [ha, true_or, ite_true]
    rw [integral_mul_const, bernoulli_test_integral hX f]
  · have heq : (fun H => if already ∨ X H = 1 then f (X H) * G else f (X H) * g (Z H)) =ᵐ[μ]
        (fun H => f 0 * g (Z H) + (if X H = 1 then (1 : ℝ) else 0) * (f 1 * G - f 0 * g 0)) := by
      filter_upwards [bernoulli_support hX, hex ha] with H hs he
      rcases hs with hs | hs
      · simp only [ha, hs, Nat.zero_ne_one, or_self, ite_false, zero_mul, add_zero]
      · have hz : Z H = 0 := by rcases he with he | he; omega; exact he
        simp only [ha, hs, hz, false_or, ite_true, one_mul]
        ring
    have hig : Integrable (fun H => g (Z H)) μ :=
      hZ.integrable_fun_comp (integrable_bernoulliMeasure _ _ _ g)
    have hiX : Integrable (fun H => if X H = 1 then (1 : ℝ) else 0) μ :=
      integrable_unitInterval_function _ measurable_from_top (fun H => by split_ifs <;> norm_num)
    rw [integral_congr_ae heq, integral_add (hig.const_mul _) (hiX.mul_const _),
      integral_const_mul, integral_mul_const, bernoulli_test_integral hZ g,
      bernoulli_test_integral hX (fun j => if j = 1 then (1 : ℝ) else 0)]
    simp only [ite_true, Nat.zero_ne_one, ite_false, mul_one, mul_zero, add_zero]
    dsimp only [G]
    linear_combination -(f 0 * (g 1 - g 0)) * hpq

/-- Exact product joint law, hence the auxiliary really is independent of
the actual first increment, with the required enlarged parameter. -/
theorem augmentLaw_map_pair (μ : Measure Base) [IsProbabilityMeasure μ]
    (already : Prop) (X Z : Base → ℕ) (p q : unitInterval)
    (hX : HasLaw X (bernoulliMeasure (1 : ℕ) 0 p) μ)
    (hZ : HasLaw Z (bernoulliMeasure (1 : ℕ) 0 p) μ)
    (hex : ¬already → ∀ᵐ H ∂μ, X H = 0 ∨ Z H = 0)
    (hpq : (1 - (p : ℝ)) * (q : ℝ) = p) :
    (augmentLaw μ already X Z q).map (fun s => (X s.history, s.auxiliary)) =
      (bernoulliMeasure (1 : ℕ) 0 p).prod (bernoulliMeasure (1 : ℕ) 0 q) := by
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro ⟨a, b⟩
  let f := fun j : ℕ => if j = a then (1 : ℝ) else 0
  let g := fun j : ℕ => if j = b then (1 : ℝ) else 0
  have hprod := augmentLaw_integral_product μ already X Z p q hX hZ hex hpq f g
    (fun _ => by dsimp only [f]; split_ifs <;> norm_num)
    (fun _ => by dsimp only [g]; split_ifs <;> norm_num)
  have hleft : (∫ s, f (X s.history) * g s.auxiliary ∂augmentLaw μ already X Z q) =
      ((augmentLaw μ already X Z q).map (fun s => (X s.history, s.auxiliary))).real {(a,b)} := by
    have he : (fun z : ℕ × ℕ => f z.1 * g z.2) = ({(a,b)} : Set (ℕ × ℕ)).indicator (fun _ => (1 : ℝ)) := by
      funext z
      rcases z with ⟨c,d⟩
      simp only [Set.indicator_apply, Set.mem_singleton_iff, Prod.mk.injEq, f, g]
      split_ifs <;> simp_all
    calc
      _ = ∫ z : ℕ × ℕ, f z.1 * g z.2 ∂(augmentLaw μ already X Z q).map
          (fun s => (X s.history, s.auxiliary)) :=
        (integral_map measurable_from_top.aemeasurable (measurable_of_countable _).aestronglyMeasurable).symm
      _ = _ := by
        rw [he, integral_indicator_const _ (measurableSet_singleton _)]
        simp only [smul_eq_mul, mul_one]
  have hright : ((bernoulliMeasure (1 : ℕ) 0 p).prod (bernoulliMeasure (1 : ℕ) 0 q)).real {(a,b)} =
      ((p : ℝ) * f 1 + (1 - (p : ℝ)) * f 0) *
        ((q : ℝ) * g 1 + (1 - (q : ℝ)) * g 0) := by
    have he : ({(a,b)} : Set (ℕ × ℕ)) = ({a} : Set ℕ) ×ˢ {b} := by ext z; simp
    have hfI : (∫ j, f j ∂bernoulliMeasure (1 : ℕ) 0 p) =
        (bernoulliMeasure (1 : ℕ) 0 p).real {a} := by
      simpa only [Set.indicator_apply, Set.mem_singleton_iff, f, smul_eq_mul, mul_one] using
        integral_indicator_const (μ := bernoulliMeasure (1 : ℕ) 0 p) (1 : ℝ) (measurableSet_singleton a)
    have hgI : (∫ j, g j ∂bernoulliMeasure (1 : ℕ) 0 q) =
        (bernoulliMeasure (1 : ℕ) 0 q).real {b} := by
      simpa only [Set.indicator_apply, Set.mem_singleton_iff, g, smul_eq_mul, mul_one] using
        integral_indicator_const (μ := bernoulliMeasure (1 : ℕ) 0 q) (1 : ℝ) (measurableSet_singleton b)
    rw [he, measureReal_prod_prod, ← hfI, ← hgI, integral_bernoulliMeasure, integral_bernoulliMeasure]
    simp only [smul_eq_mul]
  exact hleft.symm.trans (hprod.trans hright.symm)

/-- The source deterministic identity is retained on the coupled space.
The state criterion is equality before the step, including the current
coalescence boundary in the distinct-root branch. -/
theorem augmentLaw_relation (μ : Measure Base) [IsProbabilityMeasure μ]
    (already : Prop) (X Z : Base → ℕ) (p q : unitInterval)
    (hX : HasLaw X (bernoulliMeasure (1 : ℕ) 0 p) μ)
    (hsame : already → X =ᵐ[μ] Z)
    (hex : ¬already → ∀ᵐ H ∂μ, X H = 0 ∨ Z H = 0) :
    ∀ᵐ s ∂augmentLaw μ already X Z q,
      Z s.history = if already then X s.history else s.auxiliary * (1 - X s.history) := by
  rw [augmentLaw]
  apply ae_bind_of_ae measurable_from_top.aemeasurable (by trivial)
  by_cases ha : already
  · filter_upwards [hsame ha] with H hH
    rw [ite_eq_left (Or.inl ha)]
    apply (ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)).mpr
    exact ae_of_all _ (fun ξ => by simpa only [ite_eq_left ha] using hH.symm)
  · filter_upwards [bernoulli_support hX, hex ha] with H hS hE
    by_cases hx : X H = 1
    · have hz : Z H = 0 := by rcases hE with hE | hE; omega; exact hE
      rw [ite_eq_left (Or.inr hx)]
      apply (ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)).mpr
      exact ae_of_all _ (fun ξ => by simp only [ha, hx, hz, ite_false, Nat.sub_self, Nat.mul_zero])
    · have hz : X H = 0 := by rcases hS with hS | hS; exact hS; exact (hx hS).elim
      rw [ite_eq_right (not_or.mpr ⟨ha, hx⟩)]
      apply (ae_dirac_iff (by trivial)).mpr
      simp only [ha, hz, ite_false, Nat.sub_zero, Nat.mul_one]

end Freezing1.BernoulliPairCoupling
