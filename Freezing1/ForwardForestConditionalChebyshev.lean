module

public import Freezing1.ForwardForestConditionalChainVariance
public import Freezing1.ConditionalRelativeChebyshev

/-! Source A53: conditional Chebyshev under the actual full-forest observation. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

theorem goodSet_count_integrable (x : SignSequence) (n C k₀ k : ℕ) (t : ℝ) :
    Integrable (fun q => ((goodSet q C k₀ k t).card : ℝ)) (treeLaw x n) := by
  apply Integrable.of_bound measurable_from_top.aestronglyMeasurable ((n : ℝ) + 1)
  filter_upwards [treeLaw_valid x n] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Finset.card_le_card (goodSet_subset q C k₀ k t)).trans
    (active_card_le_time_succ hq)

/-- All conditional Chebyshev integrability obligations for the actual count
are discharged from its true finite population bound. -/
theorem goodSet_condExp_square_integrable {B : Type*} [MeasurableSpace B]
    (x : SignSequence) (n C k₀ k : ℕ) (t : ℝ) (O : State → B) :
    let X := fun q => ((goodSet q C k₀ k t).card : ℝ)
    let E := (treeLaw x n)[X | MeasurableSpace.comap O inferInstance]
    Integrable (fun q => (E q) ^ 2) (treeLaw x n) ∧
      Integrable (fun q => (X q - E q) ^ 2) (treeLaw x n) := by
  dsimp only
  let X := fun q => ((goodSet q C k₀ k t).card : ℝ)
  let E := (treeLaw x n)[X | MeasurableSpace.comap O inferInstance]
  have hO : Measurable O := measurable_from_top
  have hXint : Integrable X (treeLaw x n) := goodSet_count_integrable x n C k₀ k t
  have hXb : ∀ᵐ q ∂treeLaw x n, 0 ≤ X q ∧ X q ≤ (n : ℝ) + 1 := by
    filter_upwards [treeLaw_valid x n] with q hq
    refine ⟨Nat.cast_nonneg _, ?_⟩
    change ((goodSet q C k₀ k t).card : ℝ) ≤ (n : ℝ) + 1
    exact_mod_cast (Finset.card_le_card (goodSet_subset q C k₀ k t)).trans
      (active_card_le_time_succ hq)
  have hE0 : 0 ≤ᵐ[treeLaw x n] E := condExp_nonneg (hXb.mono (fun _ hq => hq.1))
  have hEb : E ≤ᵐ[treeLaw x n] fun _ => (n : ℝ) + 1 := by
    have hh := condExp_mono (m := MeasurableSpace.comap O inferInstance) hXint
      (integrable_const ((n : ℝ) + 1)) (hXb.mono (fun _ hq => hq.2))
    simpa only [condExp_const hO.comap_le] using hh
  constructor
  · apply Integrable.of_bound measurable_from_top.aestronglyMeasurable (((n : ℝ) + 1) ^ 2)
    filter_upwards [hE0, hEb] with q hq0 hqb
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ hq0 (by positivity)).mpr hqb
  · apply Integrable.of_bound measurable_from_top.aestronglyMeasurable ((2 * ((n : ℝ) + 1)) ^ 2)
    filter_upwards [hXb, hE0, hEb] with q hXq hq0 hqb
    have habs : |X q - E q| ≤ 2 * ((n : ℝ) + 1) := by
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg hXq.1, abs_of_nonneg hq0]
      linarith only [hXq.2, hqb]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr habs

/-- Conditional relative Chebyshev for the actual source count, at every
relative deviation. In particular $\theta=1/2$ gives the printed half-mean
bound with coefficient four. -/
theorem condExp_goodSet_relative_lower_given_forest (x : SignSequence)
    {C k₀ k : ℕ} (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x) {t : ℝ} (ht : 0 ≤ t)
    {θ : ℝ} (hθ : 0 < θ) :
    let X := fun q => ((goodSet q C k₀ (k + 1) t).card : ℝ)
    let E := (treeLaw x (C ^ (k + 1)))[X |
      MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance]
    ∀ᵐ q ∂treeLaw x (C ^ (k + 1)), 0 < E q →
      (treeLaw x (C ^ (k + 1)))[relativeLowerIndicator X E θ |
        MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q ≤
          (componentMaximum q (C ^ k) : ℝ) / (θ ^ 2 * E q) := by
  dsimp only
  have hO : Measurable (pastBareForest x (C ^ k)) := measurable_from_top
  have hi := goodSet_condExp_square_integrable x (C ^ (k + 1)) C k₀ (k + 1) t
    (pastBareForest x (C ^ k))
  exact condExp_relativeLowerIndicator_le hO.comap_le measurable_from_top stronglyMeasurable_condExp
    hi.1 hi.2 hθ (condVar_goodSet_succ_given_forest x hC hk hb ht)

/-- Corrected source Chebyshev step, conditioning on the whole earlier tree
and bare forest. The center is the actual conditional mean, not an inserted
prediction or a mean premise. -/
theorem condExp_goodSet_growth_failure_given_forest (x : SignSequence)
    {C k₀ k : ℕ} (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x) {t : ℝ} (ht : 0 ≤ t)
    {target : ℝ} (hTarget : 0 < target) :
    let X := fun q => ((goodSet q C k₀ (k + 1) t).card : ℝ)
    let E := (treeLaw x (C ^ (k + 1)))[X |
      MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance]
    ∀ᵐ q ∂treeLaw x (C ^ (k + 1)), 3 * target ≤ E q →
      (treeLaw x (C ^ (k + 1)))[(fun r => if X r < 2 * target then (1 : ℝ) else 0) |
        MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q ≤
          3 * (componentMaximum q (C ^ k) : ℝ) / target := by
  dsimp only
  let X := fun q => ((goodSet q C k₀ (k + 1) t).card : ℝ)
  let E := (treeLaw x (C ^ (k + 1)))[X |
    MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance]
  have hO : Measurable (pastBareForest x (C ^ k)) := measurable_from_top
  have hi := goodSet_condExp_square_integrable x (C ^ (k + 1)) C k₀ (k + 1) t
    (pastBareForest x (C ^ k))
  have hE2 : Integrable (fun q => (E q) ^ 2) (treeLaw x (C ^ (k + 1))) := by
    exact hi.1
  have hY : Integrable (fun q => (X q - E q) ^ 2) (treeLaw x (C ^ (k + 1))) := by
    exact hi.2
  exact condExp_growthIndicator_le hO.comap_le measurable_from_top stronglyMeasurable_condExp
    hE2 hY (condVar_goodSet_succ_given_forest x hC hk hb ht) hTarget
    (ae_of_all _ (fun _ => Nat.cast_nonneg _))

/-- On the source favorable event, the true population bound $S_a\le a+1$
gives a factor-three mean. This repairs the printed factor-four argument
without changing the doubling target or the summable error order. -/
theorem condExp_goodSet_doubling_on_favorable_forest (x : SignSequence)
    {C k₀ k : ℕ} (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : 3 ≤ C ^ k) {t : ℝ} (ht : 0 ≤ t) {target : ℝ} (hTarget : 0 < target) :
    ∀ᵐ q ∂treeLaw x (C ^ (k + 1)),
      target ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ) →
      4 * (C ^ k : ℝ) ≤ (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) →
      (treeLaw x (C ^ (k + 1)))[(fun r =>
          if ((goodSet r C k₀ (k + 1) t).card : ℝ) < 2 * target then (1 : ℝ) else 0) |
        MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q ≤
          3 * (componentMaximum q (C ^ k) : ℝ) / target := by
  have hab : C ^ k ≤ C ^ (k + 1) := pow_le_pow_right₀ hC (Nat.le_succ k)
  have h3 : (3 : ℝ) ≤ C ^ k := by exact_mod_cast ha
  have hSbound : (activeCount x (C ^ k) : ℝ) ≤ (C ^ k : ℝ) + 1 := by
    have hu := activeCount_le_plusCount_add_one x (C ^ k)
    have hp := plusCount_le x (C ^ k)
    have hpI : (plusCount x (C ^ k) : ℤ) ≤ ((C ^ k : ℕ) : ℤ) := by exact_mod_cast hp
    have hI : activeCount x (C ^ k) ≤ ((C ^ k : ℕ) : ℤ) + 1 :=
      hu.trans (Int.add_le_add_right hpI 1)
    exact_mod_cast hI
  have hstep := condExp_goodSet_growth_failure_given_forest x hC hk hb ht hTarget
  have hmean := condExp_goodSet_succ_given_forest x hC hk hb ht
  filter_upwards [hstep, hmean, treeLaw_historyShape x (C ^ (k + 1)) hb]
    with q hstepq hmeanq hq hG hN
  have hprefix := hq.prefix_phaseData hab
  have hGleS : ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ) ≤
      (activeCount x (C ^ k) : ℝ) := by
    have hh := Finset.card_le_card (goodSet_subset (truncateAt q (C ^ k)) C k₀ k t)
    have hc := hprefix.count
    have hhR : ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ) ≤
        ((truncateAt q (C ^ k)).active.card : ℝ) := by exact_mod_cast hh
    have hcR : (((truncateAt q (C ^ k)).active.card : ℕ) : ℝ) =
        (activeCount x (C ^ k) : ℝ) := by exact_mod_cast hc
    exact hhR.trans_eq hcR
  have hSpos : 0 < (activeCount x (C ^ k) : ℝ) := hTarget.trans_le (hG.trans hGleS)
  apply hstepq
  rw [hmeanq]
  apply (le_div_iff₀ hSpos).mpr
  have hfirst : 3 * target * (activeCount x (C ^ k) : ℝ) ≤ target * (4 * (C ^ k : ℝ)) := by
    have hs := mul_le_mul_of_nonneg_left hSbound (show 0 ≤ 3 * target by positivity)
    nlinarith only [hs, mul_nonneg hTarget.le (sub_nonneg.mpr h3)]
  exact hfirst.trans (mul_le_mul hG hN (by positivity) (Nat.cast_nonneg _))

theorem condExp_goodSet_doubling_on_source_event (x : SignSequence)
    {C k₀ k : ℕ} (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : 3 ≤ C ^ k) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ q ∂treeLaw x (C ^ (k + 1)),
      (2 : ℝ) ^ k ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ) →
      4 * (C ^ k : ℝ) ≤ (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) →
      (componentMaximum q (C ^ k) : ℝ) ≤ (k : ℝ) ^ 3 →
      (treeLaw x (C ^ (k + 1)))[(fun r =>
          if ((goodSet r C k₀ (k + 1) t).card : ℝ) < (2 : ℝ) ^ (k + 1) then (1 : ℝ) else 0) |
        MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q ≤
          3 * (k : ℝ) ^ 3 / (2 : ℝ) ^ k := by
  have h := condExp_goodSet_doubling_on_favorable_forest x hC hk hb ha ht
    (target := (2 : ℝ) ^ k) (by positivity)
  filter_upwards [h] with q hq hG hN hM
  have hbound := hq hG hN
  have he : 2 * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
  rw [he] at hbound
  exact hbound.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hM (by norm_num)) (by positivity))

end Freezing1.Forward
