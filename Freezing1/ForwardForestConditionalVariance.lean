module

public import Freezing1.ForwardForestConditionalMean
public import Freezing1.TaggedPopulationSlotCenteredMoments

/-! Actual conditional second moment given the whole past and complete bare forest. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

theorem componentMaximum_le_active_card_add_one (q : State) (a : ℕ) :
    componentMaximum q a ≤ q.active.card + 1 := by
  unfold componentMaximum
  apply Finset.sup_le
  intro r _
  unfold componentPopulationWithRoot
  exact (Finset.card_insert_le r (componentActive q a r)).trans
    (Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) 1)

theorem rootPopulation_le_forestComponentMaximum {m a : ℕ} {F : State}
    (htags : TaggedPopulation.TagsIn (Finset.range m) (taggedPopulation F a)) (r : ℕ) :
    TaggedPopulation.rootPopulation (taggedPopulation F a) r ≤ forestComponentMaximum F a m := by
  by_cases hz : TaggedPopulation.rootPopulation (taggedPopulation F a) r = 0
  · rw [hz]
    exact Nat.zero_le _
  · have hpos : 0 < ((taggedPopulation F a).filter fun v => v.1 = r).card := Nat.pos_of_ne_zero hz
    obtain ⟨v, hv⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
    obtain ⟨hv, hr⟩ := Multiset.mem_filter.mp hv
    have hroot : r ∈ Finset.range m := hr ▸ htags v hv
    have hle : TaggedPopulation.rootPopulation (taggedPopulation F a) r ≤
        TaggedPopulation.rootPopulationWithRoot (taggedPopulation F a) r := Nat.le_add_right _ _
    exact hle.trans (Finset.le_sup hroot)

theorem markedMeanObservation_ae_bounds (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (G : State → Finset ℕ) (hG : ∀ s, HasHistory x a s → G s ⊆ s.active)
    (hm : (activeCount x a).toNat ≤ a + 1) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ q ∂treeLaw x b,
      0 ≤ markedMeanObservation G a (activeCount x a).toNat hm t (pastBareForest x a q) ∧
      markedMeanObservation G a (activeCount x a).toNat hm t (pastBareForest x a q) ≤ (b : ℝ) + 1 := by
  filter_upwards [treeLaw_hasHistory x b hb] with q hq
  have hc := Finset.card_le_card (rootMarks_subset hq hb hab G hG)
  rw [rootMarks_card, Finset.card_range] at hc
  have hN : blockTallCount q a b t ≤ q.active.card := by
    unfold blockTallCount
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (congrArg Finset.card (cutRoots_eq_active_of_phaseData hq.current))
  have hNb : (blockTallCount q a b t : ℝ) ≤ (b : ℝ) + 1 := by
    exact_mod_cast hN.trans (active_card_le_time_succ hq.current.valid)
  unfold markedMeanObservation pastBareForest
  rw [bareForestTallCount_actual hq hb a _ hm ht]
  constructor
  · positivity
  · by_cases hm0 : (activeCount x a).toNat = 0
    · simp only [hm0, Nat.cast_zero, div_zero, zero_mul]
      positivity
    · have hmpos : 0 < ((activeCount x a).toNat : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
      have hratio : ((G (truncateAt q a)).card : ℝ) / (activeCount x a).toNat ≤ 1 :=
        (div_le_one hmpos).mpr (by exact_mod_cast hc)
      exact (mul_le_of_le_one_left (Nat.cast_nonneg _) hratio).trans hNb

theorem markedTallCount_rematching_centered_average_le (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (G : State → Finset ℕ) (hG : ∀ s, HasHistory x a s → G s ⊆ s.active)
    (hm : (activeCount x a).toNat ≤ a + 1) {t : ℝ} (ht : 0 ≤ t) :
    let M := fun q => markedMeanObservation G a (activeCount x a).toNat hm t (pastBareForest x a q)
    ∀ᵐ q ∂treeLaw x b,
      (Fintype.card (Equiv.Perm (Fin (activeCount x a).toNat)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (activeCount x a).toNat),
          ((markedTallCount G a t (rematchState x a b σ q) : ℝ) - M (rematchState x a b σ q)) ^ 2 ≤
        (componentMaximum q a : ℝ) * M q := by
  dsimp only
  let M := fun q => markedMeanObservation G a (activeCount x a).toNat hm t (pastBareForest x a q)
  have hacts : ∀ᵐ q ∂treeLaw x b, ∀ σ : Equiv.Perm (Fin (activeCount x a).toNat),
      truncateAt (rematchState x a b σ q) a = truncateAt q a ∧
      slotForest (rematchState x a b σ q) a =
        (slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ) :=
    ae_all_iff.mpr (fun σ => (rematchState_ae_spec x hab hb σ).mono (fun _ h => h.2))
  have hobs : ∀ᵐ q ∂treeLaw x b, ∀ σ : Equiv.Perm (Fin (activeCount x a).toNat),
      pastBareForest x a (rematchState x a b σ q) = pastBareForest x a q :=
    ae_all_iff.mpr (fun σ => pastBareForest_rematchState x hab hb σ)
  filter_upwards [treeLaw_hasHistory x b hb, treeLaw_slotForest_tagsIn x hab hb, hacts, hobs,
    markedTallCount_rematching_average x hab hb G hG hm ht] with q hq htags hactsq hobsq hmean
  have hmarks := rootMarks_subset hq hb hab G hG
  have hcap : ∀ r : ℕ, (TaggedPopulation.rootPopulation (taggedPopulation (slotForest q a) a) r : ℝ) ≤
      componentMaximum q a := by
    intro r
    have hh := rootPopulation_le_forestComponentMaximum htags r
    have hcard := cutRoots_card_eq_activeCount hq hb hab
    rw [← hcard, forestComponentMaximum_slotForest hq hb a] at hh
    exact_mod_cast hh
  have hfun : (fun σ : Equiv.Perm (Fin (activeCount x a).toNat) =>
      (markedTallCount G a t (rematchState x a b σ q) : ℝ)) =
      (fun σ => (TaggedPopulation.goodTall
        (TaggedPopulation.relabel (rootSlotPermutation (activeCount x a).toNat σ)
          (taggedPopulation (slotForest q a) a)) (rootMarks G a q) t : ℝ)) := by
    funext σ
    exact congrArg Nat.cast (markedTallCount_eq_of_root_relabel G a t _
      (fun i hi => rootSlotPermutation_bounded _ σ i (by omega)) (hactsq σ).1 (hactsq σ).2)
  have hmeanIntegral : (∫ σ, (markedTallCount G a t (rematchState x a b σ q) : ℝ)
      ∂uniformPermutationLaw (Fin (activeCount x a).toNat)) = M q := by
    rw [integral_uniformPermutation_fintype]
    exact hmean
  have hvar : variance (fun σ => (markedTallCount G a t (rematchState x a b σ q) : ℝ))
      (uniformPermutationLaw (Fin (activeCount x a).toNat)) ≤ (componentMaximum q a : ℝ) * M q := by
    have hv := TaggedPopulation.variance_goodTall_slot_le htags (rootMarks G a q) t hcap
    rw [← hfun, hmeanIntegral] at hv
    exact hv
  rw [variance_eq_integral measurable_from_top.aemeasurable, hmeanIntegral] at hvar
  calc
    _ = ∫ σ, ((markedTallCount G a t (rematchState x a b σ q) : ℝ) - M (rematchState x a b σ q)) ^ 2
        ∂uniformPermutationLaw (Fin (activeCount x a).toNat) :=
      (integral_uniformPermutation_fintype (fun σ : Equiv.Perm (Fin (activeCount x a).toNat) =>
        ((markedTallCount G a t (rematchState x a b σ q) : ℝ) - M (rematchState x a b σ q)) ^ 2)).symm
    _ = ∫ σ, ((markedTallCount G a t (rematchState x a b σ q) : ℝ) - M q) ^ 2
        ∂uniformPermutationLaw (Fin (activeCount x a).toNat) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun σ => by simp only [M, hobsq σ])
    _ ≤ _ := hvar

/-- Source 14/07/19hb in centered form. The center is the actual conditional
mean already proved in `condExp_markedTallCount`, and the full bare forest is
included in the conditioning. -/
theorem condExp_markedTallCount_centered_sq_le (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) (G : State → Finset ℕ)
    (hG : ∀ s, HasHistory x a s → G s ⊆ s.active) {t : ℝ} (ht : 0 ≤ t) :
    let E := fun q => ((G (truncateAt q a)).card : ℝ) / (activeCount x a).toNat * blockTallCount q a b t
    ∀ᵐ q ∂treeLaw x b,
      (treeLaw x b)[(fun r => ((markedTallCount G a t r : ℝ) - E r) ^ 2) |
        MeasurableSpace.comap (pastBareForest x a) inferInstance] q ≤ (componentMaximum q a : ℝ) * E q := by
  dsimp only
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab : (a : ℕ∞) ≤ b).trans hb
  have hm : (activeCount x a).toNat ≤ a + 1 := by
    have hnon := activeCount_nonneg_of_le_extinctionTime haτ
    have hu := activeCount_le_plusCount_add_one x a
    have hp := plusCount_le x a
    omega
  let O := pastBareForest x a
  let f := fun q => (markedTallCount G a t q : ℝ)
  let M := markedMeanObservation G a (activeCount x a).toNat hm t
  let Y := fun q => (f q - M (O q)) ^ 2
  let H : State × RootErasedForest (activeCount x a).toNat → ℝ :=
    fun z => (bareForestComponentMaximum a (activeCount x a).toNat hm z.2 : ℝ) * M z
  have hO : Measurable O := measurable_from_top
  have hT (σ : Equiv.Perm (Fin (activeCount x a).toNat)) :
      MeasurePreserving (rematchState x a b σ) (treeLaw x b) (treeLaw x b) :=
    ⟨measurable_from_top, map_treeLaw_rematchState x hab hb σ⟩
  have hobs (σ : Equiv.Perm (Fin (activeCount x a).toNat)) :
      (fun q => O (rematchState x a b σ q)) =ᵐ[treeLaw x b] O := pastBareForest_rematchState x hab hb σ
  have hMbound := markedMeanObservation_ae_bounds x hab hb G hG hm ht
  have hYint : Integrable Y (treeLaw x b) := by
    apply Integrable.of_bound measurable_from_top.aestronglyMeasurable ((2 * ((b : ℝ) + 1)) ^ 2)
    filter_upwards [hMbound, treeLaw_valid x b] with q hmq hq
    have hX0 : 0 ≤ f q := Nat.cast_nonneg _
    have hXb : f q ≤ (b : ℝ) + 1 := by
      change (markedTallCount G a t q : ℝ) ≤ (b : ℝ) + 1
      exact_mod_cast (markedTallCount_le_active_card G a t q).trans (active_card_le_time_succ hq)
    have habs : |f q - M (O q)| ≤ 2 * ((b : ℝ) + 1) := by
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg hX0, abs_of_nonneg hmq.1]
      linarith only [hXb, hmq.2]
    change ‖(f q - M (O q)) ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr habs
  have hHval : ∀ᵐ q ∂treeLaw x b, H (O q) = (componentMaximum q a : ℝ) * M (O q) := by
    filter_upwards [treeLaw_hasHistory x b hb] with q hq
    dsimp only [H, O, pastBareForest]
    rw [bareForestComponentMaximum_actual hq hb hab hm]
  have hHint : Integrable (fun q => H (O q)) (treeLaw x b) := by
    apply Integrable.of_bound measurable_from_top.aestronglyMeasurable (((b : ℝ) + 2) * ((b : ℝ) + 1))
    filter_upwards [hMbound, treeLaw_valid x b, hHval] with q hmq hq hHq
    have hCb : (componentMaximum q a : ℝ) ≤ (b : ℝ) + 2 := by
      exact_mod_cast (componentMaximum_le_active_card_add_one q a).trans
        (Nat.add_le_add_right (active_card_le_time_succ hq) 1)
    rw [hHq, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hmq.1)]
    exact mul_le_mul hCb hmq.2 hmq.1 (by positivity)
  have hHmeas : Measurable H := by
    have hc : Measurable (fun F : RootErasedForest (activeCount x a).toNat =>
        (bareForestComponentMaximum a (activeCount x a).toNat hm F : ℝ)) := measurable_from_top
    exact (hc.comp measurable_snd).mul (measurable_markedMeanObservation G a _ hm t)
  have hOc : @Measurable State (State × RootErasedForest (activeCount x a).toNat)
      (MeasurableSpace.comap O inferInstance) inferInstance O := measurable_iff_comap_le.mpr le_rfl
  have hHsm : StronglyMeasurable[MeasurableSpace.comap O inferInstance] (fun q => H (O q)) :=
    (hHmeas.comp hOc).stronglyMeasurable
  have hHfix := condExp_of_stronglyMeasurable hO.comap_le hHsm hHint
  have hfinite := condExp_finite_invariant_average hO Finset.univ Finset.univ_nonempty
    (rematchState x a b) (fun σ _ => hT σ) (fun σ _ => hobs σ) hYint
  have hiavg : Integrable (fun q =>
      (Fintype.card (Equiv.Perm (Fin (activeCount x a).toNat)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (activeCount x a).toNat), Y (rematchState x a b σ q)) (treeLaw x b) :=
    (integrable_finsetSum Finset.univ (fun σ _ => (hT σ).integrable_comp_of_integrable hYint)).const_mul _
  have hle : (fun q =>
      (Fintype.card (Equiv.Perm (Fin (activeCount x a).toNat)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (activeCount x a).toNat), Y (rematchState x a b σ q)) ≤ᵐ[treeLaw x b]
      (fun q => H (O q)) := by
    filter_upwards [markedTallCount_rematching_centered_average_le x hab hb G hG hm ht, hHval]
      with q hq hHq
    rw [hHq]
    exact hq
  have hcondLe : (treeLaw x b)[Y | MeasurableSpace.comap O inferInstance] ≤ᵐ[treeLaw x b]
      (fun q => H (O q)) := by
    have hfinite' : (treeLaw x b)[(fun q =>
        (Fintype.card (Equiv.Perm (Fin (activeCount x a).toNat)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin (activeCount x a).toNat), Y (rematchState x a b σ q)) |
        MeasurableSpace.comap O inferInstance] =ᵐ[treeLaw x b]
        (treeLaw x b)[Y | MeasurableSpace.comap O inferInstance] := by
      simpa only [Finset.card_univ] using hfinite
    have hmono := condExp_mono (m := MeasurableSpace.comap O inferInstance) hiavg hHint hle
    filter_upwards [hfinite', hmono] with q hq hineq
    rw [hq, hHfix] at hineq
    exact hineq
  have hMeanVal : (fun q => M (O q)) =ᵐ[treeLaw x b]
      (fun q => ((G (truncateAt q a)).card : ℝ) / (activeCount x a).toNat * blockTallCount q a b t) := by
    filter_upwards [treeLaw_hasHistory x b hb] with q hq
    dsimp only [M, O, markedMeanObservation, pastBareForest]
    rw [bareForestTallCount_actual hq hb a _ hm ht]
  have hYeq : Y =ᵐ[treeLaw x b] (fun q =>
      ((markedTallCount G a t q : ℝ) -
        ((G (truncateAt q a)).card : ℝ) / (activeCount x a).toNat * blockTallCount q a b t) ^ 2) := by
    filter_upwards [hMeanVal] with q hq
    dsimp only [Y, f]
    rw [hq]
  filter_upwards [hcondLe, condExp_congr_ae (m := MeasurableSpace.comap O inferInstance) hYeq,
    hHval, hMeanVal] with q hq hCE hHq hMq
  rw [← hCE]
  exact hq.trans_eq (by rw [hHq, hMq])

end Freezing1.Forward
