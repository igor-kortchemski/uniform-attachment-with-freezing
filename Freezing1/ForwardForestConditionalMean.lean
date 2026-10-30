module

public import Freezing1.ForwardForestRematchingAction
public import Freezing1.ForwardForestPopulationLaw
public import Freezing1.ForwardForestMaximumStatistics
public import Freezing1.TaggedPopulationSlotMoments
public import Freezing1.ConditionalInvariantAverage
public import Freezing1.UniformPermutationFiniteAverage

/-! Actual expectation conditional on the whole past and complete bare forest. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def rootMarks (G : State → Finset ℕ) (a : ℕ) (q : State) : Finset ℕ :=
  (G (truncateAt q a)).image (rootNormalizer a (cutRoots q a))

noncomputable def markedTallCount (G : State → Finset ℕ) (a : ℕ) (t : ℝ) (q : State) : ℕ :=
  TaggedPopulation.goodTall (taggedPopulation (slotForest q a) a) (rootMarks G a q) t

theorem rootMarks_card (G : State → Finset ℕ) (a : ℕ) (q : State) :
    (rootMarks G a q).card = (G (truncateAt q a)).card :=
  Finset.card_image_of_injective _ (rootNormalizer a (cutRoots q a)).injective

theorem rootMarks_eq_of_prefix (G : State → Finset ℕ) (a : ℕ) {q s : State}
    (hp : truncateAt q a = truncateAt s a) : rootMarks G a q = rootMarks G a s := by
  have hr : cutRoots q a = cutRoots s a := congrArg State.active hp
  unfold rootMarks
  rw [hp, hr]

theorem markedTallCount_eq_of_root_relabel (G : State → Finset ℕ) (a : ℕ) (t : ℝ)
    {q s : State} (e : Equiv.Perm ℕ) (he : ∀ i : ℕ, a < i → e i = i)
    (hp : truncateAt s a = truncateAt q a) (hF : slotForest s a = (slotForest q a).relabel e) :
    markedTallCount G a t s = TaggedPopulation.goodTall
      (TaggedPopulation.relabel e (taggedPopulation (slotForest q a) a)) (rootMarks G a q) t := by
  unfold markedTallCount
  rw [hF, rootMarks_eq_of_prefix G a hp, taggedPopulation_relabel e _ a he]

theorem markedTallCount_eq_actual {x : SignSequence} {b : ℕ} {q : State}
    (hq : HasHistory x b q) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (G : State → Finset ℕ) (a : ℕ) (t : ℝ) :
    markedTallCount G a t q =
      (q.active.filter fun v => cutAncestor q a v ∈ G (truncateAt q a) ∧ t < (cutHeight q a v : ℝ)).card := by
  unfold markedTallCount rootMarks slotForest
  rw [taggedPopulation_relabel _ _ a (rootNormalizer_future a (cutRoots q a)),
    taggedPopulation_forestCut hq hb a, TaggedPopulation.goodTall_relabel_image,
    goodTall_taggedPopulation]

theorem rootMarks_subset {x : SignSequence} {a b : ℕ} {q : State}
    (hq : HasHistory x b q) (hb : (b : ℕ∞) ≤ extinctionTime x) (hab : a ≤ b)
    (G : State → Finset ℕ) (hG : ∀ s, HasHistory x a s → G s ⊆ s.active) :
    rootMarks G a q ⊆ Finset.range (activeCount x a).toNat := by
  have hg := hG (truncateAt q a) ((hq.historyShape hb).prefix_hasHistory hab)
  have he := rootNormalizer_image a (cutRoots q a) (fun r hr => ((mem_cutRoots q a r).mp hr).2)
  rw [cutRoots_card_eq_activeCount hq hb hab] at he
  rw [← he]
  exact Finset.image_subset_image hg

noncomputable def markedMeanObservation (G : State → Finset ℕ) (a m : ℕ)
    (hm : m ≤ a + 1) (t : ℝ) (z : State × RootErasedForest m) : ℝ :=
  ((G z.1).card : ℝ) / m * bareForestTallCount a m hm t z.2

theorem measurable_markedMeanObservation (G : State → Finset ℕ) (a m : ℕ)
    (hm : m ≤ a + 1) (t : ℝ) : Measurable (markedMeanObservation G a m hm t) := by
  have hg : Measurable (fun s : State => ((G s).card : ℝ)) := measurable_from_top
  have hn : Measurable (fun F : RootErasedForest m => (bareForestTallCount a m hm t F : ℝ)) := measurable_from_top
  exact ((hg.comp measurable_fst).div_const m).mul (hn.comp measurable_snd)

theorem markedTallCount_le_active_card (G : State → Finset ℕ) (a : ℕ) (t : ℝ) (q : State) :
    markedTallCount G a t q ≤ q.active.card := by
  have hh := Multiset.card_le_card (Multiset.filter_le
    (fun v : ℕ × ℕ => v.1 ∈ rootMarks G a q ∧ t < (v.2 : ℝ))
    (taggedPopulation (slotForest q a) a))
  simpa only [markedTallCount, TaggedPopulation.goodTall, taggedPopulation_card,
    slotForest_active_card] using hh

theorem markedTallCount_integrable (x : SignSequence) (b : ℕ) (G : State → Finset ℕ) (a : ℕ) (t : ℝ) :
    Integrable (fun q => (markedTallCount G a t q : ℝ)) (treeLaw x b) := by
  apply Integrable.of_bound measurable_from_top.aestronglyMeasurable ((b : ℝ) + 1)
  filter_upwards [treeLaw_valid x b] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (markedTallCount_le_active_card G a t q).trans (active_card_le_time_succ hq)

theorem markedTallCount_rematching_average (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (G : State → Finset ℕ) (hG : ∀ s, HasHistory x a s → G s ⊆ s.active)
    (hm : (activeCount x a).toNat ≤ a + 1) {t : ℝ} (ht : 0 ≤ t) :
    (fun q => (Fintype.card (Equiv.Perm (Fin (activeCount x a).toNat)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin (activeCount x a).toNat), (markedTallCount G a t (rematchState x a b σ q) : ℝ))
      =ᵐ[treeLaw x b]
      (fun q => markedMeanObservation G a (activeCount x a).toNat hm t (pastBareForest x a q)) := by
  have hacts : ∀ᵐ q ∂treeLaw x b, ∀ σ : Equiv.Perm (Fin (activeCount x a).toNat),
      HasHistory x b (rematchState x a b σ q) ∧
      truncateAt (rematchState x a b σ q) a = truncateAt q a ∧
      slotForest (rematchState x a b σ q) a =
        (slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ) :=
    ae_all_iff.mpr (fun σ => rematchState_ae_spec x hab hb σ)
  filter_upwards [treeLaw_hasHistory x b hb, treeLaw_slotForest_tagsIn x hab hb, hacts] with q hq htags hactsq
  have hmarks := rootMarks_subset hq hb hab G hG
  have hfun : (fun σ : Equiv.Perm (Fin (activeCount x a).toNat) =>
      (markedTallCount G a t (rematchState x a b σ q) : ℝ)) =
      (fun σ => (TaggedPopulation.goodTall
        (TaggedPopulation.relabel (rootSlotPermutation (activeCount x a).toNat σ)
          (taggedPopulation (slotForest q a) a)) (rootMarks G a q) t : ℝ)) := by
    funext σ
    exact congrArg Nat.cast (markedTallCount_eq_of_root_relabel G a t _
      (fun i hi => rootSlotPermutation_bounded _ σ i (by omega)) (hactsq σ).2.1 (hactsq σ).2.2)
  calc
    _ = ∫ σ, (markedTallCount G a t (rematchState x a b σ q) : ℝ)
        ∂uniformPermutationLaw (Fin (activeCount x a).toNat) := by
      exact (integral_uniformPermutation_fintype
        (fun σ : Equiv.Perm (Fin (activeCount x a).toNat) =>
          (markedTallCount G a t (rematchState x a b σ q) : ℝ))).symm
    _ = ∫ σ, (TaggedPopulation.goodTall
        (TaggedPopulation.relabel (rootSlotPermutation (activeCount x a).toNat σ)
          (taggedPopulation (slotForest q a) a)) (rootMarks G a q) t : ℝ)
        ∂uniformPermutationLaw (Fin (activeCount x a).toNat) := by
      exact congrArg (fun f : Equiv.Perm (Fin (activeCount x a).toNat) → ℝ =>
        ∫ σ, f σ ∂uniformPermutationLaw (Fin (activeCount x a).toNat)) hfun
    _ = ((rootMarks G a q).card : ℝ) / (activeCount x a).toNat *
        TaggedPopulation.totalTall (taggedPopulation (slotForest q a) a) t := by
      exact TaggedPopulation.integral_goodTall_slot htags (rootMarks G a q) hmarks t
    _ = _ := by
      rw [rootMarks_card]
      unfold markedMeanObservation pastBareForest
      rw [bareForestTallCount_bareSlotOrbit _ a _ hm ht]
      rfl

/-- Source A51's conditional mean, for any genuine subset of old active
vertices. The complete bare forest is included in the conditioning. -/
theorem condExp_markedTallCount (x : SignSequence) {a b : ℕ} (hab : a ≤ b)
    (hb : (b : ℕ∞) ≤ extinctionTime x) (G : State → Finset ℕ)
    (hG : ∀ s, HasHistory x a s → G s ⊆ s.active) {t : ℝ} (ht : 0 ≤ t) :
    (treeLaw x b)[(fun q => (markedTallCount G a t q : ℝ)) |
      MeasurableSpace.comap (pastBareForest x a) inferInstance] =ᵐ[treeLaw x b]
      (fun q => ((G (truncateAt q a)).card : ℝ) / (activeCount x a).toNat * blockTallCount q a b t) := by
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
  have hO : Measurable O := measurable_from_top
  have hf : Integrable f (treeLaw x b) := markedTallCount_integrable x b G a t
  have hT (σ : Equiv.Perm (Fin (activeCount x a).toNat)) :
      MeasurePreserving (rematchState x a b σ) (treeLaw x b) (treeLaw x b) :=
    ⟨measurable_from_top, map_treeLaw_rematchState x hab hb σ⟩
  have hobs (σ : Equiv.Perm (Fin (activeCount x a).toNat)) :
      (fun q => O (rematchState x a b σ q)) =ᵐ[treeLaw x b] O := pastBareForest_rematchState x hab hb σ
  have havg := markedTallCount_rematching_average x hab hb G hG hm ht
  have hfinite := condExp_finite_invariant_average hO Finset.univ Finset.univ_nonempty
    (rematchState x a b) (fun σ _ => hT σ) (fun σ _ => hobs σ) hf
  have hiavg : Integrable (fun q =>
      (Fintype.card (Equiv.Perm (Fin (activeCount x a).toNat)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (activeCount x a).toNat), f (rematchState x a b σ q)) (treeLaw x b) :=
    (integrable_finsetSum Finset.univ (fun σ _ => (hT σ).integrable_comp_of_integrable hf)).const_mul _
  have hiM : Integrable (fun q => M (O q)) (treeLaw x b) := hiavg.congr havg
  have hOc : @Measurable State (State × RootErasedForest (activeCount x a).toNat)
      (MeasurableSpace.comap O inferInstance) inferInstance O := measurable_iff_comap_le.mpr le_rfl
  have hsm : StronglyMeasurable[MeasurableSpace.comap O inferInstance] (fun q => M (O q)) :=
    ((measurable_markedMeanObservation G a _ hm t).comp hOc).stronglyMeasurable
  have hfix := condExp_of_stronglyMeasurable hO.comap_le hsm hiM
  have hmean : (treeLaw x b)[f | MeasurableSpace.comap O inferInstance] =ᵐ[treeLaw x b]
      (fun q => M (O q)) := by
    calc
      _ =ᵐ[treeLaw x b] (treeLaw x b)[(fun q =>
          (Fintype.card (Equiv.Perm (Fin (activeCount x a).toNat)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin (activeCount x a).toNat), f (rematchState x a b σ q)) |
          MeasurableSpace.comap O inferInstance] := by simpa only [Finset.card_univ] using hfinite.symm
      _ =ᵐ[treeLaw x b] (treeLaw x b)[(fun q => M (O q)) | MeasurableSpace.comap O inferInstance] :=
        condExp_congr_ae havg
      _ =ᵐ[treeLaw x b] _ := Eventually.of_forall (congrFun hfix)
  filter_upwards [hmean, treeLaw_hasHistory x b hb] with q hq hhist
  rw [hq]
  unfold M O markedMeanObservation pastBareForest
  rw [bareForestTallCount_actual hhist hb a _ hm ht]

end Freezing1.Forward
