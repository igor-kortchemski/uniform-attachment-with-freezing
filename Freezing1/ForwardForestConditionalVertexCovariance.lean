module

public import Freezing1.ForwardForestConditionalVertexMean

/-! Actual conditional negative correlation for named vertices in distinct cut components. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def vertexPairUpperObservation (G : State → Finset ℕ) (a m : ℕ)
    (hm : m ≤ a + 1) (t : ℝ) (v : ℕ) (hv : a < v) (w : ℕ) (hw : a < w)
    (z : State × RootErasedForest m) : ℝ :=
  if bareVertexSeparated a m hm v hv w hw z.2 then
    vertexMeanObservation G a m hm t v hv z * vertexMeanObservation G a m hm t w hw z
  else 1

theorem measurable_vertexPairUpperObservation (G : State → Finset ℕ) (a m : ℕ)
    (hm : m ≤ a + 1) (t : ℝ) (v : ℕ) (hv : a < v) (w : ℕ) (hw : a < w) :
    Measurable (vertexPairUpperObservation G a m hm t v hv w hw) := by
  have hd : MeasurableSet {Q : RootErasedForest m | bareVertexSeparated a m hm v hv w hw Q} := by trivial
  exact Measurable.ite (measurable_snd hd)
    ((measurable_vertexMeanObservation G a m hm t v hv).mul
      (measurable_vertexMeanObservation G a m hm t w hw)) measurable_const

theorem integral_forestMarkedVertex_pair_upper {F : State} {a m v w : ℕ}
    (hm : m ≤ a + 1) (hv : a < v) (hw : a < w)
    (htags : TaggedPopulation.TagsIn (Finset.range m) (taggedPopulation F a))
    (G : Finset ℕ) (hG : G ⊆ Finset.range m) (t : ℝ) :
    (∫ σ, forestMarkedVertexIndicator (F.relabel (rootSlotPermutation m σ)) a t G v *
      forestMarkedVertexIndicator (F.relabel (rootSlotPermutation m σ)) a t G w
      ∂uniformPermutationLaw (Fin m)) ≤
      if forestVertexSeparated F a v w then
        (((G.card : ℝ) / m) * forestVertexTallIndicator F a t v) *
          (((G.card : ℝ) / m) * forestVertexTallIndicator F a t w) else 1 := by
  by_cases hd : forestVertexSeparated F a v w
  · rw [ite_eq_left hd]
    exact (integral_forestMarkedVertexIndicator_pair_le hm hv hw htags G hG t hd).trans_eq (by ring)
  · rw [ite_eq_right hd]
    calc
      _ ≤ ∫ _σ : Equiv.Perm (Fin m), (1 : ℝ) ∂uniformPermutationLaw (Fin m) := by
        apply integral_mono (uniformPermutation_integrable _) (integrable_const 1)
        intro σ
        have hvb := forestMarkedVertexIndicator_bounds (F.relabel (rootSlotPermutation m σ)) a t G v
        have hwb := forestMarkedVertexIndicator_bounds (F.relabel (rootSlotPermutation m σ)) a t G w
        exact (mul_le_of_le_one_left hwb.1 hvb.2).trans hwb.2
      _ = 1 := by simp

theorem markedVertexIndicators_rematching_average_le (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (G : State → Finset ℕ) (hG : ∀ s, HasHistory x a s → G s ⊆ s.active)
    (hm : (activeCount x a).toNat ≤ a + 1) (t : ℝ) (v : ℕ) (hv : a < v) (w : ℕ) (hw : a < w) :
    (fun q => (Fintype.card (Equiv.Perm (Fin (activeCount x a).toNat)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin (activeCount x a).toNat),
        markedVertexIndicator G a t v (rematchState x a b σ q) *
          markedVertexIndicator G a t w (rematchState x a b σ q)) ≤ᵐ[treeLaw x b]
      (fun q => vertexPairUpperObservation G a (activeCount x a).toNat hm t v hv w hw (pastBareForest x a q)) := by
  have hacts : ∀ᵐ q ∂treeLaw x b, ∀ σ : Equiv.Perm (Fin (activeCount x a).toNat),
      truncateAt (rematchState x a b σ q) a = truncateAt q a ∧
      slotForest (rematchState x a b σ q) a =
        (slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ) :=
    ae_all_iff.mpr (fun σ => (rematchState_ae_spec x hab hb σ).mono (fun _ h => h.2))
  filter_upwards [treeLaw_hasHistory x b hb, treeLaw_slotForest_tagsIn x hab hb, hacts]
    with q hq htags hactsq
  have hmarks := rootMarks_subset hq hb hab G hG
  have hfun : (fun σ : Equiv.Perm (Fin (activeCount x a).toNat) =>
      markedVertexIndicator G a t v (rematchState x a b σ q) * markedVertexIndicator G a t w (rematchState x a b σ q)) =
      (fun σ => forestMarkedVertexIndicator ((slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ))
          a t (rootMarks G a q) v *
        forestMarkedVertexIndicator ((slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ))
          a t (rootMarks G a q) w) := by
    funext σ
    rw [markedVertexIndicator_eq_of_root_relabel G a t v _ (hactsq σ).1 (hactsq σ).2,
      markedVertexIndicator_eq_of_root_relabel G a t w _ (hactsq σ).1 (hactsq σ).2]
  calc
    _ = ∫ σ, markedVertexIndicator G a t v (rematchState x a b σ q) *
        markedVertexIndicator G a t w (rematchState x a b σ q)
        ∂uniformPermutationLaw (Fin (activeCount x a).toNat) :=
      (integral_uniformPermutation_fintype (fun σ : Equiv.Perm (Fin (activeCount x a).toNat) =>
        markedVertexIndicator G a t v (rematchState x a b σ q) *
          markedVertexIndicator G a t w (rematchState x a b σ q))).symm
    _ = ∫ σ, forestMarkedVertexIndicator ((slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ))
          a t (rootMarks G a q) v *
        forestMarkedVertexIndicator ((slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ))
          a t (rootMarks G a q) w ∂uniformPermutationLaw (Fin (activeCount x a).toNat) :=
      congrArg (fun f : Equiv.Perm (Fin (activeCount x a).toNat) → ℝ =>
        ∫ σ, f σ ∂uniformPermutationLaw (Fin (activeCount x a).toNat)) hfun
    _ ≤ if forestVertexSeparated (slotForest q a) a v w then
        (((rootMarks G a q).card : ℝ) / (activeCount x a).toNat * forestVertexTallIndicator (slotForest q a) a t v) *
          (((rootMarks G a q).card : ℝ) / (activeCount x a).toNat * forestVertexTallIndicator (slotForest q a) a t w) else 1 :=
      integral_forestMarkedVertex_pair_upper hm hv hw htags _ hmarks t
    _ = _ := by
      rw [rootMarks_card]
      unfold vertexPairUpperObservation vertexMeanObservation pastBareForest
      simp only [bareVertexSeparated_bareSlotOrbit, bareVertexTallIndicator_bareSlotOrbit]

theorem condExp_markedVertexIndicators_pair_le (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (G : State → Finset ℕ) (hG : ∀ s, HasHistory x a s → G s ⊆ s.active)
    (hm : (activeCount x a).toNat ≤ a + 1) (t : ℝ) (v : ℕ) (hv : a < v) (w : ℕ) (hw : a < w) :
    ∀ᵐ q ∂treeLaw x b, forestVertexSeparated (slotForest q a) a v w →
      (treeLaw x b)[(fun r => markedVertexIndicator G a t v r * markedVertexIndicator G a t w r) |
        MeasurableSpace.comap (pastBareForest x a) inferInstance] q ≤
      (treeLaw x b)[markedVertexIndicator G a t v | MeasurableSpace.comap (pastBareForest x a) inferInstance] q *
        (treeLaw x b)[markedVertexIndicator G a t w | MeasurableSpace.comap (pastBareForest x a) inferInstance] q := by
  let O := pastBareForest x a
  let H := vertexPairUpperObservation G a (activeCount x a).toNat hm t v hv w hw
  have hO : Measurable O := measurable_from_top
  have hT (σ : Equiv.Perm (Fin (activeCount x a).toNat)) :
      MeasurePreserving (rematchState x a b σ) (treeLaw x b) (treeLaw x b) :=
    ⟨measurable_from_top, map_treeLaw_rematchState x hab hb σ⟩
  have hobs (σ : Equiv.Perm (Fin (activeCount x a).toNat)) :
      (fun q => O (rematchState x a b σ q)) =ᵐ[treeLaw x b] O := pastBareForest_rematchState x hab hb σ
  have hf : Integrable (fun q => markedVertexIndicator G a t v q * markedVertexIndicator G a t w q) (treeLaw x b) := by
    apply Integrable.of_bound measurable_from_top.aestronglyMeasurable 1
    apply Eventually.of_forall
    intro q
    have hvb := markedVertexIndicator_bounds G a t v q
    have hwb := markedVertexIndicator_bounds G a t w q
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hvb.1 hwb.1)]
    exact (mul_le_of_le_one_left hwb.1 hvb.2).trans hwb.2
  have hHi : Integrable (fun q => H (O q)) (treeLaw x b) := by
    apply Integrable.of_bound measurable_from_top.aestronglyMeasurable 1
    filter_upwards [vertexMeanObservation_ae_bounds x hab hb G hG hm t v hv,
      vertexMeanObservation_ae_bounds x hab hb G hG hm t w hw] with q hvq hwq
    dsimp only [H, vertexPairUpperObservation]
    split
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hvq.1 hwq.1)]
      exact (mul_le_of_le_one_left hwq.1 hvq.2).trans hwq.2
    · norm_num
  have hCE : (treeLaw x b)[(fun q => markedVertexIndicator G a t v q * markedVertexIndicator G a t w q) |
      MeasurableSpace.comap O inferInstance] ≤ᵐ[treeLaw x b] (fun q => H (O q)) := by
    apply condExp_le_of_finite_invariant_average hO Finset.univ Finset.univ_nonempty
      (rematchState x a b) (fun σ _ => hT σ) (fun σ _ => hobs σ) hf H
      (measurable_vertexPairUpperObservation G a _ hm t v hv w hw) hHi
    simpa only [Finset.card_univ] using markedVertexIndicators_rematching_average_le x hab hb G hG hm t v hv w hw
  filter_upwards [hCE, condExp_markedVertexIndicator x hab hb G hG hm t v hv,
    condExp_markedVertexIndicator x hab hb G hG hm t w hw] with q hq hvq hwq
  intro hd
  have hdObs : bareVertexSeparated a (activeCount x a).toNat hm v hv w hw
      (bareSlotOrbit (activeCount x a).toNat (slotForest q a)) :=
    (bareVertexSeparated_bareSlotOrbit _ a _ hm v hv w hw).mpr hd
  rw [hvq, hwq]
  exact hq.trans_eq (by simp only [H, vertexPairUpperObservation, O, pastBareForest, hdObs, ite_true])

end Freezing1.Forward
