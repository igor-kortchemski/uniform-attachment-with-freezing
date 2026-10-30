module

public import Freezing1.ForwardForestVertexMatchingMoments
public import Freezing1.ForwardForestConditionalMean
public import Freezing1.ConditionalInvariantBounds

/-! Actual conditional one-vertex probabilities given the complete bare forest. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def markedVertexIndicator (G : State → Finset ℕ) (a : ℕ) (t : ℝ) (v : ℕ) (q : State) : ℝ :=
  forestMarkedVertexIndicator (slotForest q a) a t (rootMarks G a q) v

theorem markedVertexIndicator_bounds (G : State → Finset ℕ) (a : ℕ) (t : ℝ) (v : ℕ) (q : State) :
    0 ≤ markedVertexIndicator G a t v q ∧ markedVertexIndicator G a t v q ≤ 1 :=
  forestMarkedVertexIndicator_bounds _ a t _ v

theorem markedVertexIndicator_integrable (x : SignSequence) (b : ℕ)
    (G : State → Finset ℕ) (a : ℕ) (t : ℝ) (v : ℕ) :
    Integrable (markedVertexIndicator G a t v) (treeLaw x b) := by
  apply Integrable.of_bound measurable_from_top.aestronglyMeasurable 1
  exact Eventually.of_forall (fun q => by
    rw [Real.norm_eq_abs, abs_of_nonneg (markedVertexIndicator_bounds G a t v q).1]
    exact (markedVertexIndicator_bounds G a t v q).2)

theorem markedVertexIndicator_eq_of_root_relabel (G : State → Finset ℕ) (a : ℕ) (t : ℝ) (v : ℕ)
    {q s : State} (e : Equiv.Perm ℕ) (hp : truncateAt s a = truncateAt q a)
    (hF : slotForest s a = (slotForest q a).relabel e) :
    markedVertexIndicator G a t v s =
      forestMarkedVertexIndicator ((slotForest q a).relabel e) a t (rootMarks G a q) v := by
  unfold markedVertexIndicator
  rw [hF, rootMarks_eq_of_prefix G a hp]

noncomputable def vertexMeanObservation (G : State → Finset ℕ) (a m : ℕ)
    (hm : m ≤ a + 1) (t : ℝ) (v : ℕ) (hv : a < v) (z : State × RootErasedForest m) : ℝ :=
  ((G z.1).card : ℝ) / m * bareVertexTallIndicator a m hm t v hv z.2

theorem measurable_vertexMeanObservation (G : State → Finset ℕ) (a m : ℕ)
    (hm : m ≤ a + 1) (t : ℝ) (v : ℕ) (hv : a < v) :
    Measurable (vertexMeanObservation G a m hm t v hv) := by
  have hg : Measurable (fun s : State => ((G s).card : ℝ)) := measurable_from_top
  have hn : Measurable (bareVertexTallIndicator a m hm t v hv) := measurable_from_top
  exact ((hg.comp measurable_fst).div_const m).mul (hn.comp measurable_snd)

theorem oldMark_fraction_ae_bounds (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (G : State → Finset ℕ) (hG : ∀ s, HasHistory x a s → G s ⊆ s.active) :
    ∀ᵐ q ∂treeLaw x b, 0 ≤ ((G (truncateAt q a)).card : ℝ) / (activeCount x a).toNat ∧
      ((G (truncateAt q a)).card : ℝ) / (activeCount x a).toNat ≤ 1 := by
  filter_upwards [treeLaw_hasHistory x b hb] with q hq
  have hc := Finset.card_le_card (rootMarks_subset hq hb hab G hG)
  rw [rootMarks_card, Finset.card_range] at hc
  constructor
  · positivity
  · by_cases hm0 : (activeCount x a).toNat = 0
    · simp only [hm0, Nat.cast_zero, div_zero]
      norm_num
    · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hm0)).mpr (by exact_mod_cast hc)

theorem vertexMeanObservation_ae_bounds (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (G : State → Finset ℕ) (hG : ∀ s, HasHistory x a s → G s ⊆ s.active)
    (hm : (activeCount x a).toNat ≤ a + 1) (t : ℝ) (v : ℕ) (hv : a < v) :
    ∀ᵐ q ∂treeLaw x b,
      0 ≤ vertexMeanObservation G a (activeCount x a).toNat hm t v hv (pastBareForest x a q) ∧
      vertexMeanObservation G a (activeCount x a).toNat hm t v hv (pastBareForest x a q) ≤ 1 := by
  filter_upwards [oldMark_fraction_ae_bounds x hab hb G hG] with q hq
  have ha := bareVertexTallIndicator_bounds a _ hm t v hv
    (bareSlotOrbit (activeCount x a).toNat (slotForest q a))
  constructor
  · exact mul_nonneg hq.1 ha.1
  · exact (mul_le_of_le_one_left ha.1 hq.2).trans ha.2

theorem markedVertexIndicator_rematching_average (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (G : State → Finset ℕ) (hG : ∀ s, HasHistory x a s → G s ⊆ s.active)
    (hm : (activeCount x a).toNat ≤ a + 1) (t : ℝ) (v : ℕ) (hv : a < v) :
    (fun q => (Fintype.card (Equiv.Perm (Fin (activeCount x a).toNat)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin (activeCount x a).toNat), markedVertexIndicator G a t v (rematchState x a b σ q))
      =ᵐ[treeLaw x b]
      (fun q => vertexMeanObservation G a (activeCount x a).toNat hm t v hv (pastBareForest x a q)) := by
  have hacts : ∀ᵐ q ∂treeLaw x b, ∀ σ : Equiv.Perm (Fin (activeCount x a).toNat),
      truncateAt (rematchState x a b σ q) a = truncateAt q a ∧
      slotForest (rematchState x a b σ q) a =
        (slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ) :=
    ae_all_iff.mpr (fun σ => (rematchState_ae_spec x hab hb σ).mono (fun _ h => h.2))
  filter_upwards [treeLaw_hasHistory x b hb, treeLaw_slotForest_tagsIn x hab hb, hacts]
    with q hq htags hactsq
  have hmarks := rootMarks_subset hq hb hab G hG
  have hfun : (fun σ : Equiv.Perm (Fin (activeCount x a).toNat) =>
      markedVertexIndicator G a t v (rematchState x a b σ q)) =
      (fun σ => forestMarkedVertexIndicator
        ((slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ)) a t (rootMarks G a q) v) := by
    funext σ
    exact markedVertexIndicator_eq_of_root_relabel G a t v _ (hactsq σ).1 (hactsq σ).2
  calc
    _ = ∫ σ, markedVertexIndicator G a t v (rematchState x a b σ q)
        ∂uniformPermutationLaw (Fin (activeCount x a).toNat) :=
      (integral_uniformPermutation_fintype (fun σ : Equiv.Perm (Fin (activeCount x a).toNat) =>
        markedVertexIndicator G a t v (rematchState x a b σ q))).symm
    _ = ∫ σ, forestMarkedVertexIndicator
        ((slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ)) a t (rootMarks G a q) v
        ∂uniformPermutationLaw (Fin (activeCount x a).toNat) :=
      congrArg (fun f : Equiv.Perm (Fin (activeCount x a).toNat) → ℝ =>
        ∫ σ, f σ ∂uniformPermutationLaw (Fin (activeCount x a).toNat)) hfun
    _ = ((rootMarks G a q).card : ℝ) / (activeCount x a).toNat * forestVertexTallIndicator (slotForest q a) a t v :=
      integral_forestMarkedVertexIndicator hm hv htags _ hmarks t
    _ = _ := by
      rw [rootMarks_card]
      unfold vertexMeanObservation pastBareForest
      rw [bareVertexTallIndicator_bareSlotOrbit]

theorem condExp_markedVertexIndicator (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (G : State → Finset ℕ) (hG : ∀ s, HasHistory x a s → G s ⊆ s.active)
    (hm : (activeCount x a).toNat ≤ a + 1) (t : ℝ) (v : ℕ) (hv : a < v) :
    (treeLaw x b)[markedVertexIndicator G a t v |
      MeasurableSpace.comap (pastBareForest x a) inferInstance] =ᵐ[treeLaw x b]
      (fun q => vertexMeanObservation G a (activeCount x a).toNat hm t v hv (pastBareForest x a q)) := by
  apply condExp_eq_of_finite_invariant_average measurable_from_top Finset.univ Finset.univ_nonempty
    (rematchState x a b) (fun σ _ => ⟨measurable_from_top, map_treeLaw_rematchState x hab hb σ⟩)
    (fun σ _ => pastBareForest_rematchState x hab hb σ)
    (markedVertexIndicator_integrable x b G a t v)
    (vertexMeanObservation G a (activeCount x a).toNat hm t v hv)
    (measurable_vertexMeanObservation G a _ hm t v hv)
  simpa only [Finset.card_univ] using markedVertexIndicator_rematching_average x hab hb G hG hm t v hv

end Freezing1.Forward
