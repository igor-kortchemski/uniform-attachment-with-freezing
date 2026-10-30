module

public import Freezing1.ConstructionEquivalence
public import Freezing1.ForwardUniformHeight

/-!
# Uniform sampling is preserved by the canonical vertex coordinates

Finite injective relabeling preserves uniform measures, including the empty
case of the generic lemma. Actual tree applications separately prove their
vertex sets nonempty. No independence between sampled heights is asserted.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped Classical ENNReal

theorem map_uniformOfFinset_of_injOn {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [decβ : DecidableEq β]
    (s : Finset α) (f : α → β) (hf : Measurable f) (hinj : Set.InjOn f s) :
    (Measure.uniformOfFinset s).map f = Measure.uniformOfFinset (s.image f) := by
  ext E hE
  rw [Measure.map_apply hf hE, Measure.uniformOfFinset_apply, Measure.uniformOfFinset_apply]
  have hfilter : (s.image f).filter (fun y => y ∈ E) =
      (s.filter fun a => f a ∈ E).image f := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, he⟩
      exact ⟨a, ⟨ha, he⟩, rfl⟩
    · rintro ⟨a, ⟨ha, he⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, he⟩
  rw [hfilter, Finset.card_image_iff.mpr hinj,
    Finset.card_image_iff.mpr (hinj.mono (by intro a ha; exact (Finset.mem_filter.mp ha).1))]
  rfl

namespace CanonicalTree

theorem uniform_reverse_coordinates {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    (Measure.uniformOfFinset F.forest.vertices).map F.edgeTime =
      Measure.uniformOfFinset (reverseState F).vertices := by
  simpa only [reverseState, reverse] using
    map_uniformOfFinset_of_injOn (decβ := instDecidableEqNat)
      F.forest.vertices F.edgeTime (by fun_prop) hinj

theorem uniform_reverse_height {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    (Measure.uniformOfFinset (reverseState F).vertices).map (reverseState F).height =
      (Measure.uniformOfFinset F.forest.vertices).map F.forest.depth := by
  rw [← uniform_reverse_coordinates hinj,
    Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  have hae : ∀ᵐ v ∂Measure.uniformOfFinset F.forest.vertices, v ∈ F.forest.vertices := by
    rw [ae_iff]
    simp [Measure.uniformOfFinset_apply]
  filter_upwards [hae] with v hv
  exact (reverseState_vertex_data hinj hv).2.1

/-- The existing forward uniform-height law is exactly uniform sampling in
the actual reverse tree. Active and frozen vertices are both included. -/
theorem forward_uniformHeightLaw_eq_reverse (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    Forward.uniformHeightLaw x n =
      (Reverse.treeLaw x n).bind (fun F => (Measure.uniformOfFinset F.vertices).map F.depth) := by
  unfold Forward.uniformHeightLaw
  rw [← reverseStateLaw_eq_forward_treeLaw x n hn, reverseStateLaw,
    Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    ← ReverseStamped.map_treeLaw x n,
    Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [ReverseStamped.treeLaw_canonical_ids x n hn,
    treeLaw_reverseState_historyShape x n hn] with F hF hs
  have hne : (reverseState F).vertices.Nonempty :=
    ⟨0, (hs.schedule.vertex_iff 0).mpr (Or.inl rfl)⟩
  change (if (reverseState F).vertices.Nonempty then
    (Measure.uniformOfFinset (reverseState F).vertices).map (reverseState F).height
    else Measure.dirac 0) = _
  rw [ite_eq_left hne]
  exact uniform_reverse_height hF.1

end CanonicalTree
end Freezing1
