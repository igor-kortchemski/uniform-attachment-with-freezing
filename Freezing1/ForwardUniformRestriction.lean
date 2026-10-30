module

public import Freezing1.FiniteUniformPairs
public import Freezing1.ForwardPrefixGeometry
public import Freezing1.CanonicalPairSampling
public import Freezing1.ForwardUniformHeight

/-!
# Uniform terminal samples captured by an earlier vertex set

Both conditional laws concern actual forward tree observations. Earlier
vertices keep their heights and graph distances along the same history;
the mass of later vertices is the only error in the comparison.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped ENNReal Classical

namespace CanonicalTree

theorem forwardPairKernel_eq_product (s : Forward.State) :
    forwardPairKernel s =
      ((Measure.uniformOfFinset s.vertices).prod (Measure.uniformOfFinset s.vertices)).map
        (fun q : ℕ × ℕ => (s.height q.1, s.height q.2, s.graph.dist q.1 q.2)) := by
  rw [Measure.prod_eq_of_sfinite, Measure.map_bind
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  unfold forwardPairKernel
  congr 1
  funext u
  rw [Measure.map_map (measurable_of_countable _) measurable_prodMk_left]
  rfl

theorem forwardPairKernel_restriction_bound {s t : Forward.State}
    (hs : s.vertices.Nonempty) (hst : s.vertices ⊆ t.vertices)
    (hh : ∀ v ∈ s.vertices, t.height v = s.height v)
    (hd : ∀ u ∈ s.vertices, ∀ v ∈ s.vertices, t.graph.dist u v = s.graph.dist u v)
    (A : Set (ℕ × ℕ × ℕ)) :
    |(forwardPairKernel t).real A - (forwardPairKernel s).real A| ≤
      2 * (((t.vertices.card : ℝ) - s.vertices.card) / t.vertices.card) := by
  rw [forwardPairKernel_eq_product, forwardPairKernel_eq_product]
  apply FiniteUniform.uniform_pair_observation_difference_le hs hst _ _ _ A
    (Set.to_countable A).measurableSet
  intro u hu v hv
  rw [hh u hu, hh v hv, hd u hu v hv]

end CanonicalTree

namespace Forward

theorem vertexHeightKernel_restriction_bound {s t : State}
    (hs : s.vertices.Nonempty) (hst : s.vertices ⊆ t.vertices)
    (hh : ∀ v ∈ s.vertices, t.height v = s.height v) (A : Set ℕ) :
    (|(vertexHeightKernel t).real A - (vertexHeightKernel s).real A|) ≤
      ((t.vertices.card : ℝ) - s.vertices.card) / t.vertices.card := by
  have ht := hs.mono hst
  change |(if t.vertices.Nonempty then (Measure.uniformOfFinset t.vertices).map t.height
      else Measure.dirac 0).real A -
    (if s.vertices.Nonempty then (Measure.uniformOfFinset s.vertices).map s.height
      else Measure.dirac 0).real A| ≤ _
  rw [ite_eq_left ht, ite_eq_left hs]
  exact FiniteUniform.uniformOfFinset_observation_difference_le hs hst t.height s.height hh A
    (Set.to_countable A).measurableSet

end Forward

namespace ForwardInfiniteHistory

open Forward CanonicalTree

theorem fullLaw_uniform_samples_restriction_bound (x : SignSequence) (a k : ℕ) (hak : a ≤ k)
    (A : Set ℕ) (B : Set (ℕ × ℕ × ℕ)) :
    ∀ᵐ H ∂fullLaw x,
      |(vertexHeightKernel (H k)).real A - (vertexHeightKernel (H a)).real A| ≤
          (((H k).vertices.card : ℝ) - (H a).vertices.card) / (H k).vertices.card ∧
      |(forwardPairKernel (H k)).real B - (forwardPairKernel (H a)).real B| ≤
          2 * ((((H k).vertices.card : ℝ) - (H a).vertices.card) / (H k).vertices.card) := by
  filter_upwards [fullLaw_old_geometry x a k hak, fullLaw_valid x] with H hg hv
  have hne : (H a).vertices.Nonempty := ⟨0, (hv a).root_mem⟩
  exact ⟨vertexHeightKernel_restriction_bound hne hg.1 hg.2.1 A,
    forwardPairKernel_restriction_bound hne hg.1 hg.2.1 hg.2.2 B⟩

end ForwardInfiniteHistory
end Freezing1
