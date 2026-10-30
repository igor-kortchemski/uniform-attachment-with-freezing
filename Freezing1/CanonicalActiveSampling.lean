module

public import Freezing1.CanonicalUniformSampling
public import Freezing1.ForwardAbsorption

/-! Conditional uniform sampling of active vertices under canonical coordinates. -/

@[expose] public section

namespace Freezing1.CanonicalTree

open Filter MeasureTheory
open scoped Classical

def reverseActiveVertices (F : Reverse.Forest) : Finset (ℕ ⊕ ℕ) :=
  F.vertices.filter (fun v => reverseLabel v = none)

theorem uniform_reverse_active_coordinates {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    (Measure.uniformOfFinset (reverseActiveVertices F.forest)).map F.edgeTime =
      Measure.uniformOfFinset (reverseState F).active := by
  apply map_uniformOfFinset_of_injOn
  · exact measurable_of_countable _
  · intro u hu v hv he
    exact hinj u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 he

theorem uniform_reverse_active_height {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    (Measure.uniformOfFinset (reverseState F).active).map (reverseState F).height =
      (Measure.uniformOfFinset (reverseActiveVertices F.forest)).map F.forest.depth := by
  rw [← uniform_reverse_active_coordinates hinj,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  apply Measure.map_congr
  have hs : ∀ᵐ v ∂Measure.uniformOfFinset (reverseActiveVertices F.forest),
      v ∈ reverseActiveVertices F.forest := by
    rw [ae_iff]
    simp [Measure.uniformOfFinset_apply]
  filter_upwards [hs] with v hv
  exact (reverseState_vertex_data hinj (Finset.mem_filter.mp hv).1).2.1

/-- The original forward active-height law is uniform active sampling in
the actual reverse tree, on every nonabsorbed horizon. -/
theorem forward_uniformActiveHeightLaw_eq_reverse (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) < extinctionTime x) :
    Forward.uniformActiveHeightLaw x n =
      (Reverse.treeLaw x n).bind (fun F =>
        (Measure.uniformOfFinset (reverseActiveVertices F)).map F.depth) := by
  have ha := Forward.treeLaw_active_nonempty x n hn
  rw [← reverseStateLaw_eq_forward_treeLaw x n hn.le, reverseStateLaw] at ha
  have hact : ∀ᵐ F ∂ReverseStamped.treeLaw x n, (reverseState F).active.Nonempty :=
    ae_of_ae_map (f := reverseState) measurable_from_top.aemeasurable ha
  unfold Forward.uniformActiveHeightLaw
  rw [← reverseStateLaw_eq_forward_treeLaw x n hn.le, reverseStateLaw,
    Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    ← ReverseStamped.map_treeLaw x n,
    Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [ReverseStamped.treeLaw_canonical_ids x n hn.le, hact] with F hF hA
  change (if (reverseState F).active.Nonempty then
    (Measure.uniformOfFinset (reverseState F).active).map (reverseState F).height
      else Measure.dirac 0) = _
  rw [ite_eq_left hA]
  exact uniform_reverse_active_height hF.1

end Freezing1.CanonicalTree
