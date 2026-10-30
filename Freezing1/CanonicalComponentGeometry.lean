module

public import Freezing1.CanonicalCutAncestor

/-!
# The forward population observable counts actual graph components

The cut ancestor is identified directly with connectivity in the forward
cut graph, under the actual forward tree law. This certifies the geometric
meaning of the population and maximum observables used in Forestjump.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped Classical

namespace Forward

theorem cutGraph_walk_support_mem (s : State) (a : ℕ) {u v : ℕ}
    (p : (cutGraph s a).Walk u v) (hu : u ∈ cutVertices s a) :
    ∀ w ∈ p.support, w ∈ cutVertices s a := by
  induction p with
  | nil => simpa using hu
  | cons h p ih =>
    intro w hw
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hu
    · exact ih h.2.1 w hw

end Forward

namespace ReverseStampedHistory

open ReverseStamped CanonicalTree

set_option backward.isDefEq.respectTransparency false in
theorem stage_reachable_iff_cutGraph {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i))
    (ho : TimestampOrder H.current) {i : ℕ} (hi : i ≤ n) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ (stage H i).forest.vertices) (hv : v ∈ (stage H i).forest.vertices) :
    (stage H i).forest.graph.Reachable u v ↔
      (Forward.cutGraph (reverseState H.current) i).Reachable
        (H.current.edgeTime u) (H.current.edgeTime v) := by
  let e := cutGraphIso hd hs ho hi
  let V := Forward.cutVertices (reverseState H.current) i
  have htu : H.current.edgeTime u ∈ V :=
    (mem_phase_iff_mem_cutVertices hd hi (phase_vertices_subset_current hd hi hu)).mp hu
  constructor
  · rintro ⟨p⟩
    let p' : (stage H i).forest.toGraph.Walk ⟨u, hu⟩ ⟨v, hv⟩ :=
      p.induce ((stage H i).forest.vertices : Set (ℕ ⊕ ℕ))
        ((stage H i).forest.walk_support_mem p hu)
    exact ⟨(p'.map e.toHom).map (SimpleGraph.Embedding.induce (V : Set ℕ)).toHom⟩
  · rintro ⟨p⟩
    have hp := Forward.cutGraph_walk_support_mem _ i p htu
    let p' := p.induce (V : Set ℕ) hp
    have hback := (p'.map e.symm.toHom).map
      (SimpleGraph.Embedding.induce ((stage H i).forest.vertices : Set (ℕ ⊕ ℕ))).toHom
    have heu : e ⟨u, hu⟩ = ⟨H.current.edgeTime u, htu⟩ := rfl
    have htv : H.current.edgeTime v ∈ V :=
      (mem_phase_iff_mem_cutVertices hd hi (phase_vertices_subset_current hd hi hv)).mp hv
    have hev : e ⟨v, hv⟩ = ⟨H.current.edgeTime v, htv⟩ := rfl
    have heu' : e.symm ⟨H.current.edgeTime u, htu⟩ = ⟨u, hu⟩ := by rw [← heu, e.symm_apply_apply]
    have hev' : e.symm ⟨H.current.edgeTime v, htv⟩ = ⟨v, hv⟩ := by rw [← hev, e.symm_apply_apply]
    have hr : (stage H i).forest.graph.Reachable
        (e.symm ⟨H.current.edgeTime u, htu⟩).val
        (e.symm ⟨H.current.edgeTime v, htv⟩).val := ⟨hback⟩
    simpa only [heu', hev'] using hr

/-- A fixed cut root's ancestor fiber is exactly its graph component. -/
theorem cutAncestor_eq_root_iff_reachable {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i))
    (ho : TimestampOrder H.current) {i : ℕ} (hi : i ≤ n) {r v : ℕ}
    (hr : r ∈ Forward.cutRoots (reverseState H.current) i)
    (hv : v ∈ Forward.cutVertices (reverseState H.current) i) :
    Forward.cutAncestor (reverseState H.current) i v = r ↔
      (Forward.cutGraph (reverseState H.current) i).Reachable r v := by
  have hrV := Forward.cutRoots_subset _ i hr
  have hrle := ((Forward.mem_cutRoots _ i r).mp hr).2
  rw [← image_phase_vertices_eq_cutVertices hd hi] at hrV hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hrV
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  rw [← Forward.cutAncestor_of_le (reverseState H.current) i (H.current.edgeTime u) hrle]
  rw [eq_comm, cutAncestor_eq_iff_stage_reachable hd hs hi hu hw,
    stage_reachable_iff_cutGraph hd hs ho hi hu hw]
  rw [Forward.cutAncestor_of_le (reverseState H.current) i (H.current.edgeTime u) hrle]

end ReverseStampedHistory

namespace Forward

/-- Under the actual tree law, the population's parent-recursion test is
exactly membership in the corresponding cut-graph component. -/
theorem treeLaw_cutAncestor_eq_root_iff_reachable (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂treeLaw x n, ∀ a ≤ n, ∀ r ∈ cutRoots s a, ∀ v ∈ cutVertices s a,
      cutAncestor s a v = r ↔ (cutGraph s a).Reachable r v := by
  rw [← ReverseStampedHistory.map_fullLaw_forwardState x n hn]
  apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
  have ho : ∀ᵐ H ∂ReverseStampedHistory.fullLaw x n,
      ReverseStamped.TimestampOrder H.current := by
    apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mp
    rw [ReverseStampedHistory.map_fullLaw_current]
    exact ReverseStamped.treeLaw_timestamp_order x n hn
  filter_upwards [ReverseStampedHistory.fullLaw_phaseData x n hn,
    ReverseStampedHistory.fullLaw_legalSteps x n hn, ho] with H hd hs horder
  intro a ha r hr v hv
  exact ReverseStampedHistory.cutAncestor_eq_root_iff_reachable hd hs horder ha hr hv

end Forward
end Freezing1
