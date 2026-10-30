module

public import Freezing1.PlaneFiniteGraph
public import Freezing1.ForwardPlaneUpdates
public import Freezing1.CanonicalPairSampling
public import Freezing1.ForwardSupportCharacterization
public import Freezing1.ForwardAbsorption

/-!
# Chronological addresses preserve actual pair distances

The address graph has edges precisely at the original parent edges. Walks
are transported in both directions on the finite vertex set; conditional
uniform pair data are consequently unchanged by the plane projection.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal Classical

def ParentGraphData (s : State) : Prop := ∀ u v : ℕ,
  s.graph.Adj u v ↔ u ∈ s.vertices ∧ v ∈ s.vertices ∧
    ((u ≠ 0 ∧ s.parent u = v) ∨ (v ≠ 0 ∧ s.parent v = u))

theorem plane_parentGraph_adj_iff {n : ℕ} {s : State} (hs : ValidAt n s)
    (hg : ParentGraphData s) {u v : ℕ} (hu : u ∈ s.vertices) (hv : v ∈ s.vertices) :
    (PlaneForward.parentGraph s.toPlaneState).Adj (planeAddress s u) (planeAddress s v) ↔
      s.graph.Adj u v := by
  have hu' : planeAddress s u ∈ s.toPlaneState.vertices := Finset.mem_image_of_mem _ hu
  have hv' : planeAddress s v ∈ s.toPlaneState.vertices := Finset.mem_image_of_mem _ hv
  change (planeAddress s u ∈ s.toPlaneState.vertices ∧
    planeAddress s v ∈ s.toPlaneState.vertices ∧ _) ↔ _
  rw [hg u v]
  simp only [hu, hv, hu', hv', true_and]
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact Or.inr ⟨(planeAddress_child_iff hs hu hv j).mp hj |>.1,
        (planeAddress_child_iff hs hu hv j).mp hj |>.2.1⟩
    · exact Or.inl ⟨(planeAddress_child_iff hs hv hu j).mp hj |>.1,
        (planeAddress_child_iff hs hv hu j).mp hj |>.2.1⟩
  · rintro (⟨hu0, hup⟩ | ⟨hv0, hvp⟩)
    · exact Or.inr ⟨childRank s u, (planeAddress_child_iff hs hv hu _).mpr ⟨hu0, hup, rfl⟩⟩
    · exact Or.inl ⟨childRank s v, (planeAddress_child_iff hs hu hv _).mpr ⟨hv0, hvp, rfl⟩⟩

noncomputable def originalVertex (s : State) (u : PlaneTree.Address) : ℕ :=
  if hu : u ∈ s.toPlaneState.vertices then
    Classical.choose (Finset.mem_image.mp hu) else 0

theorem originalVertex_mem {s : State} {u : PlaneTree.Address}
    (hu : u ∈ s.toPlaneState.vertices) : originalVertex s u ∈ s.vertices := by
  simp only [originalVertex, dite_eq_left hu]
  exact (Classical.choose_spec (Finset.mem_image.mp hu)).1

theorem planeAddress_originalVertex {s : State} {u : PlaneTree.Address}
    (hu : u ∈ s.toPlaneState.vertices) : planeAddress s (originalVertex s u) = u := by
  simp only [originalVertex, dite_eq_left hu]
  exact (Classical.choose_spec (Finset.mem_image.mp hu)).2

theorem originalVertex_planeAddress {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) : originalVertex s (planeAddress s v) = v := by
  have hm := Finset.mem_image_of_mem (planeAddress s) hv
  exact hs.planeAddress_injective (originalVertex_mem hm) hv (planeAddress_originalVertex hm)

noncomputable def planeGraphForward {n : ℕ} {s : State} (hs : ValidAt n s)
    (hg : ParentGraphData s) : s.graph →g PlaneForward.parentGraph s.toPlaneState where
  toFun := planeAddress s
  map_rel' := by
    intro u v huv
    exact (plane_parentGraph_adj_iff hs hg (hs.adj_mem huv).1 (hs.adj_mem huv).2).mpr huv

noncomputable def planeGraphBackward {n : ℕ} {s : State} (hs : ValidAt n s)
    (hg : ParentGraphData s) : PlaneForward.parentGraph s.toPlaneState →g s.graph where
  toFun := originalVertex s
  map_rel' := by
    intro u v huv
    have hu := huv.1
    have hv := huv.2.1
    apply (plane_parentGraph_adj_iff hs hg (originalVertex_mem hu) (originalVertex_mem hv)).mp
    rwa [planeAddress_originalVertex hu, planeAddress_originalVertex hv]

theorem planeAddress_graph_dist {n : ℕ} {s : State} (hs : ValidAt n s)
    (hg : ParentGraphData s) {u v : ℕ} (hu : u ∈ s.vertices) (hv : v ∈ s.vertices) :
    (PlaneForward.parentGraph s.toPlaneState).dist (planeAddress s u) (planeAddress s v) =
      s.graph.dist u v := by
  let f := planeGraphForward hs hg
  let g := planeGraphBackward hs hg
  have hf (w : ℕ) : f w = planeAddress s w := rfl
  have hr := (hs.reachable u hu).symm.trans (hs.reachable v hv)
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    have hh := (PlaneForward.parentGraph s.toPlaneState).dist_le (p.map f)
    simpa only [SimpleGraph.Walk.length_map, hp, hf] using hh
  · obtain ⟨p, hp⟩ := (hr.map f).exists_walk_length_eq_dist
    have hh := s.graph.dist_le (p.map g)
    have hu' : g (f u) = u := originalVertex_planeAddress hs hu
    have hv' : g (f v) = v := originalVertex_planeAddress hs hv
    rw [SimpleGraph.Walk.length_map, hp, hu', hv'] at hh
    exact hh

theorem pairDataKernel_toPlaneState {n : ℕ} {s : State} (hs : ValidAt n s)
    (hg : ParentGraphData s) :
    PlaneForward.pairDataKernel s.toPlaneState = CanonicalTree.forwardPairKernel s := by
  have hp : s.toPlaneState.vertices.Nonempty := ⟨[], by
    rw [← planeAddress_zero s]
    exact Finset.mem_image_of_mem _ hs.root_mem⟩
  have hmap : (Measure.uniformOfFinset s.vertices).map (planeAddress s) =
      Measure.uniformOfFinset s.toPlaneState.vertices :=
    map_uniformOfFinset_of_injOn s.vertices (planeAddress s) (measurable_of_countable _)
      hs.planeAddress_injective
  change (if s.toPlaneState.vertices.Nonempty then _ else _) = _
  rw [ite_eq_left hp]
  unfold CanonicalTree.forwardPairKernel
  simp_rw [← hmap]
  rw [Measure.bind_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  apply Measure.bind_congr_right
  have hae : ∀ᵐ u ∂Measure.uniformOfFinset s.vertices, u ∈ s.vertices := by
    rw [ae_iff]
    simp [Measure.uniformOfFinset_apply]
  filter_upwards [hae] with u hu
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  apply Measure.map_congr
  filter_upwards [hae] with v hv
  simp only [Function.comp_def, hs.planeAddress_length hu, hs.planeAddress_length hv,
    planeAddress_graph_dist hs hg hu hv]

theorem treeLaw_parentGraphData (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, ParentGraphData s := by
  by_cases hn : (n : ℕ∞) ≤ extinctionTime x
  · filter_upwards [treeLaw_historyShape x n hn] with s hs
    exact hs.graph_iff
  · have hfinite : extinctionTime x ≠ ⊤ := ne_top_of_lt (lt_of_not_ge hn)
    obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfinite
    have htn : t ≤ n := by
      have hh : (t : ℕ∞) < n := by rw [ht]; exact lt_of_not_ge hn
      exact_mod_cast hh.le
    have he : treeLaw x n = treeLaw x t := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le htn
      rw [hk]
      exact treeLaw_constant_after_extinction ht.symm k
    rw [he]
    filter_upwards [treeLaw_historyShape x t ht.le] with s hs
    exact hs.graph_iff

theorem treeLaw_pairDataKernel_toPlaneState (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n,
      PlaneForward.pairDataKernel s.toPlaneState = CanonicalTree.forwardPairKernel s := by
  filter_upwards [treeLaw_valid x n, treeLaw_parentGraphData x n] with s hs hg
  exact pairDataKernel_toPlaneState hs hg

theorem planePairDataLaw_fixed (x : SignSequence) (n : ℕ) :
    ((treeLaw x n).map State.toPlaneState).bind PlaneForward.pairDataKernel =
      CanonicalTree.forwardPairDataLaw x n := by
  rw [Measure.bind_map measurable_from_top.aemeasurable PlaneForward.pairDataKernel.measurable.aemeasurable]
  apply Measure.bind_congr_right
  exact treeLaw_pairDataKernel_toPlaneState x n

end Freezing1.Forward
