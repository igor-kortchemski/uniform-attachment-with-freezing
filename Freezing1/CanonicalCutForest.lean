module

public import Freezing1.ReverseTimestampCuts
public import Freezing1.ForwardCutForest

/-!
# Canonical coordinates identify the actual cut forests

Terminal incoming-edge IDs transport each recorded reverse phase onto the
forward terminal tree with early frozen vertices and early edges removed.
The active vertices at the cut are exactly the transported component roots.
-/

@[expose] public section

namespace Freezing1.ReverseStampedHistory

open ReverseStamped CanonicalTree
open scoped Classical

theorem current_times_injective {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i)) :
    ∀ u ∈ H.current.forest.vertices, ∀ v ∈ H.current.forest.vertices,
      H.current.edgeTime u = H.current.edgeTime v → u = v := by
  have h0 := hd 0 (Nat.zero_le _)
  apply h0.times.edgeTime_injective_of_one_root
  simpa [activeCount_zero] using h0.valid.roots_card

theorem phase_vertices_subset_current {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i)) {i : ℕ} (hi : i ≤ n) :
    (stage H i).forest.vertices ⊆ H.current.forest.vertices := by
  intro v hv
  rw [(hd i hi).valid.vertices_eq] at hv
  have hverts0 : H.current.forest.vertices = Reverse.phaseLabels x n 0 :=
    (hd 0 (Nat.zero_le _)).valid.vertices_eq
  rw [hverts0]
  cases v <;> simp_all [Reverse.phaseLabels]

theorem mem_phase_iff_mem_cutVertices {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i)) {i : ℕ} (hi : i ≤ n)
    {v : ℕ ⊕ ℕ} (hv : v ∈ H.current.forest.vertices) :
    v ∈ (stage H i).forest.vertices ↔
      H.current.edgeTime v ∈ Forward.cutVertices (reverseState H.current) i := by
  have htime : H.current.edgeTime v ∈ (reverseState H.current).vertices :=
    Finset.mem_image_of_mem _ hv
  have hlabel := (reverseState_vertex_data (current_times_injective hd) hv).2.2
  rw [(hd i hi).valid.vertices_eq]
  simp only [Forward.cutVertices, Finset.mem_filter, htime, true_and, hlabel]
  have hverts0 : H.current.forest.vertices = Reverse.phaseLabels x n 0 :=
    (hd 0 (Nat.zero_le _)).valid.vertices_eq
  rw [hverts0] at hv
  cases v <;> simp_all [Reverse.phaseLabels, reverseLabel]

theorem image_phase_vertices_eq_cutVertices {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i)) {i : ℕ} (hi : i ≤ n) :
    (stage H i).forest.vertices.image H.current.edgeTime =
      Forward.cutVertices (reverseState H.current) i := by
  ext t
  constructor
  · intro ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    exact (mem_phase_iff_mem_cutVertices hd hi (phase_vertices_subset_current hd hi hv)).mp hv
  · intro ht
    have htV := (Finset.mem_filter.mp ht).1
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp htV
    exact Finset.mem_image.mpr ⟨v, (mem_phase_iff_mem_cutVertices hd hi hv).mpr ht, rfl⟩

theorem image_phase_roots_eq_cutRoots {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i))
    {i : ℕ} (hi : i ≤ n) :
    (stage H i).forest.roots.image H.current.edgeTime =
      Forward.cutRoots (reverseState H.current) i := by
  ext t
  constructor
  · intro ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    have hvI := (RootedForest.mem_roots.mp hv).1
    have hv0 := phase_vertices_subset_current hd hi hvI
    exact (Forward.mem_cutRoots _ _ _).mpr
      ⟨(mem_phase_iff_mem_cutVertices hd hi hv0).mp hvI,
        ((stage_roots_cut_iff hd hs hi v).mp hv).2⟩
  · intro ht
    obtain ⟨htV, hti⟩ := (Forward.mem_cutRoots _ _ _).mp ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ((Finset.mem_filter.mp htV).1)
    have hvI := (mem_phase_iff_mem_cutVertices hd hi hv).mpr htV
    refine Finset.mem_image.mpr ⟨v, (stage_roots_cut_iff hd hs hi v).mpr ⟨?_, hti⟩, rfl⟩
    exact (hd i hi).valid.vertices_eq ▸ hvI

theorem stage_graph_eq_cutGraph {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i))
    (ho : TimestampOrder H.current) {i : ℕ} (hi : i ≤ n)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ (stage H i).forest.vertices)
    (hv : v ∈ (stage H i).forest.vertices) :
    (stage H i).forest.graph.Adj u v ↔
      (Forward.cutGraph (reverseState H.current) i).Adj
        (H.current.edgeTime u) (H.current.edgeTime v) := by
  have hu0 := phase_vertices_subset_current hd hi hu
  have hv0 := phase_vertices_subset_current hd hi hv
  have huc := (mem_phase_iff_mem_cutVertices hd hi hu0).mp hu
  have hvc := (mem_phase_iff_mem_cutVertices hd hi hv0).mp hv
  have huI := (hd i hi).valid.vertices_eq ▸ hu
  have hvI := (hd i hi).valid.vertices_eq ▸ hv
  rw [stage_graph_cut_iff hd hs hi u v]
  simp only [Forward.cutGraph, huc, hvc, huI, hvI, true_and]
  rw [show (reverseState H.current).graph = (reverse H.current).graph from rfl,
    reverse_adj_iff (current_times_injective hd) hu0 hv0]
  simp only [RootedForest.graph, hu0, hv0, true_and, and_assoc]
  apply and_congr_right
  intro hne
  have hzero := hd 0 (Nat.zero_le _)
  have hmaxU (hp : H.current.forest.parent u = v) :
      max (H.current.edgeTime u) (H.current.edgeTime v) = H.current.edgeTime u := by
    have hz : H.current.edgeTime u ≠ 0 := by
      intro hz
      exact hne ((parent_of_time_zero hzero.times hzero.defaults hz).symm.trans hp)
    have hlt := ho.parent_lt u hu0 hz
    rw [hp] at hlt
    exact max_eq_left hlt.le
  have hmaxV (hp : H.current.forest.parent v = u) :
      max (H.current.edgeTime u) (H.current.edgeTime v) = H.current.edgeTime v := by
    have hz : H.current.edgeTime v ≠ 0 := by
      intro hz
      exact hne (hp.symm.trans (parent_of_time_zero hzero.times hzero.defaults hz))
    have hlt := ho.parent_lt v hv0 hz
    rw [hp] at hlt
    exact max_eq_right hlt.le
  constructor
  · rintro (⟨hp, ht⟩ | ⟨hp, ht⟩)
    · exact ⟨Or.inl hp, by rw [hmaxU hp]; exact ht⟩
    · exact ⟨Or.inr hp, by rw [hmaxV hp]; exact ht⟩
  · rintro ⟨hp | hp, ht⟩
    · exact Or.inl ⟨hp, by rwa [hmaxU hp] at ht⟩
    · exact Or.inr ⟨hp, by rwa [hmaxV hp] at ht⟩

/-- An explicit isomorphism of the finite phase graph and the actual forward
cut graph. The coordinates are the terminal edge birth times. -/
noncomputable def cutGraphIso {x : SignSequence} {n : ℕ} {H : History}
    (hd : ∀ i ≤ n, PhaseData x n i (stage H i))
    (hs : ∀ i < n, LegalStep x i (stage H (i + 1)) (stage H i))
    (ho : TimestampOrder H.current) {i : ℕ} (hi : i ≤ n) :
    (stage H i).forest.toGraph ≃g
      (Forward.cutGraph (reverseState H.current) i).induce
        (Forward.cutVertices (reverseState H.current) i : Set ℕ) where
  toEquiv := Equiv.ofBijective (fun v => ⟨H.current.edgeTime v,
    (mem_phase_iff_mem_cutVertices hd hi (phase_vertices_subset_current hd hi v.property)).mp v.property⟩)
    (by
      constructor
      · intro u v he
        apply Subtype.ext
        exact current_times_injective hd _ (phase_vertices_subset_current hd hi u.property)
          _ (phase_vertices_subset_current hd hi v.property) (congrArg Subtype.val he)
      · rintro ⟨t, ht⟩
        rw [← image_phase_vertices_eq_cutVertices hd hi] at ht
        obtain ⟨v, hv, he⟩ := Finset.mem_image.mp ht
        exact ⟨⟨v, hv⟩, Subtype.ext he⟩)
  map_rel_iff' := by
    intro u v
    exact (stage_graph_eq_cutGraph hd hs ho hi u.property v.property).symm

end Freezing1.ReverseStampedHistory
