module

public import Freezing1.ReverseTimestampOrder
public import Freezing1.ForwardEdgeOrder
public import Freezing1.ForwardScheduleSupport

/-!
# A common observable for the two constructions

The root has canonical identifier zero. A nonroot identifier is its incoming
edge timestamp. We retain the actual undirected graph, active vertex IDs and
all frozen vertex labels. The timestamp of an edge is the maximum endpoint ID,
as proved below for the two actual constructions. Thus only the distinctions
between the reverse construction's active labels are erased.

This defines the precise target of T05; equality of the two pushforward laws is
not assumed or asserted in this module.
-/

@[expose] public section

namespace Freezing1.CanonicalTree

open MeasureTheory
open scoped Classical

structure Observable where
  vertices : Finset ℕ
  graph : SimpleGraph ℕ
  active : Finset ℕ
  frozen : Finset (ℕ × ℕ)

instance : MeasurableSpace Observable := ⊤
instance : DiscreteMeasurableSpace Observable := ⟨fun _ => trivial⟩

/-- Reconstruct the edge timestamp from canonical endpoint coordinates. -/
def edgeTime (u v : ℕ) : ℕ := max u v

/-- All frozen vertex labels, with their persistent vertex identifiers. -/
def frozenPairs {V : Type*} [DecidableEq V] (s : Finset V)
    (coordinate : V → ℕ) (label : V → Option ℕ) : Finset (ℕ × ℕ) :=
  s.biUnion fun v => (label v).toFinset.image fun t => (coordinate v, t)

theorem mem_frozenPairs {V : Type*} [DecidableEq V] {s : Finset V}
    {coordinate : V → ℕ} {label : V → Option ℕ} {a t : ℕ} :
    (a, t) ∈ frozenPairs s coordinate label ↔
      ∃ v ∈ s, coordinate v = a ∧ label v = some t := by
  simp only [frozenPairs, Finset.mem_biUnion, Finset.mem_image, Option.mem_toFinset,
    Prod.mk.injEq]
  constructor
  · rintro ⟨v, hv, u, hu, hc, rfl⟩
    exact ⟨v, hv, hc, hu⟩
  · rintro ⟨v, hv, hc, ht⟩
    exact ⟨v, hv, t, ht, hc, rfl⟩

/-- Transport a finite graph to canonical coordinates. The explicit inequality
makes this a simple graph even on inputs whose coordinates are not injective. -/
def transportGraph {V : Type*} [DecidableEq V] (s : Finset V)
    (coordinate : V → ℕ) (G : SimpleGraph V) : SimpleGraph ℕ where
  Adj a b := a ≠ b ∧ ∃ u ∈ s, ∃ v ∈ s,
    coordinate u = a ∧ coordinate v = b ∧ G.Adj u v
  symm := by
    constructor
    rintro a b ⟨hne, u, hu, v, hv, hcu, hcv, hadj⟩
    exact ⟨hne.symm, v, hv, u, hu, hcv, hcu, hadj.symm⟩
  loopless := ⟨by simp⟩

/-- Injective coordinates preserve and reflect every adjacency. -/
theorem transportGraph_adj_iff {V : Type*} [DecidableEq V] {s : Finset V}
    {coordinate : V → ℕ} {G : SimpleGraph V}
    (hinj : ∀ u ∈ s, ∀ v ∈ s, coordinate u = coordinate v → u = v)
    {u v : V} (hu : u ∈ s) (hv : v ∈ s) :
    (transportGraph s coordinate G).Adj (coordinate u) (coordinate v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨_, a, ha, b, hb, hca, hcb, hadj⟩
    have hau : a = u := hinj a ha u hu hca
    have hbv : b = v := hinj b hb v hv hcb
    simpa only [hau, hbv] using hadj
  · intro hadj
    exact ⟨fun he => hadj.ne (hinj u hu v hv he), u, hu, v, hv, rfl, rfl, hadj⟩

/-- The forward state's displayed labels and graph, with its existing birth IDs. -/
def forward (s : Forward.State) : Observable where
  vertices := s.vertices
  graph := s.graph
  active := s.active
  frozen := frozenPairs s.vertices id s.frozenAt

/-- The reverse label `inr j` displays freezing time `j+1`; active identities
`inl j` all display the same unlabeled active status. -/
def reverseLabel : (ℕ ⊕ ℕ) → Option ℕ
  | .inl _ => none
  | .inr j => some (j + 1)

/-- The exact common observable of a timestamped reverse forest. -/
def reverse (F : ReverseStamped.Forest) : Observable where
  vertices := F.forest.vertices.image F.edgeTime
  graph := transportGraph F.forest.vertices F.edgeTime F.forest.graph
  active := (F.forest.vertices.filter fun v => reverseLabel v = none).image F.edgeTime
  frozen := frozenPairs F.forest.vertices F.edgeTime reverseLabel

theorem forward_frozen_iff {s : Forward.State} {v t : ℕ} :
    (v, t) ∈ (forward s).frozen ↔ v ∈ s.vertices ∧ s.frozenAt v = some t := by
  simp [forward, mem_frozenPairs]

theorem reverse_frozen_iff {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices) {t : ℕ} :
    (F.edgeTime v, t) ∈ (reverse F).frozen ↔ reverseLabel v = some t := by
  change (_, _) ∈ frozenPairs _ _ _ ↔ _
  rw [mem_frozenPairs]
  constructor
  · rintro ⟨u, hu, he, ht⟩
    simpa only [hinj u hu v hv he] using ht
  · exact fun ht => ⟨v, hv, rfl, ht⟩

theorem reverse_active_iff {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices) :
    F.edgeTime v ∈ (reverse F).active ↔ reverseLabel v = none := by
  simp only [reverse, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, hl⟩, he⟩
    simpa only [hinj u hu v hv he] using hl
  · exact fun hl => ⟨v, ⟨hv, hl⟩, rfl⟩

theorem reverse_adj_iff {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ F.forest.vertices) (hv : v ∈ F.forest.vertices) :
    (reverse F).graph.Adj (F.edgeTime u) (F.edgeTime v) ↔ F.forest.graph.Adj u v :=
  transportGraph_adj_iff hinj hu hv

/-- Incoming-edge coordinates give a bijection of the actual finite vertex sets. -/
theorem reverse_coordinates_bijective {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    Function.Bijective (fun v : {v // v ∈ F.forest.vertices} =>
      (⟨F.edgeTime v, Finset.mem_image_of_mem _ v.property⟩ :
        {t // t ∈ (reverse F).vertices})) := by
  constructor
  · intro u v he
    exact Subtype.ext (hinj u u.property v v.property (congrArg Subtype.val he))
  · rintro ⟨t, ht⟩
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp ht
    exact ⟨⟨v, hv⟩, Subtype.ext he⟩

/-- The finite underlying graph is preserved up to an explicit isomorphism. -/
noncomputable def reverseGraphIso {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    F.forest.toGraph ≃g (reverse F).graph.induce ((reverse F).vertices : Set ℕ) where
  toEquiv := Equiv.ofBijective (fun v : {v // v ∈ F.forest.vertices} =>
    (⟨F.edgeTime v, Finset.mem_image_of_mem _ v.property⟩ :
      {t // t ∈ (reverse F).vertices})) (reverse_coordinates_bijective hinj)
  map_rel_iff' := by
    intro u v
    exact reverse_adj_iff hinj u.property v.property

/-- The actual reverse law meets the injectivity condition needed for this
finite graph isomorphism, including the extinction endpoint. -/
theorem treeLaw_reverse_graph_isomorphic (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂ReverseStamped.treeLaw x n,
      Nonempty (F.forest.toGraph ≃g (reverse F).graph.induce ((reverse F).vertices : Set ℕ)) := by
  filter_upwards [ReverseStamped.treeLaw_canonical_ids x n hn] with F hF
  exact ⟨reverseGraphIso hF.1⟩

/-- Forward parent edges keep exactly their attachment timestamp. -/
theorem forward_edge_time {n : ℕ} {s : Forward.State} (hs : Forward.ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) (hn : v ≠ 0) :
    edgeTime (s.parent v) v = v := max_eq_right (hs.parent_lt v hv hn).le

/-- Reverse parent edges keep exactly the timestamp stored by the genuine
root-pair kernel, after passage to the common observable. -/
theorem reverse_edge_time {F : ReverseStamped.Forest} (ho : ReverseStamped.TimestampOrder F)
    {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices) (hn : F.edgeTime v ≠ 0) :
    edgeTime (F.edgeTime (F.forest.parent v)) (F.edgeTime v) = F.edgeTime v :=
  ho.parent_edge_time hv hn

/-- The common observable retains the root as identifier zero. -/
theorem reverse_root_id {x : SignSequence} {n i : ℕ} {F : ReverseStamped.Forest}
    (ht : ReverseStamped.TimesValidAt x n i F) {r : ℕ ⊕ ℕ}
    (hr : r ∈ F.forest.roots) : F.edgeTime r = 0 :=
  (ht.root_zero r (RootedForest.mem_roots.mp hr).1).mpr hr

noncomputable def forwardLaw (x : SignSequence) (n : ℕ) : Measure Observable :=
  (Forward.treeLaw x n).map forward

noncomputable def reverseLaw (x : SignSequence) (n : ℕ) : Measure Observable :=
  (ReverseStamped.treeLaw x n).map reverse

instance forwardLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (forwardLaw x n) :=
  Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr inferInstance

instance reverseLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (reverseLaw x n) :=
  Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr inferInstance

/-- Both observable laws use precisely the prescribed canonical birth-ID set. -/
theorem forwardLaw_vertices (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ T ∂forwardLaw x n,
      T.vertices = insert 0 (ReverseStamped.attachmentTimes x n 0) := by
  apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
  filter_upwards [Forward.treeLaw_schedule_support x n hn] with s hs
  ext v
  simp only [forward, Finset.mem_insert, ReverseStamped.attachmentTimes,
    Finset.mem_filter, Finset.mem_Ioc]
  rw [hs.vertex_iff]
  constructor
  · rintro (rfl | ⟨hpos, hle, hx⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨by omega, hle⟩, hx⟩
  · rintro (rfl | ⟨⟨hpos, hle⟩, hx⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨by omega, hle, hx⟩

theorem reverseLaw_vertices (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ T ∂reverseLaw x n,
      T.vertices = insert 0 (ReverseStamped.attachmentTimes x n 0) := by
  apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
  filter_upwards [ReverseStamped.treeLaw_canonical_ids x n hn] with F hF
  exact hF.2

end Freezing1.CanonicalTree
