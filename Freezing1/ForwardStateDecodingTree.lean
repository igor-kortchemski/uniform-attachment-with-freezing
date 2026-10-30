module

public import Freezing1.RootedForwardEncodingMain

/-!
# Decoding a forward state into a labelled rooted tree: the tree and its local properties

For a forward state `s` and a bound `N`, the decoded tree rooted at the vertex `v` has the
freezing label `s.frozenAt v` (`none` means active) and one child for each vertex `w` with
`v < w ≤ N`, `w ∈ s.vertices` and `s.parent w = v`; the child carries the edge label `w` and is
the decoded tree rooted at `w`. The children are listed in increasing order of `w`.
The recursion is well founded on `N - v`.

For a state satisfying the schedule-free intrinsic conditions `Forward.IncreasingLabelled N`,
the decoded tree is heap-increasing, has strictly increasing sibling edge labels (hence is
`Rooted.Increasing`), and is encoded by `s` in the recursive sense `Rooted.Encodes`.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

/-- Identifiers of the children of `v`, in increasing order: the vertices `w` of `s` with
`v < w ≤ N` whose parent is `v`. -/
noncomputable def decChildren (s : Forward.State) (N v : ℕ) : List ℕ :=
  (List.range' (v + 1) (N - v)).filter (fun w => decide (w ∈ s.vertices ∧ s.parent w = v))

theorem mem_decChildren {s : Forward.State} {N v w : ℕ} :
    w ∈ decChildren s N v ↔ v < w ∧ w ≤ N ∧ w ∈ s.vertices ∧ s.parent w = v := by
  simp only [decChildren, List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by omega, by omega, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by omega, by omega⟩, h3, h4⟩

theorem decChildren_pairwise (s : Forward.State) (N v : ℕ) :
    (decChildren s N v).Pairwise (· < ·) := by
  unfold decChildren
  exact List.Pairwise.filter _ List.pairwise_lt_range'

theorem decChildren_nodup (s : Forward.State) (N v : ℕ) : (decChildren s N v).Nodup :=
  (decChildren_pairwise s N v).imp (fun h => h.ne)

/-- The finite set of children of `v`. -/
noncomputable def decChildSet (s : Forward.State) (N v : ℕ) : Finset ℕ :=
  (decChildren s N v).toFinset

theorem mem_decChildSet {s : Forward.State} {N v w : ℕ} :
    w ∈ decChildSet s N v ↔ v < w ∧ w ≤ N ∧ w ∈ s.vertices ∧ s.parent w = v := by
  rw [decChildSet, List.mem_toFinset, mem_decChildren]

/-- The tree decoded from the state `s` below the vertex `v`. -/
noncomputable def decodeTree (s : Forward.State) (N v : ℕ) : Rooted :=
  .node (s.frozenAt v)
    ((decChildren s N v).attach.map (fun w => (w.1, decodeTree s N w.1)))
termination_by N - v
decreasing_by
  have := mem_decChildren.mp w.2
  omega

theorem decodeTree_eq (s : Forward.State) (N v : ℕ) :
    decodeTree s N v = .node (s.frozenAt v)
      ((decChildren s N v).map (fun w => (w, decodeTree s N w))) := by
  rw [decodeTree]
  congr 1
  exact List.attach_map_val (f := fun w => (w, decodeTree s N w))

/-- Induction along the decoding recursion: a property that holds at `v` whenever it holds at all
children of `v` holds everywhere. -/
theorem decChildren_induction (s : Forward.State) (N : ℕ) {P : ℕ → Prop}
    (h : ∀ v, (∀ c ∈ decChildren s N v, P c) → P v) : ∀ v, P v := by
  intro v
  induction hn : N - v using Nat.strong_induction_on generalizing v with
  | _ m ih =>
    apply h
    intro c hc
    have := mem_decChildren.mp hc
    exact ih (N - c) (by omega) c rfl

theorem edgeLabels_decodeTree (s : Forward.State) (N v : ℕ) :
    (decodeTree s N v).edgeLabels =
      ∑ c ∈ decChildSet s N v, (c ::ₘ (decodeTree s N c).edgeLabels) := by
  rw [decodeTree_eq, Rooted.edgeLabels_node, decChildSet,
    List.sum_toFinset _ (decChildren_nodup s N v), List.map_map]
  congr 1

/-- The decoded tree always has strictly increasing sibling edge labels. -/
theorem decodeTree_canonical (s : Forward.State) (N : ℕ) : ∀ v, (decodeTree s N v).Canonical := by
  apply decChildren_induction s N (P := fun v => (decodeTree s N v).Canonical)
  intro v ih
  rw [decodeTree_eq, Rooted.canonical_node_iff]
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_map]
    exact decChildren_pairwise s N v
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact ih c hc

/-- The decoded tree is matched by the state in the recursive sense of `Rooted.Encodes`. -/
theorem decodeTree_encodes {s : Forward.State} {N : ℕ} (h : Forward.IncreasingLabelled N s) :
    ∀ v, (decodeTree s N v).Encodes s v := by
  apply decChildren_induction s N (P := fun v => (decodeTree s N v).Encodes s v)
  intro v ih
  rw [decodeTree_eq, Rooted.encodes_node_iff]
  refine ⟨rfl, ?_⟩
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨h1, h2, h3, h4⟩ := mem_decChildren.mp hc
  refine ⟨h4, ?_, ih c hc⟩
  rw [h.height_parent c h3 (by omega), h4]

theorem decodeTree_rootAbove {s : Forward.State} {N : ℕ} (h : Forward.IncreasingLabelled N s)
    {w : ℕ} (hw : w ∈ s.vertices) : (decodeTree s N w).rootAbove w := by
  rw [decodeTree_eq]
  refine ⟨?_, ?_⟩
  · cases hf : s.frozenAt w with
    | none => trivial
    | some t => exact h.frozen_after_birth w hw t hf
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact (mem_decChildren.mp hc).1

/-- The decoded tree is heap-increasing. -/
theorem decodeTree_heapIncreasing {s : Forward.State} {N : ℕ}
    (h : Forward.IncreasingLabelled N s) : ∀ v, (decodeTree s N v).HeapIncreasing := by
  apply decChildren_induction s N (P := fun v => (decodeTree s N v).HeapIncreasing)
  intro v ih
  rw [decodeTree_eq, Rooted.heapIncreasing_node_iff]
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨h1, h2, h3, h4⟩ := mem_decChildren.mp hc
  refine ⟨ih c hc, decodeTree_rootAbove h h3, ?_⟩
  cases hf : s.frozenAt v with
  | none => trivial
  | some t => exact h.parent_frozen_after_child c h3 (by omega) t (h4 ▸ hf)

/-- The decoded tree is increasing in the source's sorted sense. -/
theorem decodeTree_increasing {s : Forward.State} {N : ℕ}
    (h : Forward.IncreasingLabelled N s) (v : ℕ) : (decodeTree s N v).Increasing :=
  (Rooted.increasing_iff_heap_canonical _).mpr
    ⟨decodeTree_heapIncreasing h v, decodeTree_canonical s N v⟩

end Freezing1.BinaryBijection
