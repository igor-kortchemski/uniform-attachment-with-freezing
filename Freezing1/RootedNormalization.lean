module

public import Freezing1.RootedUnorderedTrees
public import Freezing1.ListSortByKey

/-!
# Canonical edge-sorted representatives of unordered rooted trees

Normalization recursively normalizes each subtree and sorts siblings by
their integer edge labels. It is related to the input by actual subtree
congruences and sibling permutations. Distinct labels make the result
canonical and independent of every auxiliary sibling order.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

theorem Rooted.child_size_lt (label : Option ℕ) (children : List (ℕ × Rooted))
    (p : ℕ × Rooted) (hp : p ∈ children) : sizeOf p.2 < sizeOf (Rooted.node label children) := by
  have hm := List.sizeOf_lt_of_mem hp
  have hp' : sizeOf p.2 < sizeOf p := by
    change sizeOf p.2 < 1 + sizeOf p.1 + sizeOf p.2
    omega
  simp_wf
  omega

theorem Rooted.UnorderedEq.children_map (label : Option ℕ) (f : Rooted → Rooted)
    (children before : List (ℕ × Rooted))
    (hf : ∀ p ∈ children, (f p.2).UnorderedEq p.2) :
    (Rooted.node label (before ++ children.map (fun p => (p.1, f p.2)))).UnorderedEq
      (Rooted.node label (before ++ children)) := by
  induction children generalizing before with
  | nil => exact .refl _
  | cons p rest ih =>
    rcases p with ⟨edge, child⟩
    apply Rooted.UnorderedEq.trans
      (.child label edge before (rest.map (fun p => (p.1, f p.2))) (hf (edge, child) (by simp)))
    simpa only [List.append_assoc, List.singleton_append] using
      ih (before ++ [(edge, child)]) (fun p hp => hf p (List.mem_cons_of_mem _ hp))

def Rooted.normalize : Rooted → Rooted
  | .node label children =>
      .node label (ListSortByKey.sort Prod.fst
        (children.attach.map (fun p => (p.val.1, normalize p.val.2))))
termination_by t => sizeOf t
decreasing_by exact Rooted.child_size_lt label children _ p.property

theorem Rooted.normalize_node (label : Option ℕ) (children : List (ℕ × Rooted)) :
    (Rooted.node label children).normalize = Rooted.node label
      (ListSortByKey.sort Prod.fst (children.map (fun p => (p.1, p.2.normalize)))) := by
  rw [Rooted.normalize]
  apply congrArg (Rooted.node label)
  apply congrArg (ListSortByKey.sort Prod.fst)
  exact List.attach_map_val (l := children) (f := fun p : ℕ × Rooted => (p.1, p.2.normalize))

theorem Rooted.normalize_related : ∀ t : Rooted, t.normalize.UnorderedEq t
  | .node label children => by
      rw [Rooted.normalize_node]
      have hc := Rooted.UnorderedEq.children_map label Rooted.normalize children []
        (fun p hp => normalize_related p.2)
      exact Rooted.UnorderedEq.trans
        (.perm label (ListSortByKey.sort_perm _ _))
        (by simpa only [List.nil_append] using hc)
termination_by t => sizeOf t
decreasing_by exact Rooted.child_size_lt label children _ hp

theorem Rooted.normalize_vertexCount (t : Rooted) : t.normalize.vertexCount = t.vertexCount :=
  t.normalize_related.data_eq.1

theorem Rooted.normalize_activeCount (t : Rooted) : t.normalize.activeCount = t.activeCount :=
  t.normalize_related.data_eq.2.1

theorem Rooted.normalize_labels (t : Rooted) : t.normalize.labels = t.labels :=
  t.normalize_related.data_eq.2.2

theorem Rooted.normalize_rootAbove (t : Rooted) (bound : ℕ) :
    t.normalize.rootAbove bound ↔ t.rootAbove bound := t.normalize_related.rootAbove_iff bound

theorem Rooted.normalize_heapIncreasing (t : Rooted) :
    t.normalize.HeapIncreasing ↔ t.HeapIncreasing := t.normalize_related.heapIncreasing_iff

theorem Rooted.edgeLabels_node (label : Option ℕ) (children : List (ℕ × Rooted)) :
    (Rooted.node label children).edgeLabels =
      (children.map (fun p => ({p.1} : Multiset ℕ) + p.2.edgeLabels)).sum := by
  induction children with
  | nil => simp [Rooted.edgeLabels]
  | cons p rest ih =>
    rcases p with ⟨edge, child⟩
    simp only [Rooted.edgeLabels, List.map_cons, List.sum_cons, ih]

theorem Rooted.vertexLabels_node (label : Option ℕ) (children : List (ℕ × Rooted)) :
    (Rooted.node label children).vertexLabels =
      labelMultiset label + (children.map (fun p => p.2.vertexLabels)).sum := by
  induction children with
  | nil => simp [Rooted.vertexLabels]
  | cons p rest ih =>
    rcases p with ⟨edge, child⟩
    simp only [Rooted.vertexLabels, List.map_cons, List.sum_cons, ih]
    ac_rfl

theorem Rooted.UnorderedEq.edge_vertex_labels_eq {s t : Rooted} (h : s.UnorderedEq t) :
    s.edgeLabels = t.edgeLabels ∧ s.vertexLabels = t.vertexLabels := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | symm h ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans h1 h2 ih1 ih2 => exact ⟨ih1.1.trans ih2.1, ih1.2.trans ih2.2⟩
  | perm label hp =>
    constructor
    · rw [Rooted.edgeLabels_node, Rooted.edgeLabels_node,
        (hp.map (fun p => ({p.1} : Multiset ℕ) + p.2.edgeLabels)).sum_eq]
    · rw [Rooted.vertexLabels_node, Rooted.vertexLabels_node,
        (hp.map (fun p => p.2.vertexLabels)).sum_eq]
  | child label edge before after he ih =>
    simp only [Rooted.edgeLabels_node, Rooted.vertexLabels_node,
      List.map_append, List.map_cons, List.sum_append, List.sum_cons, ih.1, ih.2]
    trivial

theorem Rooted.normalize_edgeLabels (t : Rooted) : t.normalize.edgeLabels = t.edgeLabels :=
  t.normalize_related.edge_vertex_labels_eq.1

theorem Rooted.normalize_vertexLabels (t : Rooted) : t.normalize.vertexLabels = t.vertexLabels :=
  t.normalize_related.edge_vertex_labels_eq.2

theorem Rooted.root_edge_mem_labels (label : Option ℕ) (children : List (ℕ × Rooted))
    (p : ℕ × Rooted) (hp : p ∈ children) : p.1 ∈ (Rooted.node label children).labels := by
  induction children with
  | nil => simp at hp
  | cons q rest ih =>
    rcases q with ⟨edge, child⟩
    rcases List.mem_cons.mp hp with he | hp
    · simp only [he, Rooted.labels, Multiset.mem_add, Multiset.mem_singleton, true_or]
    · rw [Rooted.labels]
      exact Multiset.mem_add.mpr (Or.inr (ih hp))

theorem Rooted.child_labels_le (label : Option ℕ) (children : List (ℕ × Rooted))
    (p : ℕ × Rooted) (hp : p ∈ children) : p.2.labels ≤ (Rooted.node label children).labels := by
  induction children with
  | nil => simp at hp
  | cons q rest ih =>
    rcases q with ⟨edge, child⟩
    rw [Rooted.labels]
    rcases List.mem_cons.mp hp with he | hp
    · rw [he]
      exact (Multiset.le_add_left child.labels {edge}).trans (Multiset.le_add_right _ _)
    · exact (ih hp).trans (Multiset.le_add_left _ _)

theorem Rooted.root_keys_nodup (label : Option ℕ) (children : List (ℕ × Rooted))
    (hnd : (Rooted.node label children).labels.Nodup) : (children.map Prod.fst).Nodup := by
  induction children with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨edge, child⟩
    have hh : edge ∉ child.labels + (Rooted.node label rest).labels ∧
        (child.labels + (Rooted.node label rest).labels).Nodup := by
      simpa only [Rooted.labels, Multiset.singleton_add, Multiset.cons_add, Multiset.nodup_cons] using hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (Multiset.nodup_of_le (Multiset.le_add_left _ _) hh.2)⟩
    intro hmem
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hmem
    change p.1 = edge at he
    have hm : edge ∈ (Rooted.node label rest).labels := by
      rw [← he]
      exact root_edge_mem_labels label rest p hp
    exact hh.1 (Multiset.mem_add.mpr (Or.inr hm))

theorem Rooted.normalize_canonical : ∀ t : Rooted, t.labels.Nodup → t.normalize.Canonical
  | .node label children, hnd => by
      rw [Rooted.normalize_node, Rooted.canonical_node_iff]
      refine ⟨ListSortByKey.sort_pairwise _ _ ?_, ?_⟩
      · simpa only [List.map_map, Function.comp_def] using root_keys_nodup label children hnd
      · intro p hp
        have hm := (ListSortByKey.sort_perm Prod.fst _).mem_iff.mp hp
        obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
        rw [← he]
        exact normalize_canonical q.2 (Multiset.nodup_of_le (child_labels_le label children q hq) hnd)
termination_by t => sizeOf t
decreasing_by exact Rooted.child_size_lt label children _ hq

theorem Rooted.normalize_eq_self : ∀ t : Rooted, t.Canonical → t.normalize = t
  | .node label children, hc => by
      have hh := (Rooted.canonical_node_iff label children).mp hc
      have hm : children.map (fun p => (p.1, p.2.normalize)) = children := by
        simpa only [List.map_id] using
          (List.map_congr_left (l := children) (f := fun p => (p.1, p.2.normalize)) (g := id)
            (fun p hp => by rw [normalize_eq_self p.2 (hh.2 p hp)]; rfl))
      rw [Rooted.normalize_node, hm, ListSortByKey.sort_eq_self _ _ hh.1]
termination_by t => sizeOf t
decreasing_by exact Rooted.child_size_lt label children _ hp

theorem Rooted.normalize_node_perm (label : Option ℕ) {left right : List (ℕ × Rooted)}
    (hp : left.Perm right) (hnd : (Rooted.node label left).labels.Nodup) :
    (Rooted.node label left).normalize = (Rooted.node label right).normalize := by
  rw [Rooted.normalize_node, Rooted.normalize_node]
  congr 1
  apply ListSortByKey.sort_eq_of_perm Prod.fst (hp.map (fun p => (p.1, p.2.normalize)))
  simpa only [List.map_map, Function.comp_def] using root_keys_nodup label left hnd

theorem Rooted.UnorderedEq.normalize_eq {s t : Rooted} (h : s.UnorderedEq t)
    (hnd : s.labels.Nodup) : s.normalize = t.normalize := by
  revert hnd
  induction h with
  | refl => intro _; rfl
  | symm h ih =>
    intro hnd
    apply Eq.symm
    exact ih (by rwa [h.data_eq.2.2])
  | trans h1 h2 ih1 ih2 =>
    intro hnd
    exact (ih1 hnd).trans (ih2 (by rwa [← h1.data_eq.2.2]))
  | perm label hp => exact Rooted.normalize_node_perm label hp
  | @child label edge left right before after he ih =>
    intro hnd
    have hc : left.labels.Nodup := Multiset.nodup_of_le
      (Rooted.child_labels_le label (before ++ (edge, left) :: after) (edge, left)
        (List.mem_append.mpr (Or.inr List.mem_cons_self))) hnd
    simp only [Rooted.normalize_node, List.map_append, List.map_cons, ih hc]

theorem Rooted.canonical_unique {s t : Rooted} (h : s.UnorderedEq t) (hnd : s.labels.Nodup)
    (hs : s.Canonical) (ht : t.Canonical) : s = t := by
  have he := h.normalize_eq hnd
  rwa [s.normalize_eq_self hs, t.normalize_eq_self ht] at he

theorem Rooted.exists_unique_canonical (t : Rooted) (hnd : t.labels.Nodup) :
    ∃! s : Rooted, s.Canonical ∧ s.UnorderedEq t := by
  refine ⟨t.normalize, ⟨t.normalize_canonical hnd, t.normalize_related⟩, ?_⟩
  intro s hs
  have hnds : s.labels.Nodup := by rwa [hs.2.data_eq.2.2]
  have he := hs.2.normalize_eq hnds
  rwa [s.normalize_eq_self hs.1] at he

end Freezing1.BinaryBijection
