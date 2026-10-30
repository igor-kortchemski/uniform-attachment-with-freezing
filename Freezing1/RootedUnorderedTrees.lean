module

public import Freezing1.BinaryTreeSourceDomain

/-!
# Unordered rooted trees as sibling-permutation quotients

The relation is the equivalence and subtree-congruence closure of arbitrary
sibling permutations. Thus sibling order is auxiliary coding data. Numeric
labels, active vertices, and the source's local increasing conditions are
invariant under this relation.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

inductive Rooted.UnorderedEq : Rooted → Rooted → Prop
  | refl (t : Rooted) : UnorderedEq t t
  | symm {s t : Rooted} : UnorderedEq s t → UnorderedEq t s
  | trans {r s t : Rooted} : UnorderedEq r s → UnorderedEq s t → UnorderedEq r t
  | perm (label : Option ℕ) {left right : List (ℕ × Rooted)} (hp : left.Perm right) :
      UnorderedEq (.node label left) (.node label right)
  | child (label : Option ℕ) (edge : ℕ) {left right : Rooted}
      (before after : List (ℕ × Rooted)) (he : UnorderedEq left right) :
      UnorderedEq (.node label (before ++ (edge, left) :: after))
        (.node label (before ++ (edge, right) :: after))

def Rooted.unorderedSetoid : Setoid Rooted where
  r := Rooted.UnorderedEq
  iseqv := ⟨Rooted.UnorderedEq.refl, Rooted.UnorderedEq.symm, Rooted.UnorderedEq.trans⟩

theorem Rooted.UnorderedEq.data_eq {s t : Rooted} (h : s.UnorderedEq t) :
    s.vertexCount = t.vertexCount ∧ s.activeCount = t.activeCount ∧ s.labels = t.labels := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | symm h ih => exact ⟨ih.1.symm, ih.2.1.symm, ih.2.2.symm⟩
  | trans h1 h2 ih1 ih2 => exact ⟨ih1.1.trans ih2.1, ih1.2.1.trans ih2.2.1, ih1.2.2.trans ih2.2.2⟩
  | perm label hp =>
    refine ⟨?_, ?_, ?_⟩
    · rw [Rooted.vertexCount_node, Rooted.vertexCount_node,
        (hp.map (fun p => p.2.vertexCount)).sum_eq]
    · rw [Rooted.activeCount_node, Rooted.activeCount_node,
        (hp.map (fun p => p.2.activeCount)).sum_eq]
    · rw [Rooted.labels_node, Rooted.labels_node,
        (hp.map (fun p => ({p.1} : Multiset ℕ) + p.2.labels)).sum_eq]
  | child label edge before after he ih =>
    simp only [Rooted.vertexCount_node, Rooted.activeCount_node, Rooted.labels_node,
      List.map_append, List.map_cons, List.sum_append, List.sum_cons, ih.1, ih.2.1, ih.2.2]
    trivial

theorem Rooted.UnorderedEq.rootAbove_iff {s t : Rooted} (h : s.UnorderedEq t) (bound : ℕ) :
    s.rootAbove bound ↔ t.rootAbove bound := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  | perm label hp =>
    simp only [Rooted.rootAbove]
    constructor
    · rintro ⟨hl, hall⟩
      exact ⟨hl, fun p hp' => hall p (hp.mem_iff.mpr hp')⟩
    · rintro ⟨hl, hall⟩
      exact ⟨hl, fun p hp' => hall p (hp.mem_iff.mp hp')⟩
  | child label edge before after he ih => simp [Rooted.rootAbove, or_imp, forall_and]

/-- The source's increasing conditions without any sibling order. -/
def Rooted.HeapIncreasing : Rooted → Prop
  | .node _ [] => True
  | .node label ((edge, child) :: rest) =>
      child.HeapIncreasing ∧ (Rooted.node label rest).HeapIncreasing ∧
        child.rootAbove edge ∧ labelAbove edge label
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem Rooted.heapIncreasing_node_iff (label : Option ℕ) (children : List (ℕ × Rooted)) :
    (Rooted.node label children).HeapIncreasing ↔
      ∀ p ∈ children, p.2.HeapIncreasing ∧ p.2.rootAbove p.1 ∧ labelAbove p.1 label := by
  induction children with
  | nil => simp [Rooted.HeapIncreasing]
  | cons p rest ih =>
    rcases p with ⟨edge, child⟩
    rw [Rooted.HeapIncreasing, ih]
    constructor
    · rintro ⟨hc, hr, hb, hl⟩ p hp
      rcases List.mem_cons.mp hp with he | hp
      · simpa only [he] using (show child.HeapIncreasing ∧ child.rootAbove edge ∧
          labelAbove edge label from ⟨hc, hb, hl⟩)
      · exact hr p hp
    · intro hall
      have hh := hall (edge, child) (by simp)
      exact ⟨hh.1, fun p hp => hall p (List.mem_cons_of_mem _ hp), hh.2.1, hh.2.2⟩

theorem Rooted.UnorderedEq.heapIncreasing_iff {s t : Rooted} (h : s.UnorderedEq t) :
    s.HeapIncreasing ↔ t.HeapIncreasing := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  | perm label hp =>
    rw [Rooted.heapIncreasing_node_iff, Rooted.heapIncreasing_node_iff]
    exact ⟨fun hall p hp' => hall p (hp.mem_iff.mpr hp'),
      fun hall p hp' => hall p (hp.mem_iff.mp hp')⟩
  | child label edge before after he ih =>
    rw [Rooted.heapIncreasing_node_iff, Rooted.heapIncreasing_node_iff]
    simp only [List.mem_append, List.mem_cons, or_imp, forall_and]
    simp only [forall_eq, ih, he.rootAbove_iff edge]

theorem Rooted.increasing_iff_heap_canonical : ∀ t : Rooted,
    t.Increasing ↔ t.HeapIncreasing ∧ t.Canonical
  | .node _ [] => by simp [Rooted.Increasing, Rooted.HeapIncreasing, Rooted.Canonical]
  | .node label ((edge, child) :: rest) => by
      rw [Rooted.Increasing, Rooted.HeapIncreasing, Rooted.Canonical,
        increasing_iff_heap_canonical child, increasing_iff_heap_canonical (.node label rest)]
      change ((_ ∧ _) ∧ (_ ∧ _) ∧ _ ∧ (labelAbove edge label ∧ ∀ p ∈ rest, edge < p.1)) ↔ _
      tauto
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

end Freezing1.BinaryBijection
