module

public import Freezing1.ForwardTree

/-!
# The actual finite graph degree of the forward root

The observable counts graph neighbours among the true vertex set. A new
attachment increments it precisely when the selected parent is the root;
freezing preserves the graph and hence the degree.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

noncomputable def rootDegree (s : State) : ℕ :=
  (s.vertices.filter fun v => s.graph.Adj 0 v).card

theorem rootDegree_initial : rootDegree initial = 0 := by simp [rootDegree, initial]

theorem rootDegree_le_vertices_card (s : State) : rootDegree s ≤ s.vertices.card :=
  Finset.card_filter_le _ _

theorem rootNeighbors_attach {n : ℕ} {s : State} (hs : ValidAt n s) (p : ℕ) :
    (attach s (n + 1) p).vertices.filter (fun v => (attach s (n + 1) p).graph.Adj 0 v) =
      if p = 0 then insert (n + 1) (s.vertices.filter fun v => s.graph.Adj 0 v)
      else s.vertices.filter fun v => s.graph.Adj 0 v := by
  classical
  have hfresh : n + 1 ∉ s.vertices := by intro h; have := hs.vertices_le _ h; omega
  have hnotadj : ¬s.graph.Adj 0 (n + 1) := fun h => hfresh (hs.adj_mem h).2
  ext v
  by_cases hp : p = 0 <;> by_cases hv : v = n + 1
  · subst p v
    simp [attach, SimpleGraph.edge_adj, hnotadj]
  · subst p
    simp [attach, SimpleGraph.edge_adj, hv]
  · subst v
    simp [attach, SimpleGraph.edge_adj, hp, Ne.symm hp, hnotadj, hfresh]
  · simp [attach, SimpleGraph.edge_adj, hp, hv]

theorem rootDegree_attach {n : ℕ} {s : State} (hs : ValidAt n s) (p : ℕ) :
    rootDegree (attach s (n + 1) p) = rootDegree s + if p = 0 then 1 else 0 := by
  have hfresh : n + 1 ∉ s.vertices.filter (fun v => s.graph.Adj 0 v) := by
    intro h
    have := hs.vertices_le _ (Finset.mem_filter.mp h).1
    omega
  rw [rootDegree, rootNeighbors_attach hs p]
  by_cases hp : p = 0 <;> simp [hp, rootDegree, Finset.card_insert_of_notMem hfresh]

theorem rootDegree_freeze (s : State) (t p : ℕ) : rootDegree (freeze s t p) = rootDegree s := rfl

theorem rootDegree_step {n : ℕ} {s : State} (hs : ValidAt n s) {p : ℕ}
    (hp : p ∈ s.active) (sign : Bool) :
    rootDegree (step s (n + 1) sign p) =
      rootDegree s + if sign = true ∧ p = 0 then 1 else 0 := by
  rw [step, ite_eq_left hp]
  cases sign <;> simp [rootDegree_freeze, rootDegree_attach hs p]

end Freezing1.Forward
