module

public import Freezing1.ForwardLaw

/-!
# Frozen labels are later than every incident edge

Forward nonroot vertex IDs are their incoming edge times. Every new edge
joins a fresh, larger ID to an old active vertex, so its timestamp is the
maximum of its endpoint IDs. The invariant below proves the source's strict
ordering requirement for frozen vertex labels.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory

def FrozenEdgeOrder (s : State) : Prop :=
  ∀ u v t, s.frozenAt u = some t → s.graph.Adj u v → max u v < t

theorem initial_frozen_edge_order : FrozenEdgeOrder initial := by
  intro u v t ht _
  simp [initial] at ht

theorem FrozenEdgeOrder.attach {n : ℕ} {s : State} (h : FrozenEdgeOrder s)
    (hs : ValidAt n s) {v : ℕ} (hv : v ∈ s.active) :
    FrozenEdgeOrder (attach s (n + 1) v) := by
  intro u w t hut huw
  have hune : u ≠ n + 1 := by intro he; simp [Forward.attach, he] at hut
  have huto : s.frozenAt u = some t := by simpa [Forward.attach, hune] using hut
  change s.graph.Adj u w ∨ (SimpleGraph.edge v (n + 1)).Adj u w at huw
  rcases huw with hold | hnew
  · exact h u w t huto hold
  · simp only [SimpleGraph.edge_adj] at hnew
    rcases hnew with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
    · have hvnone := (hs.active_iff _ (hs.active_subset hv)).mp hv
      rw [hvnone] at huto
      contradiction
    · exact False.elim (hune rfl)

theorem FrozenEdgeOrder.freeze {n : ℕ} {s : State} (h : FrozenEdgeOrder s)
    (hs : ValidAt n s) (v : ℕ) : FrozenEdgeOrder (freeze s (n + 1) v) := by
  intro u w t hut huw
  by_cases huv : u = v
  · simp only [Forward.freeze, huv, Function.update_self, Option.some.injEq] at hut
    have hadj : s.graph.Adj u w := huw
    have hu := hs.vertices_le u (hs.adj_mem hadj).1
    have hw := hs.vertices_le w (hs.adj_mem hadj).2
    subst t
    exact Nat.lt_succ_of_le (max_le hu hw)
  · have huto : s.frozenAt u = some t := by simpa [Forward.freeze, huv] using hut
    exact h u w t huto huw

theorem FrozenEdgeOrder.step {n : ℕ} {s : State} (h : FrozenEdgeOrder s)
    (hs : ValidAt n s) (sign : Bool) (v : ℕ) :
    FrozenEdgeOrder (step s (n + 1) sign v) := by
  unfold Forward.step
  split_ifs with hv
  · exact h.attach hs hv
  · exact h.freeze hs v
  · exact h

/-- The ordering condition holds for every actual forward marginal, including
absorbed states. It does not assume the terminal point-mass formula. -/
theorem treeLaw_frozen_edge_order (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, FrozenEdgeOrder s := by
  have h := treeLaw_ae_induction x (fun n s => ValidAt n s ∧ FrozenEdgeOrder s)
    ⟨initial_valid, initial_frozen_edge_order⟩
    (fun k s hs _ => ⟨hs.1.mono (Nat.le_succ k), hs.2⟩)
    (fun k s hs v _ => ⟨hs.1.step _ _, hs.2.step hs.1 _ _⟩) n
  exact h.mono fun _ hs => hs.2

end Freezing1.Forward
