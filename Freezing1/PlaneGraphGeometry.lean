module

public import Freezing1.PlaneFiniteGraph

/-!
# Root paths and metric bounds in the actual plane graph
-/

@[expose] public section

namespace Freezing1.PlaneForward

open scoped Classical

theorem Valid.exists_root_walk {s : State} (hs : Valid s)
    (u : PlaneTree.Address) (hu : u ∈ s.vertices) :
    ∃ p : (parentGraph s).Walk [] u, p.length = u.length := by
  induction u using List.reverseRecOn with
  | nil => exact ⟨.nil, rfl⟩
  | append_singleton u j ih =>
    have hu' := hs.prefix_closed u [j] hu
    obtain ⟨p, hp⟩ := ih hu'
    have ha : (parentGraph s).Adj u (u ++ [j]) := ⟨hu', hu, Or.inl ⟨j, rfl⟩⟩
    exact ⟨p.concat ha, by simp [hp]⟩

theorem parentGraph_adj_length_le {s : State} {u v : PlaneTree.Address}
    (ha : (parentGraph s).Adj u v) : v.length ≤ u.length + 1 := by
  rcases ha.2.2 with ⟨j, rfl⟩ | ⟨j, hj⟩
  · simp
  · have hh := congrArg List.length hj
    simp only [List.length_append, List.length_singleton] at hh
    omega

theorem parentGraph_walk_length_bound {s : State} {u v : PlaneTree.Address}
    (p : (parentGraph s).Walk u v) : v.length ≤ u.length + p.length := by
  induction p with
  | nil => simp
  | cons ha p ih =>
    have hh := parentGraph_adj_length_le ha
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem Valid.parentGraph_root_dist {s : State} (hs : Valid s)
    {u : PlaneTree.Address} (hu : u ∈ s.vertices) :
    (parentGraph s).dist [] u = u.length := by
  obtain ⟨p, hp⟩ := hs.exists_root_walk u hu
  apply le_antisymm
  · exact ((parentGraph s).dist_le p).trans_eq hp
  · obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
    simpa only [List.length_nil, zero_add, hq] using parentGraph_walk_length_bound q

theorem Valid.parentGraph_dist_le_lengths {s : State} (hs : Valid s)
    {u v : PlaneTree.Address} (hu : u ∈ s.vertices) (hv : v ∈ s.vertices) :
    (parentGraph s).dist u v ≤ u.length + v.length := by
  obtain ⟨p, hp⟩ := hs.exists_root_walk u hu
  obtain ⟨q, hq⟩ := hs.exists_root_walk v hv
  have hh := (parentGraph s).dist_le (p.reverse.append q)
  simpa only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hp, hq] using hh

end Freezing1.PlaneForward
