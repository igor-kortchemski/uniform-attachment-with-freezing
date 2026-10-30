module

public import Freezing1.RootedForestDistance

/-! # Distance on the actual finite vertex carrier -/

@[expose] public section

namespace Freezing1.RootedForest

variable {V : Type*} [DecidableEq V]

set_option backward.isDefEq.respectTransparency false in
/-- Distance between existing vertices is exactly distance in the induced
finite graph; the unused isolated ambient labels have no effect. -/
theorem toGraph_dist_eq (F : RootedForest V) (u v : {w // w ∈ F.vertices}) :
    F.toGraph.dist u v = F.graph.dist u.val v.val := by
  by_cases hr : F.graph.Reachable u.val v.val
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    let p' : F.toGraph.Walk u v := p.induce (F.vertices : Set V) (F.walk_support_mem p u.property)
    have hp' : p'.length = p.length := by
      have hh := congrArg SimpleGraph.Walk.length
        (SimpleGraph.Walk.map_induce (s := (F.vertices : Set V)) p (F.walk_support_mem p u.property))
      simpa only [SimpleGraph.Walk.length_map] using hh
    have hr' : F.toGraph.Reachable u v := ⟨p'⟩
    obtain ⟨q, hq⟩ := hr'.exists_walk_length_eq_dist
    apply le_antisymm
    · have hh := F.toGraph.dist_le p'
      simpa only [hp', hp] using hh
    · have hh := F.graph.dist_le
        (q.map (SimpleGraph.Embedding.induce (F.vertices : Set V)).toHom)
      change F.graph.dist u.val v.val ≤
        (q.map (SimpleGraph.Embedding.induce (F.vertices : Set V)).toHom).length at hh
      rw [SimpleGraph.Walk.length_map, hq] at hh
      exact hh
  · have hr' : ¬F.toGraph.Reachable u v := by
      rintro ⟨p⟩
      exact hr ⟨p.map (SimpleGraph.Embedding.induce (F.vertices : Set V)).toHom⟩
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hr', SimpleGraph.dist_eq_zero_of_not_reachable hr]

/-- The stored depth is the actual root distance in the finite induced graph. -/
theorem depth_eq_tree_dist (F : RootedForest V) {v : V} (hv : v ∈ F.vertices) :
    F.depth v = F.toGraph.dist ⟨F.root v, F.root_mem v hv⟩ ⟨v, hv⟩ := by
  rw [F.toGraph_dist_eq]
  exact F.depth_eq_dist hv

end Freezing1.RootedForest
