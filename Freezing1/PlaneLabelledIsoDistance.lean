module

public import Freezing1.PlaneLabelledGraphIso

/-! An actual rooted labelled isomorphism preserves every radius. -/

@[expose] public section

namespace Freezing1.PlaneLabelled

variable {V E : Type*} {S T : Tree V E}

theorem UnorderedIso.graphIso_vertex (e : UnorderedIso S T) (u : Vertex (shape S)) :
    e.graphIso (PlaneTree.vertexOfAddress (shape S) u) =
      PlaneTree.vertexOfAddress (shape T) (e.toEquiv u) := by
  change (PlaneTree.addressEquiv (shape T))
    (e.toEquiv ((PlaneTree.addressEquiv (shape S)).symm ((PlaneTree.addressEquiv (shape S)) u))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem UnorderedIso.graphIso_root (e : UnorderedIso S T) :
    e.graphIso (LocalTree.root (PlaneTree.auxiliaryTree (shape S))) =
      LocalTree.root (PlaneTree.auxiliaryTree (shape T)) := by
  rw [← PlaneTree.vertexOfAddress_root (shape S), e.graphIso_vertex]
  change PlaneTree.vertexOfAddress (shape T) (e.toEquiv (rootVertex S)) = _
  rw [e.root_eq]
  exact PlaneTree.vertexOfAddress_root _

theorem UnorderedIso.length_le (e : UnorderedIso S T) (u : Vertex (shape S)) :
    (e.toEquiv u).val.length ≤ u.val.length := by
  obtain ⟨p, hp⟩ := LocalTree.exists_root_walk (PlaneTree.auxiliaryTree (shape S))
    (PlaneTree.vertexOfAddress (shape S) u)
  change p.length = u.val.length at hp
  let p' : (PlaneTree.graph (shape S)).Walk (LocalTree.root (PlaneTree.auxiliaryTree (shape S)))
    (PlaneTree.vertexOfAddress (shape S) u) := p
  have hp' : p'.length = u.val.length := hp
  have hl := SimpleGraph.Walk.length_map (f := e.graphIso.toHom) (p := p')
  have hh := (PlaneTree.graph (shape T)).dist_le (p'.map e.graphIso.toHom)
  change (PlaneTree.graph (shape T)).dist
    (e.graphIso (LocalTree.root (PlaneTree.auxiliaryTree (shape S))))
    (e.graphIso (PlaneTree.vertexOfAddress (shape S) u)) ≤ (p'.map e.graphIso.toHom).length at hh
  rw [e.graphIso_root, e.graphIso_vertex, PlaneTree.graph_dist_address] at hh
  simpa only [hl, hp'] using hh

theorem UnorderedIso.length_eq (e : UnorderedIso S T) (u : Vertex (shape S)) :
    (e.toEquiv u).val.length = u.val.length := by
  apply le_antisymm (e.length_le u)
  simpa only [UnorderedIso.symm, Equiv.symm_apply_apply] using e.symm.length_le (e.toEquiv u)

end Freezing1.PlaneLabelled
