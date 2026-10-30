module

public import Freezing1.PlaneLabelledIsoDistance

/-!
# Rooted labelled graph isomorphisms are exactly the parent-preserving witnesses

The parent relation is recovered from graph adjacency and root distance.
Thus it is not an extra order constraint on the forgetting-order quotient.
-/

@[expose] public section

namespace Freezing1.PlaneLabelled

variable {V E : Type*} {S T : Tree V E}

noncomputable def graphAddressEquiv
    (e : (PlaneTree.graph (shape S)).Iso (PlaneTree.graph (shape T))) :
    Vertex (shape S) ≃ Vertex (shape T) :=
  (PlaneTree.addressEquiv (shape S)).trans
    (e.toEquiv.trans (PlaneTree.addressEquiv (shape T)).symm)

theorem graphAddressEquiv_vertex
    (e : (PlaneTree.graph (shape S)).Iso (PlaneTree.graph (shape T))) (u : Vertex (shape S)) :
    PlaneTree.vertexOfAddress (shape T) (graphAddressEquiv e u) =
      e (PlaneTree.vertexOfAddress (shape S) u) := by
  change (PlaneTree.addressEquiv (shape T))
    ((PlaneTree.addressEquiv (shape T)).symm (e ((PlaneTree.addressEquiv (shape S)) u))) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem graphAddressEquiv_symm
    (e : (PlaneTree.graph (shape S)).Iso (PlaneTree.graph (shape T))) :
    graphAddressEquiv e.symm = (graphAddressEquiv e).symm := by
  apply Equiv.ext
  intro u
  rfl

theorem graphAddressEquiv_root
    (e : (PlaneTree.graph (shape S)).Iso (PlaneTree.graph (shape T)))
    (hr : e (LocalTree.root (PlaneTree.auxiliaryTree (shape S))) =
      LocalTree.root (PlaneTree.auxiliaryTree (shape T))) :
    graphAddressEquiv e (rootVertex S) = rootVertex T := by
  apply (PlaneTree.addressEquiv (shape T)).injective
  change PlaneTree.vertexOfAddress (shape T) (graphAddressEquiv e (rootVertex S)) =
    PlaneTree.vertexOfAddress (shape T) (rootVertex T)
  rw [graphAddressEquiv_vertex]
  simpa only [rootVertex, PlaneTree.vertexOfAddress_root] using hr

theorem graphAddressEquiv_length_le
    (e : (PlaneTree.graph (shape S)).Iso (PlaneTree.graph (shape T)))
    (hr : e (LocalTree.root (PlaneTree.auxiliaryTree (shape S))) =
      LocalTree.root (PlaneTree.auxiliaryTree (shape T))) (u : Vertex (shape S)) :
    (graphAddressEquiv e u).val.length ≤ u.val.length := by
  obtain ⟨p, hp⟩ := LocalTree.exists_root_walk (PlaneTree.auxiliaryTree (shape S))
    (PlaneTree.vertexOfAddress (shape S) u)
  let p' : (PlaneTree.graph (shape S)).Walk (LocalTree.root (PlaneTree.auxiliaryTree (shape S)))
    (PlaneTree.vertexOfAddress (shape S) u) := p
  have hp' : p'.length = u.val.length := hp
  have hl := SimpleGraph.Walk.length_map (f := e.toHom) (p := p')
  have hh := (PlaneTree.graph (shape T)).dist_le (p'.map e.toHom)
  change (PlaneTree.graph (shape T)).dist
    (e (LocalTree.root (PlaneTree.auxiliaryTree (shape S))))
    (e (PlaneTree.vertexOfAddress (shape S) u)) ≤ (p'.map e.toHom).length at hh
  rw [hr, ← graphAddressEquiv_vertex, PlaneTree.graph_dist_address] at hh
  simpa only [hl, hp'] using hh

theorem graphAddressEquiv_length_eq
    (e : (PlaneTree.graph (shape S)).Iso (PlaneTree.graph (shape T)))
    (hr : e (LocalTree.root (PlaneTree.auxiliaryTree (shape S))) =
      LocalTree.root (PlaneTree.auxiliaryTree (shape T))) (u : Vertex (shape S)) :
    (graphAddressEquiv e u).val.length = u.val.length := by
  have hsym : e.symm (LocalTree.root (PlaneTree.auxiliaryTree (shape T))) =
      LocalTree.root (PlaneTree.auxiliaryTree (shape S)) := by
    apply e.injective
    change e.toEquiv (e.toEquiv.symm _) = e.toEquiv _
    rw [Equiv.apply_symm_apply]
    exact hr.symm
  apply le_antisymm (graphAddressEquiv_length_le e hr u)
  simpa only [graphAddressEquiv_symm, Equiv.symm_apply_apply] using
    graphAddressEquiv_length_le e.symm hsym (graphAddressEquiv e u)

theorem parent_length_succ {T : PlaneTree.Tree} {u v : Vertex T} (hp : Parent u v) :
    u.val.length + 1 = v.val.length := by
  have hpos : 0 < v.val.length := List.length_pos_iff.mpr hp.1
  have hh := congrArg List.length hp.2
  simp only [List.length_dropLast] at hh
  omega

theorem parent_iff_graph_adj_length (T : Tree V E) (u v : Vertex (shape T)) :
    Parent u v ↔ (PlaneTree.graph (shape T)).Adj (PlaneTree.vertexOfAddress _ u)
      (PlaneTree.vertexOfAddress _ v) ∧ u.val.length + 1 = v.val.length := by
  rw [PlaneTree.graph_adj_address]
  constructor
  · intro hp
    have hl := parent_length_succ hp
    refine ⟨⟨?_, Or.inr hp⟩, hl⟩
    intro he
    have hh := congrArg (fun u : Vertex (shape T) => u.val.length) he
    omega
  · rintro ⟨⟨_, hp | hp⟩, hl⟩
    · have hh := parent_length_succ hp
      omega
    · exact hp

noncomputable def UnorderedIso.of_graphIso
    (e : (PlaneTree.graph (shape S)).Iso (PlaneTree.graph (shape T)))
    (hr : e (LocalTree.root (PlaneTree.auxiliaryTree (shape S))) =
      LocalTree.root (PlaneTree.auxiliaryTree (shape T)))
    (hv : ∀ u, vertexSlot S u.val = vertexSlot T (graphAddressEquiv e u).val)
    (he : ∀ u, edgeSlot S u.val = edgeSlot T (graphAddressEquiv e u).val) : UnorderedIso S T where
  toEquiv := graphAddressEquiv e
  root_eq := graphAddressEquiv_root e hr
  parent_iff u v := by
    rw [parent_iff_graph_adj_length, parent_iff_graph_adj_length,
      graphAddressEquiv_vertex, graphAddressEquiv_vertex,
      graphAddressEquiv_length_eq e hr, graphAddressEquiv_length_eq e hr]
    exact and_congr e.map_rel_iff.symm Iff.rfl
  vertex_labels := hv
  edge_labels := he

theorem UnorderedIso.graphAddressEquiv_graphIso (e : UnorderedIso S T) :
    graphAddressEquiv e.graphIso = e.toEquiv := by
  apply Equiv.ext
  intro u
  apply (PlaneTree.addressEquiv (shape T)).injective
  exact (graphAddressEquiv_vertex e.graphIso u).trans (e.graphIso_vertex u)

theorem nonempty_unorderedIso_iff_graphIso (S T : Tree V E) :
    Nonempty (UnorderedIso S T) ↔
      ∃ e : (PlaneTree.graph (shape S)).Iso (PlaneTree.graph (shape T)),
        e (LocalTree.root (PlaneTree.auxiliaryTree (shape S))) =
          LocalTree.root (PlaneTree.auxiliaryTree (shape T)) ∧
        (∀ u, vertexSlot S u.val = vertexSlot T (graphAddressEquiv e u).val) ∧
        (∀ u, edgeSlot S u.val = edgeSlot T (graphAddressEquiv e u).val) := by
  constructor
  · rintro ⟨e⟩
    refine ⟨e.graphIso, e.graphIso_root, ?_, ?_⟩
    · simpa only [e.graphAddressEquiv_graphIso] using e.vertex_labels
    · simpa only [e.graphAddressEquiv_graphIso] using e.edge_labels
  · rintro ⟨e, hr, hv, he⟩
    exact ⟨UnorderedIso.of_graphIso e hr hv he⟩

end Freezing1.PlaneLabelled
