module

import Freezing1.LocalTreeGraph
import Freezing1.AttachmentReciprocalSeries

open Freezing1 Filter
open scoped Classical Topology BigOperators

example (T : LocalTree.Tree) : (LocalTree.graph T).IsTree := LocalTree.graph_isTree T

example (T : LocalTree.Tree) (v : LocalTree.Vertex T) :
    ((LocalTree.graph T).neighborSet v).Finite := LocalTree.finite_neighborSet T v

example (T : LocalTree.Tree) (v : LocalTree.Vertex T) :
    v.val.height = (LocalTree.graph T).dist (LocalTree.root T) v :=
  LocalTree.height_eq_dist T v

example (T : LocalTree.Tree) (h : ℕ) :
    (T.val h : Set LocalTree.VertexRecord) = Subtype.val ''
      {v : LocalTree.Vertex T | (LocalTree.graph T).dist (LocalTree.root T) v ≤ h} :=
  LocalTree.ball_eq_image_dist T h

example (x : SignSequence) (hτ : extinctionTime x = ⊤) :
    Tendsto (fun n => ∑ i ∈ Finset.range n,
      if x (i + 1) then 1 / (activeCount x i : ℝ) else 0) atTop atTop :=
  Forward.tendsto_sum_attachmentHazard_atTop x hτ

#print axioms Freezing1.LocalTree.vertex_birth_injective
#print axioms Freezing1.LocalTree.graph_connected
#print axioms Freezing1.LocalTree.graph_isAcyclic
#print axioms Freezing1.LocalTree.height_eq_dist
#print axioms Freezing1.LocalTree.finite_neighborSet
#print axioms Freezing1.LocalTree.ball_eq_image_dist
#print axioms Freezing1.LocalTree.graph_adj_iff_union_ballGraph
#print axioms Freezing1.Forward.tendsto_sum_attachmentHazard_atTop
#print axioms Freezing1.Forward.not_summable_attachmentHazard
