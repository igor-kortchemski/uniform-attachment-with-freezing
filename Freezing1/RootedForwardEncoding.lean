module

public import Freezing1.ForwardIntrinsicSupport
public import Freezing1.UnorderedBinaryBijection

/-!
# Encoding labelled rooted trees as forward states

An intrinsic labelled rooted tree (`Rooted`: children carry the label of their
incoming edge, a vertex label `none` means `a`, i.e. active) is read as a forward
state whose vertex identifiers are the edge labels (the attachment times) and the
root `0`. The recursive predicate `Rooted.Encodes` says that a state matches a tree
node with incoming identifier `i`: the state's freezing label at `i` is the node's
label, and every child edge `e` has parent `i` and height one more than `i`.
`Rooted.IsEncoding` adds the vertex set, the canonical defaults, the active set and
the parent graph. Existence (for distinct positive edge labels) and uniqueness of
the encoding are proved, and the encoding does not depend on sibling order.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

/-- One vertex of a rooted tree: its identifier (the label of its incoming edge, `0` for the
root), the identifier of its parent, its depth and its vertex label (`none` is active). -/
structure NodeRec where
  vertex : ℕ
  parent : ℕ
  depth : ℕ
  label : Option ℕ

/-- All vertex records of a tree whose root has identifier `i`, parent identifier `p` and
depth `d`; the root's own record comes last. -/
def Rooted.nodeRecs : Rooted → ℕ → ℕ → ℕ → List NodeRec
  | .node label [], i, p, d => [⟨i, p, d, label⟩]
  | .node label ((e, c) :: rest), i, p, d =>
      c.nodeRecs e i (d + 1) ++ (Rooted.node label rest).nodeRecs i p d
termination_by t _ _ _ => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- `s` matches the tree `t` whose root has identifier `i`: the freezing label of `i` is the
root label and every child edge `e` has parent `i` and height `height i + 1`, recursively. -/
def Rooted.Encodes (s : Forward.State) : Rooted → ℕ → Prop
  | .node label [], i => s.frozenAt i = label
  | .node label ((e, c) :: rest), i =>
      c.Encodes s e ∧ s.parent e = i ∧ s.height e = s.height i + 1 ∧
        (Rooted.node label rest).Encodes s i
termination_by t _ => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem Rooted.encodes_node_iff (s : Forward.State) (label : Option ℕ)
    (children : List (ℕ × Rooted)) (i : ℕ) :
    (Rooted.node label children).Encodes s i ↔
      s.frozenAt i = label ∧ ∀ p ∈ children,
        s.parent p.1 = i ∧ s.height p.1 = s.height i + 1 ∧ p.2.Encodes s p.1 := by
  induction children with
  | nil => simp [Rooted.Encodes]
  | cons p rest ih =>
    rcases p with ⟨e, c⟩
    rw [Rooted.Encodes, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-- The state data attached to a vertex record. -/
def NodeRec.Holds (s : Forward.State) (r : NodeRec) : Prop :=
  s.parent r.vertex = r.parent ∧ s.height r.vertex = r.depth ∧ s.frozenAt r.vertex = r.label

theorem Rooted.own_mem (label : Option ℕ) (children : List (ℕ × Rooted)) (i p d : ℕ) :
    (⟨i, p, d, label⟩ : NodeRec) ∈ (Rooted.node label children).nodeRecs i p d := by
  induction children with
  | nil => simp [Rooted.nodeRecs]
  | cons q rest ih =>
    rcases q with ⟨e, c⟩
    rw [Rooted.nodeRecs]
    exact List.mem_append_right _ ih

/-- The recursive encoding predicate is the same as the state matching every vertex record. -/
theorem Rooted.encodes_iff_forall_mem (s : Forward.State) (t : Rooted) (i p d : ℕ) :
    s.parent i = p → s.height i = d →
      (t.Encodes s i ↔ ∀ r ∈ t.nodeRecs i p d, r.Holds s) := by
  fun_induction Rooted.nodeRecs t i p d with
  | case1 label i p d =>
    intro hp hd
    simp [Rooted.Encodes, NodeRec.Holds, hp, hd]
  | case2 label e c rest i p d ihc ihr =>
    intro hp hd
    rw [Rooted.Encodes, List.forall_mem_append]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨(ihc h2 (by omega)).mp h1, (ihr hp hd).mp h4⟩
    · rintro ⟨h1, h4⟩
      cases c with
      | node lc chs =>
        have h0 := h1 _ (Rooted.own_mem lc chs e i (d + 1))
        have h2 : s.parent e = i := h0.1
        have h3 : s.height e = d + 1 := h0.2.1
        exact ⟨(ihc h2 h3).mpr h1, h2, by omega, (ihr hp hd).mpr h4⟩

theorem Rooted.nodeRecs_vertices (t : Rooted) (i p d : ℕ) :
    (((t.nodeRecs i p d).map NodeRec.vertex : List ℕ) : Multiset ℕ) = i ::ₘ t.edgeLabels := by
  fun_induction Rooted.nodeRecs t i p d with
  | case1 label i p d => simp [Rooted.edgeLabels]
  | case2 label e c rest i p d ihc ihr =>
    rw [Rooted.edgeLabels, List.map_append, ← Multiset.coe_add, ihc, ihr]
    simp only [← Multiset.singleton_add]
    abel

/-- The `v`-indexed data of the first record with vertex `v`; the default `a` if there is none. -/
def lookupRec {α : Type} (f : NodeRec → α) (a : α) (v : ℕ) : List NodeRec → α
  | [] => a
  | r :: rs => if r.vertex = v then f r else lookupRec f a v rs

theorem lookupRec_of_mem {α : Type} (f : NodeRec → α) (a : α) {l : List NodeRec}
    (hnd : (l.map NodeRec.vertex).Nodup) {r : NodeRec} (hr : r ∈ l) :
    lookupRec f a r.vertex l = f r := by
  induction l with
  | nil => simp at hr
  | cons x rs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [lookupRec]
    rcases List.mem_cons.mp hr with rfl | hr
    · simp
    · have hne : x.vertex ≠ r.vertex := fun h => hnd.1 (h ▸ List.mem_map_of_mem hr)
      simp [hne, ih hnd.2 hr]

theorem lookupRec_of_forall_ne {α : Type} (f : NodeRec → α) (a : α) {v : ℕ} {l : List NodeRec}
    (h : ∀ r ∈ l, r.vertex ≠ v) : lookupRec f a v l = a := by
  induction l with
  | nil => rfl
  | cons x rs ih =>
    have hx := h x List.mem_cons_self
    simpa [lookupRec, hx] using ih (fun r hr => h r (List.mem_cons_of_mem _ hr))

/-- The vertex identifiers of the encoding: the root `0` and the edge labels. -/
def Rooted.vertexSet (t : Rooted) : Finset ℕ := insert 0 t.edgeLabels.toFinset

theorem Rooted.mem_vertexSet_iff (t : Rooted) (v : ℕ) :
    v ∈ t.vertexSet ↔ ∃ r ∈ t.nodeRecs 0 0 0, r.vertex = v := by
  have h := congrArg (fun m : Multiset ℕ => v ∈ m) (t.nodeRecs_vertices 0 0 0)
  simp only [Multiset.mem_coe, List.mem_map, Multiset.mem_cons, eq_iff_iff] at h
  rw [Rooted.vertexSet, Finset.mem_insert, Multiset.mem_toFinset]
  rw [← h]

/-- The explicit encoding state: parent, height and freezing label are read off the first vertex
record with the given identifier (so they are the defaults outside the vertex set). -/
noncomputable def Rooted.toState (t : Rooted) : Forward.State where
  vertices := t.vertexSet
  active := t.vertexSet.filter (fun v => lookupRec NodeRec.label none v (t.nodeRecs 0 0 0) = none)
  graph := SimpleGraph.fromRel (fun u v => u ∈ t.vertexSet ∧ v ∈ t.vertexSet ∧ u ≠ 0 ∧
    lookupRec NodeRec.parent 0 u (t.nodeRecs 0 0 0) = v)
  parent := fun v => lookupRec NodeRec.parent 0 v (t.nodeRecs 0 0 0)
  height := fun v => lookupRec NodeRec.depth 0 v (t.nodeRecs 0 0 0)
  frozenAt := fun v => lookupRec NodeRec.label none v (t.nodeRecs 0 0 0)

/-- `s` encodes the labelled rooted tree `t`: its vertices are `0` and the edge labels of `t`;
`parent`, `height` and the freezing label `frozenAt` follow the tree (`Rooted.Encodes`, the root
having identifier `0`); the data are canonical (default) outside the vertex set; the active set
is the set of vertices without freezing label; the graph is the parent adjacency. -/
structure Rooted.IsEncoding (t : Rooted) (s : Forward.State) : Prop where
  vertices_eq : s.vertices = insert 0 t.edgeLabels.toFinset
  encodes : t.Encodes s 0
  defaults : Forward.CanonicalDefaults s
  height_zero : s.height 0 = 0
  active_eq : s.active = s.vertices.filter (fun v => s.frozenAt v = none)
  graph_eq : s.graph = SimpleGraph.fromRel
    (fun u v => u ∈ s.vertices ∧ v ∈ s.vertices ∧ u ≠ 0 ∧ s.parent u = v)

theorem Rooted.IsEncoding.holds {t : Rooted} {s : Forward.State} (h : t.IsEncoding s) :
    ∀ r ∈ t.nodeRecs 0 0 0, r.Holds s :=
  (Rooted.encodes_iff_forall_mem s t 0 0 0 h.defaults.parent_zero h.height_zero).mp h.encodes

theorem Rooted.IsEncoding.mem_vertices_iff {t : Rooted} {s : Forward.State}
    (h : t.IsEncoding s) (v : ℕ) : v ∈ s.vertices ↔ ∃ r ∈ t.nodeRecs 0 0 0, r.vertex = v := by
  rw [h.vertices_eq]
  exact t.mem_vertexSet_iff v

theorem forwardState_ext {s s' : Forward.State} (hv : s.vertices = s'.vertices)
    (ha : s.active = s'.active) (hg : s.graph = s'.graph) (hp : s.parent = s'.parent)
    (hh : s.height = s'.height) (hf : s.frozenAt = s'.frozenAt) : s = s' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := s
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := s'
  simp only at hv ha hg hp hh hf
  subst hv ha hg hp hh hf
  rfl

/-- The encoding of a tree is unique, with no hypothesis on the labels. -/
theorem Rooted.IsEncoding.unique {t : Rooted} {s s' : Forward.State} (h : t.IsEncoding s)
    (h' : t.IsEncoding s') : s = s' := by
  have hV : s.vertices = s'.vertices := h.vertices_eq.trans h'.vertices_eq.symm
  have hpar : s.parent = s'.parent := by
    funext v
    by_cases hv : v ∈ s.vertices
    · obtain ⟨r, hr, rfl⟩ := (h.mem_vertices_iff v).mp hv
      exact (h.holds r hr).1.trans (h'.holds r hr).1.symm
    · exact (h.defaults.outside v hv).1.trans (h'.defaults.outside v (hV ▸ hv)).1.symm
  have hhei : s.height = s'.height := by
    funext v
    by_cases hv : v ∈ s.vertices
    · obtain ⟨r, hr, rfl⟩ := (h.mem_vertices_iff v).mp hv
      exact (h.holds r hr).2.1.trans (h'.holds r hr).2.1.symm
    · exact (h.defaults.outside v hv).2.1.trans (h'.defaults.outside v (hV ▸ hv)).2.1.symm
  have hfro : s.frozenAt = s'.frozenAt := by
    funext v
    by_cases hv : v ∈ s.vertices
    · obtain ⟨r, hr, rfl⟩ := (h.mem_vertices_iff v).mp hv
      exact (h.holds r hr).2.2.trans (h'.holds r hr).2.2.symm
    · exact (h.defaults.outside v hv).2.2.trans (h'.defaults.outside v (hV ▸ hv)).2.2.symm
  refine forwardState_ext hV ?_ ?_ hpar hhei hfro
  · rw [h.active_eq, h'.active_eq, hV, hfro]
  · rw [h.graph_eq, h'.graph_eq, hV, hpar]

/-- Distinct positive edge labels make the explicit state an encoding. -/
theorem Rooted.toState_isEncoding {t : Rooted} (hid : (0 ::ₘ t.edgeLabels).Nodup) :
    t.IsEncoding t.toState := by
  have hnd : ((t.nodeRecs 0 0 0).map NodeRec.vertex).Nodup := by
    rw [← Multiset.coe_nodup, t.nodeRecs_vertices]
    exact hid
  have hholds : ∀ r ∈ t.nodeRecs 0 0 0, r.Holds t.toState := fun r hr =>
    ⟨lookupRec_of_mem NodeRec.parent 0 hnd hr, lookupRec_of_mem NodeRec.depth 0 hnd hr,
      lookupRec_of_mem NodeRec.label none hnd hr⟩
  have hroot : t.toState.parent 0 = 0 ∧ t.toState.height 0 = 0 := by
    cases t with
    | node label children =>
      have h0 := hholds _ (Rooted.own_mem label children 0 0 0)
      exact ⟨h0.1, h0.2.1⟩
  have hp0 : t.toState.parent 0 = 0 := hroot.1
  have hh0 : t.toState.height 0 = 0 := hroot.2
  refine ⟨rfl, ?_, ⟨hp0, ?_⟩, hh0, rfl, rfl⟩
  · exact (Rooted.encodes_iff_forall_mem _ _ 0 0 0 hp0 hh0).mpr hholds
  · intro v hv
    have hne : ∀ r ∈ t.nodeRecs 0 0 0, r.vertex ≠ v := by
      intro r hr hrv
      exact hv ((t.mem_vertexSet_iff v).mpr ⟨r, hr, hrv⟩)
    exact ⟨lookupRec_of_forall_ne _ _ hne, lookupRec_of_forall_ne _ _ hne,
      lookupRec_of_forall_ne _ _ hne⟩

theorem Rooted.IsEncoding.eq_toState {t : Rooted} {s : Forward.State} (h : t.IsEncoding s)
    (hid : (0 ::ₘ t.edgeLabels).Nodup) : s = t.toState :=
  h.unique (Rooted.toState_isEncoding hid)

/-- Existence of the encoding state. -/
theorem Rooted.exists_isEncoding {t : Rooted} (hid : (0 ::ₘ t.edgeLabels).Nodup) :
    ∃ s : Forward.State, t.IsEncoding s :=
  ⟨t.toState, Rooted.toState_isEncoding hid⟩

theorem Rooted.nodup_zero_cons_edgeLabels {t : Rooted} {A : Finset ℕ} (hA : t.labels = A.val)
    (hpos : ∀ a ∈ A, 0 < a) : (0 ::ₘ t.edgeLabels).Nodup := by
  have hnd : t.labels.Nodup := by rw [hA]; exact A.nodup
  rw [t.labels_eq_parts, Multiset.nodup_add] at hnd
  rw [Multiset.nodup_cons]
  refine ⟨fun h0 => ?_, hnd.1⟩
  have h0' : (0 : ℕ) ∈ t.labels := by
    rw [t.labels_eq_parts]
    exact Multiset.mem_add.mpr (Or.inl h0)
  rw [hA] at h0'
  exact absurd (hpos 0 h0') (lt_irrefl 0)

/-- The encoding conditions do not depend on the order of siblings. -/
theorem Rooted.UnorderedEq.encodes_iff {s t : Rooted} (h : s.UnorderedEq t)
    (st : Forward.State) : ∀ i, s.Encodes st i ↔ t.Encodes st i := by
  induction h with
  | refl => intro i; exact Iff.rfl
  | symm h ih => intro i; exact (ih i).symm
  | trans h1 h2 ih1 ih2 => intro i; exact (ih1 i).trans (ih2 i)
  | perm label hp =>
    intro i
    rw [Rooted.encodes_node_iff, Rooted.encodes_node_iff]
    exact and_congr Iff.rfl
      ⟨fun hall p hp' => hall p (hp.mem_iff.mpr hp'), fun hall p hp' => hall p (hp.mem_iff.mp hp')⟩
  | child label edge before after he ih =>
    intro i
    rw [Rooted.encodes_node_iff, Rooted.encodes_node_iff]
    simp only [List.mem_append, List.mem_cons, or_imp, forall_and, forall_eq, ih]

theorem Rooted.UnorderedEq.isEncoding_iff {s t : Rooted} (h : s.UnorderedEq t)
    (st : Forward.State) : s.IsEncoding st ↔ t.IsEncoding st := by
  have he := h.edge_vertex_labels_eq.1
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨by rw [h1, he], (h.encodes_iff st 0).mp h2, h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨by rw [h1, he], (h.encodes_iff st 0).mpr h2, h3, h4, h5, h6⟩

/-- The explicit encoding state is the same for unordered-equivalent trees. -/
theorem Rooted.UnorderedEq.toState_eq {s t : Rooted} (h : s.UnorderedEq t)
    (hid : (0 ::ₘ s.edgeLabels).Nodup) : s.toState = t.toState := by
  have hid' : (0 ::ₘ t.edgeLabels).Nodup := by rw [← h.edge_vertex_labels_eq.1]; exact hid
  exact ((h.isEncoding_iff _).mp (Rooted.toState_isEncoding hid)).eq_toState hid'

end Freezing1.BinaryBijection
