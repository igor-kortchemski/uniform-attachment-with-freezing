module

public import Freezing1.RootedForwardEncoding

/-!
# Heap-increasing labelled trees encode to schedule-free increasing forward states

For a rooted tree `t` that is heap-increasing (every vertex label exceeds its adjacent edge
labels and every child edge exceeds the incoming edge) and whose labels are exactly
`1, ..., N`, every encoding state (`Rooted.IsEncoding`) satisfies the schedule-free intrinsic
conditions `Forward.IncreasingLabelled N`. The vertex and active counts of the state are the
vertex and active counts of the tree, and the induced schedule has `n - 1` attachments and
`n - k` freezings among `1, ..., N`.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

theorem scheduleOf_eq_true_iff (s : State) (u : ℕ) : scheduleOf s u = true ↔ u ∈ s.vertices := by
  simp [scheduleOf]

end Freezing1.Forward

namespace Freezing1.BinaryBijection

open scoped Classical

/-- The label of the root of a tree. -/
def Rooted.encRootLabel : Rooted → Option ℕ
  | .node label _ => label

/-- Local increasing structure of the vertex records of a heap-increasing tree. Every record
`r` has a vertex label above its identifier; every record other than the root's own has
a parent identifier below its identifier, a parent record one level up whose vertex label
is above `r`'s identifier. -/
theorem Rooted.nodeRecs_spec (t : Rooted) (i p d : ℕ) :
    t.HeapIncreasing → t.rootAbove i → ∀ r ∈ t.nodeRecs i p d,
      labelAbove r.vertex r.label ∧
      (r = ⟨i, p, d, t.encRootLabel⟩ ∨
        (r.parent < r.vertex ∧ ∃ r' ∈ t.nodeRecs i p d, r'.vertex = r.parent ∧
          r.depth = r'.depth + 1 ∧ labelAbove r.vertex r'.label)) := by
  fun_induction Rooted.nodeRecs t i p d with
  | case1 label i p d =>
    intro _ hr r hr'
    have hr'' : r = ⟨i, p, d, label⟩ := by simpa using hr'
    subst hr''
    exact ⟨hr.1, Or.inl rfl⟩
  | case2 label e c rest i p d ihc ihr =>
    intro hHI hroot r hr
    rw [Rooted.HeapIncreasing] at hHI
    obtain ⟨hc, hrest, hce, hel⟩ := hHI
    have hroot' : (Rooted.node label rest).rootAbove i :=
      ⟨hroot.1, fun q hq => hroot.2 q (List.mem_cons_of_mem _ hq)⟩
    have hie : i < e := hroot.2 (e, c) List.mem_cons_self
    rw [List.mem_append] at hr
    rcases hr with hr | hr
    · obtain ⟨h1, h2⟩ := ihc hc hce r hr
      refine ⟨h1, Or.inr ?_⟩
      rcases h2 with h2 | ⟨h3, r', hr', h4, h5, h6⟩
      · subst h2
        exact ⟨hie, ⟨i, p, d, label⟩, List.mem_append_right _ (Rooted.own_mem label rest i p d),
          rfl, rfl, hel⟩
      · exact ⟨h3, r', List.mem_append_left _ hr', h4, h5, h6⟩
    · obtain ⟨h1, h2⟩ := ihr hrest hroot' r hr
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | ⟨h3, r', hr', h4, h5, h6⟩
      · exact Or.inl h2
      · exact Or.inr ⟨h3, r', List.mem_append_right _ hr', h4, h5, h6⟩

theorem Rooted.nodeRecs_labels (t : Rooted) (i p d : ℕ) :
    (((t.nodeRecs i p d).filterMap NodeRec.label : List ℕ) : Multiset ℕ) = t.vertexLabels := by
  fun_induction Rooted.nodeRecs t i p d with
  | case1 label i p d => cases label <;> simp [Rooted.vertexLabels, labelMultiset]
  | case2 label e c rest i p d ihc ihr =>
    rw [Rooted.vertexLabels, List.filterMap_append, ← Multiset.coe_add, ihc, ihr]

theorem Rooted.mem_vertexLabels_iff (t : Rooted) (w : ℕ) :
    w ∈ t.vertexLabels ↔ ∃ r ∈ t.nodeRecs 0 0 0, r.label = some w := by
  rw [← t.nodeRecs_labels 0 0 0, Multiset.mem_coe, List.mem_filterMap]

theorem Rooted.edgeLabels_card (t : Rooted) : t.edgeLabels.card + 1 = t.vertexCount := by
  have hh := (phi t).edgeLabels_card
  rwa [phi_edgeLabels, phi_leafCount] at hh

theorem list_filterMap_inj {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (l.filterMap f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → ∀ {w : β},
      f a = some w → f b = some w → a = b
  | [], _, a, _, ha, _, _, _, _ => by simp at ha
  | x :: rest, h, a, b, ha, hb, w, hfa, hfb => by
    have hmem : ∀ (c : α), c ∈ rest → ∀ (w' : β), f c = some w' → w' ∈ rest.filterMap f :=
      fun c hc w' hf => List.mem_filterMap.mpr ⟨c, hc, hf⟩
    rcases hx : f x with _ | y
    · rw [List.filterMap_cons, hx] at h
      rcases List.mem_cons.mp ha with rfl | ha'
      · rw [hx] at hfa; cases hfa
      · rcases List.mem_cons.mp hb with rfl | hb'
        · rw [hx] at hfb; cases hfb
        · exact list_filterMap_inj f rest h ha' hb' hfa hfb
    · rw [List.filterMap_cons, hx] at h
      have h' := List.nodup_cons.mp h
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · rfl
        · have : y = w := by rw [hx] at hfa; exact Option.some.inj hfa
          exact absurd (this ▸ hmem _ hb' _ hfb) h'.1
      · rcases List.mem_cons.mp hb with rfl | hb'
        · have : y = w := by rw [hx] at hfb; exact Option.some.inj hfb
          exact absurd (this ▸ hmem _ ha' _ hfa) h'.1
        · exact list_filterMap_inj f rest h'.2 ha' hb' hfa hfb

/-- Heap-increasing trees with labels exactly `1, ..., N` encode to schedule-free increasing
labelled forward states. -/
theorem Rooted.IsEncoding.increasingLabelled {t : Rooted} {s : Forward.State} {N : ℕ}
    (he : t.IsEncoding s) (hi : t.HeapIncreasing) (hA : t.labels = (Finset.Icc 1 N).val) :
    Forward.IncreasingLabelled N s := by
  have hlab : ∀ a ∈ t.labels, 1 ≤ a ∧ a ≤ N := fun a ha => by
    rw [hA] at ha
    simpa using ha
  have hnd : t.labels.Nodup := by rw [hA]; exact Finset.nodup _
  have hparts : (t.edgeLabels + t.vertexLabels).Nodup := t.labels_eq_parts ▸ hnd
  rw [Multiset.nodup_add] at hparts
  obtain ⟨hnde, hndv, hdisj⟩ := hparts
  have hroot : t.rootAbove 0 := t.rootAbove_of_above 0 (fun a ha => (hlab a ha).1)
  have hspec := t.nodeRecs_spec 0 0 0 hi hroot
  have hholds := he.holds
  have hmemV := he.mem_vertices_iff
  have hnodupR : ((t.nodeRecs 0 0 0).filterMap NodeRec.label).Nodup := by
    rw [← Multiset.coe_nodup, t.nodeRecs_labels]
    exact hndv
  have hvle : ∀ v ∈ s.vertices, v ≠ 0 → v ∈ t.edgeLabels := by
    intro v hv hv0
    rw [he.vertices_eq, Finset.mem_insert, Multiset.mem_toFinset] at hv
    exact hv.resolve_left hv0
  have key : ∀ v ∈ s.vertices, v ≠ 0 → ∃ r ∈ t.nodeRecs 0 0 0, r.vertex = v ∧
      r.parent < r.vertex ∧ ∃ r' ∈ t.nodeRecs 0 0 0, r'.vertex = r.parent ∧
        r.depth = r'.depth + 1 ∧ labelAbove r.vertex r'.label := by
    intro v hv hv0
    obtain ⟨r, hr, hrv⟩ := (hmemV v).mp hv
    refine ⟨r, hr, hrv, ?_⟩
    rcases (hspec r hr).2 with h | h
    · subst h
      exact absurd hrv.symm hv0
    · exact h
  have hparent_lt : ∀ v ∈ s.vertices, v ≠ 0 → s.parent v < v := by
    intro v hv hv0
    obtain ⟨r, hr, rfl, hlt, -⟩ := key v hv hv0
    rw [(hholds r hr).1]
    exact hlt
  refine
    { root_mem := ?_
      defaults := he.defaults
      parent_mem := ?_
      parent_lt := hparent_lt
      height_root := he.height_zero
      height_parent := ?_
      active_iff := ?_
      graph_iff := ?_
      frozen_injective := ?_
      frozen_after_birth := ?_
      parent_frozen_after_child := ?_
      vertex_le := ?_
      frozen_le := ?_
      label_disjoint := ?_
      label_cover := ?_ }
  · rw [he.vertices_eq]
    exact Finset.mem_insert_self _ _
  · intro v hv
    by_cases hv0 : v = 0
    · rw [hv0, he.defaults.parent_zero, ← hv0]
      exact hv
    · obtain ⟨r, hr, rfl, hlt, r', hr', hr'v, -⟩ := key v hv hv0
      rw [(hholds r hr).1, ← hr'v]
      exact (hmemV _).mpr ⟨r', hr', rfl⟩
  · intro v hv hv0
    obtain ⟨r, hr, rfl, hlt, r', hr', hr'v, hd, -⟩ := key v hv hv0
    rw [(hholds r hr).2.1, (hholds r hr).1, ← hr'v, (hholds r' hr').2.1]
    exact hd
  · intro v
    rw [he.active_eq, Finset.mem_filter]
  · intro u v
    rw [he.graph_eq, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, ⟨hu, hv, hu0, hpu⟩ | ⟨hv, hu, hv0, hpv⟩⟩
      · exact ⟨hu, hv, Or.inl ⟨hu0, hpu⟩⟩
      · exact ⟨hu, hv, Or.inr ⟨hv0, hpv⟩⟩
    · rintro ⟨hu, hv, ⟨hu0, hpu⟩ | ⟨hv0, hpv⟩⟩
      · refine ⟨?_, Or.inl ⟨hu, hv, hu0, hpu⟩⟩
        intro huv
        have := hparent_lt u hu hu0
        rw [hpu, huv] at this
        exact lt_irrefl _ this
      · refine ⟨?_, Or.inr ⟨hv, hu, hv0, hpv⟩⟩
        intro huv
        have := hparent_lt v hv hv0
        rw [hpv, huv] at this
        exact lt_irrefl _ this
  · intro u hu v hv w hfu hfv
    obtain ⟨ru, hru, rfl⟩ := (hmemV u).mp hu
    obtain ⟨rv, hrv, rfl⟩ := (hmemV v).mp hv
    have h1 : ru.label = some w := by rw [← (hholds ru hru).2.2]; exact hfu
    have h2 : rv.label = some w := by rw [← (hholds rv hrv).2.2]; exact hfv
    rw [list_filterMap_inj NodeRec.label _ hnodupR hru hrv h1 h2]
  · intro v hv w hfv
    obtain ⟨r, hr, rfl⟩ := (hmemV v).mp hv
    have h1 : r.label = some w := by rw [← (hholds r hr).2.2]; exact hfv
    have := (hspec r hr).1
    rw [h1] at this
    exact this
  · intro v hv hv0 w hfw
    obtain ⟨r, hr, rfl, hlt, r', hr', hr'v, hd, hla⟩ := key v hv hv0
    have h1 : r'.label = some w := by
      rw [← (hholds r' hr').2.2, hr'v, ← (hholds r hr).1]; exact hfw
    rw [h1] at hla
    exact hla
  · intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]; exact Nat.zero_le _
    · have : v ∈ t.labels := by
        rw [t.labels_eq_parts]
        exact Multiset.mem_add.mpr (Or.inl (hvle v hv hv0))
      exact (hlab v this).2
  · intro v hv w hfv
    obtain ⟨r, hr, rfl⟩ := (hmemV v).mp hv
    have h1 : r.label = some w := by rw [← (hholds r hr).2.2]; exact hfv
    have : w ∈ t.labels := by
      rw [t.labels_eq_parts]
      exact Multiset.mem_add.mpr (Or.inr ((t.mem_vertexLabels_iff w).mpr ⟨r, hr, h1⟩))
    exact (hlab w this).2
  · intro v hv hv0 w hw hfw
    obtain ⟨r, hr, rfl⟩ := (hmemV w).mp hw
    have h1 : r.label = some v := by rw [← (hholds r hr).2.2]; exact hfw
    exact Multiset.disjoint_left.mp hdisj (hvle v hv hv0)
      ((t.mem_vertexLabels_iff v).mpr ⟨r, hr, h1⟩)
  · intro u hu1 huN
    have : u ∈ t.labels := by rw [hA]; simpa using ⟨hu1, huN⟩
    rw [t.labels_eq_parts, Multiset.mem_add] at this
    rcases this with h | h
    · left
      rw [he.vertices_eq]
      exact Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr h)
    · right
      obtain ⟨r, hr, h1⟩ := (t.mem_vertexLabels_iff u).mp h
      refine ⟨r.vertex, (hmemV _).mpr ⟨r, hr, rfl⟩, ?_⟩
      rw [(hholds r hr).2.2]
      exact h1

theorem Rooted.activeCount_eq_countP (t : Rooted) (i p d : ℕ) :
    t.activeCount = (t.nodeRecs i p d).countP (fun r => decide (r.label = none)) := by
  fun_induction Rooted.nodeRecs t i p d with
  | case1 label i p d => simp [Rooted.activeCount, List.countP_cons]
  | case2 label e c rest i p d ihc ihr =>
    rw [Rooted.activeCount, List.countP_append, ← ihc, ← ihr]

/-- The encoding state has exactly the tree's vertex count. -/
theorem Rooted.IsEncoding.vertices_card {t : Rooted} {s : Forward.State} (he : t.IsEncoding s)
    (hid : (0 ::ₘ t.edgeLabels).Nodup) : s.vertices.card = t.vertexCount := by
  have h0 : (0 : ℕ) ∉ t.edgeLabels := (Multiset.nodup_cons.mp hid).1
  have hnd : t.edgeLabels.Nodup := (Multiset.nodup_cons.mp hid).2
  rw [he.vertices_eq, Finset.card_insert_of_notMem (by simpa using h0),
    Multiset.toFinset_card_of_nodup hnd, ← t.edgeLabels_card]

/-- The encoding state has exactly the tree's active vertex count. -/
theorem Rooted.IsEncoding.active_card {t : Rooted} {s : Forward.State} (he : t.IsEncoding s)
    (hid : (0 ::ₘ t.edgeLabels).Nodup) : s.active.card = t.activeCount := by
  have hnd : ((t.nodeRecs 0 0 0).map NodeRec.vertex).Nodup := by
    rw [← Multiset.coe_nodup, t.nodeRecs_vertices]
    exact hid
  have hset : s.active =
      (((t.nodeRecs 0 0 0).filter (fun r => decide (r.label = none))).map NodeRec.vertex).toFinset := by
    ext v
    rw [he.active_eq, Finset.mem_filter, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨hv, hf⟩
      obtain ⟨r, hr, rfl⟩ := (he.mem_vertices_iff v).mp hv
      refine ⟨r, List.mem_filter.mpr ⟨hr, ?_⟩, rfl⟩
      rw [← (he.holds r hr).2.2]
      simpa using hf
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
      refine ⟨(he.mem_vertices_iff _).mpr ⟨r, hr1, rfl⟩, ?_⟩
      rw [(he.holds r hr1).2.2]
      simpa using hr2
  rw [hset, List.toFinset_card_of_nodup, List.length_map, ← List.countP_eq_length_filter,
    ← t.activeCount_eq_countP 0 0 0]
  exact hnd.sublist ((List.filter_sublist).map _)


/-- The induced schedule has `n - 1` positive steps (attachments) among `1, ..., N`. -/
theorem Rooted.IsEncoding.positive_steps {t : Rooted} {s : Forward.State} {N : ℕ}
    (he : t.IsEncoding s) (hi : t.HeapIncreasing) (hA : t.labels = (Finset.Icc 1 N).val)
    (hid : (0 ::ₘ t.edgeLabels).Nodup) :
    ((Finset.Icc 1 N).filter (fun u => Forward.scheduleOf s u = true)).card =
      t.vertexCount - 1 := by
  have hil := he.increasingLabelled hi hA
  have hset : (Finset.Icc 1 N).filter (fun u => Forward.scheduleOf s u = true) =
      s.vertices.erase 0 := by
    ext u
    rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc, Forward.scheduleOf_eq_true_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, hu⟩
      exact ⟨by omega, hu⟩
    · rintro ⟨hu0, hu⟩
      exact ⟨⟨by omega, hil.vertex_le u hu⟩, hu⟩
  rw [hset, Finset.card_erase_of_mem hil.root_mem, he.vertices_card hid]

/-- The induced schedule has `n - k` negative steps (freezings) among `1, ..., N`. -/
theorem Rooted.IsEncoding.negative_steps {t : Rooted} {s : Forward.State} {N : ℕ}
    (he : t.IsEncoding s) (hi : t.HeapIncreasing) (hA : t.labels = (Finset.Icc 1 N).val)
    (hid : (0 ::ₘ t.edgeLabels).Nodup) :
    ((Finset.Icc 1 N).filter (fun u => Forward.scheduleOf s u = false)).card =
      t.vertexCount - t.activeCount := by
  have hpos := he.positive_steps hi hA hid
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 N)
    (fun u => Forward.scheduleOf s u = true)
  have hneg : (Finset.Icc 1 N).filter (fun u => ¬Forward.scheduleOf s u = true) =
      (Finset.Icc 1 N).filter (fun u => Forward.scheduleOf s u = false) := by
    apply Finset.filter_congr
    intro u _
    simp
  rw [hneg, hpos, Nat.card_Icc] at hsum
  have hlc := t.labels_card
  have hcard : t.labels.card = N := by
    rw [hA]
    simp
  have hvp := t.vertexCount_pos
  omega

end Freezing1.BinaryBijection
