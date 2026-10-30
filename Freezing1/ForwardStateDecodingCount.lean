module

public import Freezing1.ForwardStateDecodingTree

/-!
# The decoded tree encodes its state and uses exactly the labels $1,\dots,N$

For a state `s` with `Forward.IncreasingLabelled N s`, the identifiers (the root `0` and the edge
labels) of the decoded tree `decodeTree s N 0` are exactly the vertices of `s`, each occurring
once. This is shown by a double count along the decoding recursion: for a non-root vertex `u`
of `s` and every `v`, the number of occurrences of `u` among the identifiers of the subtree
decoded at `v` equals the number of occurrences of the parent of `u`, plus one if `u = v`.

Consequently `s` encodes the decoded tree (`Rooted.IsEncoding`), the vertex labels of the tree are
the freezing labels of `s`, and the edge and vertex labels together are exactly $1,\dots,N$, each
once. The vertex and active counts of the tree are those of the state, and $N=2n-k-1$.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

/-- Every edge label of the decoded tree below `v` is a vertex of `s` in `(v, N]`. -/
theorem mem_edgeLabels_decodeTree (s : Forward.State) (N : ℕ) :
    ∀ v x, x ∈ (decodeTree s N v).edgeLabels → v < x ∧ x ≤ N ∧ x ∈ s.vertices := by
  apply decChildren_induction s N (P := fun v => ∀ x, x ∈ (decodeTree s N v).edgeLabels →
    v < x ∧ x ≤ N ∧ x ∈ s.vertices)
  intro v ih x hx
  rw [edgeLabels_decodeTree, Multiset.mem_sum] at hx
  obtain ⟨c, hc, hxc⟩ := hx
  have hc' := mem_decChildSet.mp hc
  rcases Multiset.mem_cons.mp hxc with hxc | hxc
  · subst hxc
    exact ⟨hc'.1, hc'.2.1, hc'.2.2.1⟩
  · have := ih c (List.mem_toFinset.mp hc) x hxc
    exact ⟨by omega, this.2.1, this.2.2⟩

/-- The double count: the multiplicity of a non-root vertex `u` among the identifiers of the
subtree decoded at `v` is the multiplicity of its parent, plus one if `u = v`. -/
theorem decode_count_step {s : Forward.State} {N : ℕ} (h : Forward.IncreasingLabelled N s) :
    ∀ v, ∀ u ∈ s.vertices, u ≠ 0 → u ≤ N →
      Multiset.count u (v ::ₘ (decodeTree s N v).edgeLabels) =
        Multiset.count (s.parent u) (v ::ₘ (decodeTree s N v).edgeLabels) +
          if u = v then 1 else 0 := by
  apply decChildren_induction s N (P := fun v => ∀ u ∈ s.vertices, u ≠ 0 → u ≤ N →
    Multiset.count u (v ::ₘ (decodeTree s N v).edgeLabels) =
      Multiset.count (s.parent u) (v ::ₘ (decodeTree s N v).edgeLabels) +
        if u = v then 1 else 0)
  intro v ih u hu hu0 huN
  rw [Multiset.count_cons, Multiset.count_cons, edgeLabels_decodeTree, Multiset.count_sum',
    Multiset.count_sum']
  have hstep : ∀ c ∈ decChildSet s N v,
      Multiset.count u (c ::ₘ (decodeTree s N c).edgeLabels) =
        Multiset.count (s.parent u) (c ::ₘ (decodeTree s N c).edgeLabels) +
          if u = c then 1 else 0 :=
    fun c hc => ih c (List.mem_toFinset.mp hc) u hu hu0 huN
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_ite_eq]
  have hlt := h.parent_lt u hu hu0
  have hmem : u ∈ decChildSet s N v ↔ s.parent u = v := by
    rw [mem_decChildSet]
    constructor
    · exact fun h' => h'.2.2.2
    · intro hp
      exact ⟨by omega, huN, hu, hp⟩
  simp only [hmem]

/-- Every vertex of `s` occurs exactly once among the identifiers of the tree decoded at `0`,
and nothing else occurs. -/
theorem decode_count_root {s : Forward.State} {N : ℕ} (h : Forward.IncreasingLabelled N s) :
    ∀ u, Multiset.count u (0 ::ₘ (decodeTree s N 0).edgeLabels) =
      if u ∈ s.vertices then 1 else 0 := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hu : u ∈ s.vertices
    · simp only [hu, ↓reduceIte]
      by_cases hu0 : u = 0
      · subst hu0
        have h0 : (0 : ℕ) ∉ (decodeTree s N 0).edgeLabels := fun hm =>
          lt_irrefl _ (mem_edgeLabels_decodeTree s N 0 0 hm).1
        simp [Multiset.count_eq_zero_of_notMem h0]
      · rw [decode_count_step h 0 u hu hu0 (h.vertex_le u hu)]
        simp only [hu0, ↓reduceIte, add_zero]
        rw [ih (s.parent u) (h.parent_lt u hu hu0)]
        simp [h.parent_mem u hu]
    · simp only [hu, ↓reduceIte]
      apply Multiset.count_eq_zero_of_notMem
      intro hmem
      rcases Multiset.mem_cons.mp hmem with rfl | hmem
      · exact hu h.root_mem
      · exact hu (mem_edgeLabels_decodeTree s N 0 u hmem).2.2

/-- The identifiers of the decoded tree are exactly the vertices of `s`, each once. -/
theorem decodeTree_ids {s : Forward.State} {N : ℕ} (h : Forward.IncreasingLabelled N s) :
    0 ::ₘ (decodeTree s N 0).edgeLabels = s.vertices.val := by
  refine Multiset.ext.mpr (fun u => ?_)
  rw [decode_count_root h u, Multiset.count_eq_of_nodup s.vertices.nodup]
  simp

theorem decodeTree_ids_nodup {s : Forward.State} {N : ℕ} (h : Forward.IncreasingLabelled N s) :
    (0 ::ₘ (decodeTree s N 0).edgeLabels).Nodup := by
  rw [decodeTree_ids h]
  exact s.vertices.nodup

/-- Under an encoding, the vertex labels of the tree are the freezing labels of the state read on
the identifiers `0` and the edge labels. -/
theorem Rooted.IsEncoding.vertexLabels_eq {t : Rooted} {s : Forward.State} (he : t.IsEncoding s) :
    t.vertexLabels = Multiset.filterMap s.frozenAt (0 ::ₘ t.edgeLabels) := by
  have h1 := t.nodeRecs_labels 0 0 0
  have h2 := t.nodeRecs_vertices 0 0 0
  rw [← h1, ← h2, Multiset.filterMap_coe]
  congr 1
  rw [List.filterMap_map]
  apply List.filterMap_congr
  intro r hr
  exact ((he.holds r hr).2.2).symm

/-- The decoded tree is encoded by the state. -/
theorem decodeTree_isEncoding {s : Forward.State} {N : ℕ} (h : Forward.IncreasingLabelled N s) :
    (decodeTree s N 0).IsEncoding s where
  vertices_eq := by
    ext v
    have := congrArg (fun m : Multiset ℕ => v ∈ m) (decodeTree_ids h)
    simp only [Multiset.mem_cons, Finset.mem_val, eq_iff_iff] at this
    rw [Finset.mem_insert, Multiset.mem_toFinset]
    exact this.symm
  encodes := decodeTree_encodes h 0
  defaults := h.defaults
  height_zero := h.height_root
  active_eq := by
    ext v
    rw [h.active_iff v, Finset.mem_filter]
  graph_eq := by
    ext u v
    rw [h.graph_iff, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hu, hv, ⟨hu0, hpu⟩ | ⟨hv0, hpv⟩⟩
      · refine ⟨?_, Or.inl ⟨hu, hv, hu0, hpu⟩⟩
        intro huv
        have := h.parent_lt u hu hu0
        rw [hpu, huv] at this
        exact lt_irrefl _ this
      · refine ⟨?_, Or.inr ⟨hv, hu, hv0, hpv⟩⟩
        intro huv
        have := h.parent_lt v hv hv0
        rw [hpv, huv] at this
        exact lt_irrefl _ this
    · rintro ⟨_, ⟨hu, hv, hu0, hpu⟩ | ⟨hv, hu, hv0, hpv⟩⟩
      · exact ⟨hu, hv, Or.inl ⟨hu0, hpu⟩⟩
      · exact ⟨hu, hv, Or.inr ⟨hv0, hpv⟩⟩

theorem frozenAt_inj_of_increasingLabelled {s : Forward.State} {N : ℕ}
    (h : Forward.IncreasingLabelled N s) :
    ∀ a a' b, b ∈ s.frozenAt a → b ∈ s.frozenAt a' → a = a' := by
  intro a a' b ha ha'
  have ha0 : s.frozenAt a = some b := Option.mem_def.mp ha
  have ha0' : s.frozenAt a' = some b := Option.mem_def.mp ha'
  have hav : ∀ x, s.frozenAt x = some b → x ∈ s.vertices := by
    intro x hx
    by_contra hn
    rw [(h.defaults.outside x hn).2.2] at hx
    cases hx
  exact h.frozen_injective a (hav a ha0) a' (hav a' ha0') b ha0 ha0'

/-- The decoded tree uses exactly the labels `1, ..., N`, each once. -/
theorem decodeTree_labels {s : Forward.State} {N : ℕ} (h : Forward.IncreasingLabelled N s) :
    (decodeTree s N 0).labels = (Finset.Icc 1 N).val := by
  have he := decodeTree_isEncoding h
  have hI := decodeTree_ids h
  have hVL : (decodeTree s N 0).vertexLabels = Multiset.filterMap s.frozenAt s.vertices.val := by
    rw [he.vertexLabels_eq, hI]
  have hE : (decodeTree s N 0).edgeLabels.Nodup :=
    (Multiset.nodup_cons.mp (decodeTree_ids_nodup h)).2
  have h0 : (0 : ℕ) ∉ (decodeTree s N 0).edgeLabels :=
    (Multiset.nodup_cons.mp (decodeTree_ids_nodup h)).1
  have hVLnd : (decodeTree s N 0).vertexLabels.Nodup := by
    rw [hVL]
    exact Multiset.Nodup.filterMap _ (frozenAt_inj_of_increasingLabelled h) s.vertices.nodup
  have hEmem : ∀ a ∈ (decodeTree s N 0).edgeLabels, a ∈ s.vertices ∧ a ≠ 0 := by
    intro a ha
    have := (mem_edgeLabels_decodeTree s N 0 a ha)
    exact ⟨this.2.2, by omega⟩
  have hdisj : Disjoint (decodeTree s N 0).edgeLabels (decodeTree s N 0).vertexLabels := by
    rw [Multiset.disjoint_left]
    intro a ha hav
    rw [hVL, Multiset.mem_filterMap] at hav
    obtain ⟨x, hx, hxa⟩ := hav
    exact h.label_disjoint a (hEmem a ha).1 (hEmem a ha).2 x hx hxa
  rw [(decodeTree s N 0).labels_eq_parts]
  refine (Multiset.Nodup.ext (Multiset.nodup_add.mpr ⟨hE, hVLnd, hdisj⟩)
    (Finset.nodup _)).mpr (fun a => ?_)
  rw [Multiset.mem_add, Finset.mem_val, Finset.mem_Icc, hVL, Multiset.mem_filterMap]
  constructor
  · rintro (ha | ⟨x, hx, hxa⟩)
    · have := mem_edgeLabels_decodeTree s N 0 a ha
      exact ⟨by omega, this.2.1⟩
    · have h1 := h.frozen_after_birth x ((Finset.mem_val).mp hx) a hxa
      have h2 := h.frozen_le x ((Finset.mem_val).mp hx) a hxa
      exact ⟨by omega, h2⟩
  · rintro ⟨ha1, haN⟩
    rcases h.label_cover a ha1 haN with hav | ⟨w, hw, hwa⟩
    · left
      have : a ∈ 0 ::ₘ (decodeTree s N 0).edgeLabels := by
        rw [hI]
        exact hav
      rcases Multiset.mem_cons.mp this with h0' | hm
      · omega
      · exact hm
    · right
      exact ⟨w, hw, hwa⟩

theorem decodeTree_vertexCount {s : Forward.State} {N : ℕ} (h : Forward.IncreasingLabelled N s) :
    (decodeTree s N 0).vertexCount = s.vertices.card :=
  ((decodeTree_isEncoding h).vertices_card (decodeTree_ids_nodup h)).symm

theorem decodeTree_activeCount {s : Forward.State} {N : ℕ} (h : Forward.IncreasingLabelled N s) :
    (decodeTree s N 0).activeCount = s.active.card :=
  ((decodeTree_isEncoding h).active_card (decodeTree_ids_nodup h)).symm

/-- The label count: `N = 2n - k - 1` for `n` vertices and `k` active vertices. -/
theorem decodeTree_card_param {s : Forward.State} {N : ℕ}
    (h : Forward.IncreasingLabelled N s) :
    N + s.active.card + 1 = 2 * s.vertices.card := by
  have hl := (decodeTree s N 0).labels_card
  rw [decodeTree_labels h, decodeTree_vertexCount h, decodeTree_activeCount h] at hl
  simpa using hl

end Freezing1.BinaryBijection
