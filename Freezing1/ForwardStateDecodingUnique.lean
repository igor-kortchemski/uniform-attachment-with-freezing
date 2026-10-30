module

public import Freezing1.ForwardStateDecodingMain

/-!
# The decoder inverts the encoder up to sibling order

A heap-increasing rooted tree `t` with labels exactly $1,\dots,N$ that is encoded by a forward
state `s` is sibling-permutation equivalent (`Rooted.UnorderedEq`) to the tree decoded from `s`.
Hence two heap-increasing trees with labels $1,\dots,N$ encoded by the same state are equivalent,
and the unordered intrinsic class encoded by a state is unique: the intrinsic class
$\mathfrak T^+_{k,n}$ and the set of intrinsic increasing forward states are in bijection.

The proof compares multisets of edge labels. A tree `t` at identifier `i` satisfying the local
hypotheses `DecHyp` has edge labels bounded above by those of the decoded tree at `i`
(induction along the decoding recursion, children being injected into the decoded children);
at the root the cardinalities agree, so the multisets are equal; then, top-down, equality of the
sums forces the children of `t` to be exactly the decoded children with equal subtree edge
labels, and the induction hypothesis gives the equivalence of the subtrees.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

/-- The identifiers of the block of a child: its edge label and the edge labels below it. -/
def childBlock (p : ℕ × Rooted) : Multiset ℕ := p.1 ::ₘ p.2.edgeLabels

theorem edgeLabels_node_blocks (label : Option ℕ) (chs : List (ℕ × Rooted)) :
    (Rooted.node label chs).edgeLabels = (chs.map childBlock).sum := by
  rw [Rooted.edgeLabels_node]
  congr 1

theorem childBlock_le_sum {chs : List (ℕ × Rooted)} {p : ℕ × Rooted} (hp : p ∈ chs) :
    childBlock p ≤ (chs.map childBlock).sum := by
  induction chs with
  | nil => simp at hp
  | cons q rest ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Multiset.le_add_right _ _
    · exact (ih hp).trans (Multiset.le_add_left _ _)

theorem fst_le_sum (chs : List (ℕ × Rooted)) :
    ((chs.map Prod.fst : List ℕ) : Multiset ℕ) ≤ (chs.map childBlock).sum := by
  induction chs with
  | nil => simp
  | cons q rest ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, ← Multiset.cons_coe, childBlock,
      Multiset.cons_add]
    exact Multiset.cons_le_cons _ (ih.trans (Multiset.le_add_left _ _))

theorem list_sum_eq_forall {α : Type} (l : List α) (f g : α → Multiset ℕ)
    (hle : ∀ a ∈ l, f a ≤ g a) (hsum : (l.map f).sum = (l.map g).sum) :
    ∀ a ∈ l, f a = g a := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons] at hsum
    have hF : (rest.map f).sum ≤ (rest.map g).sum :=
      List.sum_le_sum (fun a ha => hle a (List.mem_cons_of_mem _ ha))
    have hb : f b = g b := by
      refine le_antisymm (hle b List.mem_cons_self) ?_
      have : g b + (rest.map g).sum ≤ f b + (rest.map g).sum := by
        rw [← hsum]
        exact add_le_add le_rfl hF
      exact le_of_add_le_add_right this
    have hrest : (rest.map f).sum = (rest.map g).sum := by
      rw [hb] at hsum
      exact add_left_cancel hsum
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hb
    · exact ih (fun a ha => hle a (List.mem_cons_of_mem _ ha)) hrest a ha

/-- Replacing the children of a node pointwise by equivalent trees (the replacement may depend
on the edge label) preserves sibling-permutation equivalence. -/
theorem Rooted.UnorderedEq.children_congr (label : Option ℕ) (g : ℕ → Rooted)
    (children before : List (ℕ × Rooted))
    (hg : ∀ p ∈ children, (g p.1).UnorderedEq p.2) :
    (Rooted.node label (before ++ children.map (fun p => (p.1, g p.1)))).UnorderedEq
      (Rooted.node label (before ++ children)) := by
  induction children generalizing before with
  | nil => exact .refl _
  | cons p rest ih =>
    rcases p with ⟨edge, child⟩
    apply Rooted.UnorderedEq.trans
      (.child label edge before (rest.map (fun p => (p.1, g p.1))) (hg (edge, child) (by simp)))
    simpa only [List.append_assoc, List.singleton_append] using
      ih (before ++ [(edge, child)]) (fun p hp => hg p (List.mem_cons_of_mem _ hp))

/-- The local hypotheses on a tree `t` hanging at the identifier `i`. -/
structure DecHyp (s : Forward.State) (N : ℕ) (t : Rooted) (i : ℕ) : Prop where
  encodes : t.Encodes s i
  heap : t.HeapIncreasing
  above : t.rootAbove i
  mem : ∀ w ∈ t.edgeLabels, w ∈ s.vertices ∧ w ≤ N
  nodup : t.edgeLabels.Nodup

theorem DecHyp.children {s : Forward.State} {N : ℕ} {label : Option ℕ}
    {chs : List (ℕ × Rooted)} {i : ℕ} (ht : DecHyp s N (.node label chs) i) :
    s.frozenAt i = label ∧ ((chs.map Prod.fst : List ℕ) : Multiset ℕ).Nodup ∧
      ∀ p ∈ chs, p.1 ∈ decChildren s N i ∧ DecHyp s N p.2 p.1 ∧
        p.2.edgeLabels ≤ childBlock p ∧ childBlock p = p.1 ::ₘ p.2.edgeLabels := by
  have hE := edgeLabels_node_blocks label chs
  obtain ⟨hf, hch⟩ := (Rooted.encodes_node_iff s label chs i).mp ht.encodes
  have hheap := (Rooted.heapIncreasing_node_iff label chs).mp ht.heap
  have habove : ∀ p ∈ chs, i < p.1 := ht.above.2
  have hblk : ∀ p ∈ chs, childBlock p ≤ (Rooted.node label chs).edgeLabels := by
    intro p hp
    rw [hE]
    exact childBlock_le_sum hp
  refine ⟨hf, ?_, ?_⟩
  · have hle : ((chs.map Prod.fst : List ℕ) : Multiset ℕ) ≤ (Rooted.node label chs).edgeLabels := by
      rw [hE]
      exact fst_le_sum chs
    exact Multiset.nodup_of_le hle ht.nodup
  · intro p hp
    have h1 : p.1 ∈ (Rooted.node label chs).edgeLabels :=
      Multiset.mem_of_le (hblk p hp) (Multiset.mem_cons_self _ _)
    have hv := ht.mem p.1 h1
    refine ⟨mem_decChildren.mpr ⟨habove p hp, hv.2, hv.1, (hch p hp).1⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
      Multiset.le_cons_self _ _, rfl⟩
    · exact (hch p hp).2.2
    · exact (hheap p hp).1
    · exact (hheap p hp).2.1
    · intro w hw
      exact ht.mem w (Multiset.mem_of_le (hblk p hp) (Multiset.mem_cons_of_mem hw))
    · exact Multiset.nodup_of_le ((Multiset.le_cons_self _ _).trans (hblk p hp)) ht.nodup

/-- The identifiers of the decoded tree at `w`. -/
noncomputable def decBlock (s : Forward.State) (N w : ℕ) : Multiset ℕ := w ::ₘ (decodeTree s N w).edgeLabels

/-- A tree at `i` satisfying the local hypotheses has edge labels below those of the decoded tree
at `i`. -/
theorem DecHyp.le_decode {s : Forward.State} {N : ℕ} :
    ∀ i t, DecHyp s N t i → t.edgeLabels ≤ (decodeTree s N i).edgeLabels := by
  apply decChildren_induction s N (P := fun i => ∀ t, DecHyp s N t i →
    t.edgeLabels ≤ (decodeTree s N i).edgeLabels)
  intro i ih t ht
  cases t with
  | node label chs =>
    obtain ⟨hf, hnd, hc⟩ := ht.children
    rw [edgeLabels_node_blocks, edgeLabels_decodeTree]
    calc (chs.map childBlock).sum
        ≤ (chs.map (fun p => p.1 ::ₘ (decodeTree s N p.1).edgeLabels)).sum := by
          apply List.sum_le_sum
          intro p hp
          obtain ⟨h1, h2, h3, h4⟩ := hc p hp
          exact h4 ▸ Multiset.cons_le_cons _ (ih p.1 h1 p.2 h2)
      _ = ∑ w ∈ (chs.map Prod.fst).toFinset, decBlock s N w := by
          rw [List.sum_toFinset _ (Multiset.coe_nodup.mp hnd), List.map_map]
          rfl
      _ ≤ ∑ w ∈ decChildSet s N i, decBlock s N w := by
          apply Finset.sum_le_sum_of_subset
          intro w hw
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
          exact List.mem_toFinset.mpr (hc p hp).1

/-- If moreover the edge labels agree with those of the decoded tree, the tree is
sibling-permutation equivalent to the decoded tree. -/
theorem DecHyp.unorderedEq_decode {s : Forward.State} {N : ℕ} :
    ∀ i t, DecHyp s N t i → t.edgeLabels = (decodeTree s N i).edgeLabels →
      t.UnorderedEq (decodeTree s N i) := by
  apply decChildren_induction s N (P := fun i => ∀ t, DecHyp s N t i →
    t.edgeLabels = (decodeTree s N i).edgeLabels → t.UnorderedEq (decodeTree s N i))
  intro i ih t ht heq
  cases t with
  | node label chs =>
    obtain ⟨hf, hnd, hc⟩ := ht.children
    have hndl : (chs.map Prod.fst).Nodup := Multiset.coe_nodup.mp hnd
    have hle_term : ∀ p ∈ chs, childBlock p ≤ decBlock s N p.1 := by
      intro p hp
      obtain ⟨h1, h2, h3, h4⟩ := hc p hp
      exact h4 ▸ Multiset.cons_le_cons _ (DecHyp.le_decode p.1 p.2 h2)
    have hS1S2 : (chs.map childBlock).sum ≤ (chs.map (fun p => decBlock s N p.1)).sum :=
      List.sum_le_sum hle_term
    have hS2 : (chs.map (fun p => decBlock s N p.1)).sum =
        ∑ w ∈ (chs.map Prod.fst).toFinset, decBlock s N w := by
      rw [List.sum_toFinset _ hndl, List.map_map]
      rfl
    have hsub : (chs.map Prod.fst).toFinset ⊆ decChildSet s N i := by
      intro w hw
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
      exact List.mem_toFinset.mpr (hc p hp).1
    have hS23 : ∑ w ∈ (chs.map Prod.fst).toFinset, decBlock s N w ≤
        ∑ w ∈ decChildSet s N i, decBlock s N w :=
      Finset.sum_le_sum_of_subset hsub
    have hEd : (decodeTree s N i).edgeLabels = ∑ w ∈ decChildSet s N i, decBlock s N w :=
      edgeLabels_decodeTree s N i
    have hEt : (Rooted.node label chs).edgeLabels = (chs.map childBlock).sum :=
      edgeLabels_node_blocks label chs
    have hchain : ∑ w ∈ decChildSet s N i, decBlock s N w = (chs.map childBlock).sum := by
      rw [← hEd, ← hEt, heq]
    have hS2le : (chs.map (fun p => decBlock s N p.1)).sum ≤ (chs.map childBlock).sum := by
      rw [hS2]
      exact hS23.trans hchain.le
    have h12 : (chs.map childBlock).sum = (chs.map (fun p => decBlock s N p.1)).sum :=
      le_antisymm hS1S2 hS2le
    have h23 : ∑ w ∈ (chs.map Prod.fst).toFinset, decBlock s N w =
        ∑ w ∈ decChildSet s N i, decBlock s N w := by
      rw [← hS2, hchain]
      exact h12.symm
    have hsd : ∑ w ∈ decChildSet s N i \ (chs.map Prod.fst).toFinset, decBlock s N w = 0 := by
      have h := Finset.sum_sdiff hsub (f := decBlock s N)
      rw [← h23] at h
      exact add_eq_right.mp h
    have hD : decChildSet s N i ⊆ (chs.map Prod.fst).toFinset := by
      intro w hw
      by_contra hn
      have := Finset.sum_eq_zero_iff.mp hsd w (Finset.mem_sdiff.mpr ⟨hw, hn⟩)
      exact Multiset.cons_ne_zero this
    have hfin : (chs.map Prod.fst).toFinset = (decChildren s N i).toFinset :=
      Finset.Subset.antisymm hsub hD
    have hperm : (chs.map Prod.fst).Perm (decChildren s N i) :=
      List.perm_of_nodup_nodup_toFinset_eq hndl (decChildren_nodup s N i) hfin
    have hterm := list_sum_eq_forall chs childBlock (fun p => decBlock s N p.1) hle_term h12
    have hsubtree : ∀ p ∈ chs, p.2.UnorderedEq (decodeTree s N p.1) := by
      intro p hp
      obtain ⟨h1, h2, h3, h4⟩ := hc p hp
      have := hterm p hp
      exact ih p.1 h1 p.2 h2 ((Multiset.cons_inj_right _).mp this)
    have step1 : (Rooted.node label chs).UnorderedEq
        (Rooted.node label (chs.map (fun p => (p.1, decodeTree s N p.1)))) := by
      have := Rooted.UnorderedEq.children_congr label (fun w => decodeTree s N w) chs []
        (fun p hp => (hsubtree p hp).symm)
      simpa using this.symm
    have step2 : (Rooted.node label (chs.map (fun p => (p.1, decodeTree s N p.1)))).UnorderedEq
        (Rooted.node label ((decChildren s N i).map (fun w => (w, decodeTree s N w)))) := by
      apply Rooted.UnorderedEq.perm
      have := hperm.map (fun w => (w, decodeTree s N w))
      simpa only [List.map_map, Function.comp_def] using this
    rw [decodeTree_eq s N i, hf]
    exact step1.trans step2

/-- The decoder inverts the encoder up to sibling order: a heap-increasing tree with labels
$1,\dots,N$ that is encoded by `s` is sibling-permutation equivalent to the tree decoded
from `s`. -/
theorem Rooted.IsEncoding.unorderedEq_decodeTree {t : Rooted} {s : Forward.State} {N : ℕ}
    (he : t.IsEncoding s) (hi : t.HeapIncreasing) (hA : t.labels = (Finset.Icc 1 N).val) :
    t.UnorderedEq (decodeTree s N 0) := by
  have h := he.increasingLabelled hi hA
  have hid := Rooted.nodup_zero_cons_edgeLabels hA (fun a ha => (Finset.mem_Icc.mp ha).1)
  have hlab : ∀ a ∈ t.labels, 1 ≤ a ∧ a ≤ N := fun a ha => by
    rw [hA] at ha
    simpa using ha
  have hD : DecHyp s N t 0 :=
    { encodes := he.encodes
      heap := hi
      above := t.rootAbove_of_above 0 (fun a ha => (hlab a ha).1)
      mem := by
        intro w hw
        refine ⟨?_, ?_⟩
        · rw [he.vertices_eq]
          exact Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr hw)
        · have : w ∈ t.labels := by
            rw [t.labels_eq_parts]
            exact Multiset.mem_add.mpr (Or.inl hw)
          exact (hlab w this).2
      nodup := (Multiset.nodup_cons.mp hid).2 }
  have hle := DecHyp.le_decode 0 t hD
  have hc1 := t.edgeLabels_card
  have hc2 := he.vertices_card hid
  have hc3 := congrArg Multiset.card (decodeTree_ids h)
  rw [Multiset.card_cons, Finset.card_val] at hc3
  have heq := Multiset.eq_of_le_of_card_le hle (by omega)
  exact DecHyp.unorderedEq_decode 0 t hD heq

/-- Two heap-increasing trees with labels $1,\dots,N$ encoded by the same state are
sibling-permutation equivalent. -/
theorem Rooted.IsEncoding.unorderedEq_of_encoding {t t' : Rooted} {s : Forward.State} {N : ℕ}
    (he : t.IsEncoding s) (hi : t.HeapIncreasing) (hA : t.labels = (Finset.Icc 1 N).val)
    (he' : t'.IsEncoding s) (hi' : t'.HeapIncreasing)
    (hA' : t'.labels = (Finset.Icc 1 N).val) : t.UnorderedEq t' :=
  (he.unorderedEq_decodeTree hi hA).trans (he'.unorderedEq_decodeTree hi' hA').symm

theorem UnorderedSourceClass.eq_of_isEncoding {k n N : ℕ}
    (q q' : UnorderedSourceClass k n (Finset.Icc 1 N)) {s : Forward.State}
    (hi : q.Increasing) (hi' : q'.Increasing)
    (hq : q.IsEncoding s) (hq' : q'.IsEncoding s) : q = q' := by
  induction q, q' using Quotient.inductionOn₂ with
  | _ a b =>
    exact Quotient.sound
      (Rooted.IsEncoding.unorderedEq_of_encoding hq hi a.property.2.2 hq' hi' b.property.2.2)

/-- A forward state encodes at most one unordered intrinsic class. -/
theorem UnorderedIncreasingClass.eq_of_isEncoding {k n N : ℕ}
    (q q' : UnorderedIncreasingClass k n (Finset.Icc 1 N)) {s : Forward.State}
    (hq : q.val.IsEncoding s) (hq' : q'.val.IsEncoding s) : q = q' :=
  Subtype.ext (UnorderedSourceClass.eq_of_isEncoding q.val q'.val q.property q'.property hq hq')

/-- Every unordered intrinsic class with labels $1,\dots,N$ is encoded by exactly one state. -/
theorem UnorderedIncreasingClass.existsUnique_state {k n N : ℕ}
    (q : UnorderedIncreasingClass k n (Finset.Icc 1 N)) :
    ∃! s : Forward.State, q.val.IsEncoding s :=
  UnorderedSourceClass.existsUnique_isEncoding (fun _ ha => (Finset.mem_Icc.mp ha).1) q.val

/-- A state encoding a class with parameters `(k, n)` has `n` vertices and `k` active vertices. -/
theorem UnorderedIncreasingClass.state_counts {k n N : ℕ}
    (q : UnorderedIncreasingClass k n (Finset.Icc 1 N)) {s : Forward.State}
    (hs : q.val.IsEncoding s) : s.vertices.card = n ∧ s.active.card = k := by
  obtain ⟨q, hqi⟩ := q
  revert hs hqi
  refine Quotient.inductionOn q ?_
  intro a hqi hs
  have hid := Rooted.nodup_zero_cons_edgeLabels a.property.2.2 (fun _ ha => (Finset.mem_Icc.mp ha).1)
  exact ⟨(hs.vertices_card hid).trans a.property.1, (hs.active_card hid).trans a.property.2.1⟩

end Freezing1.BinaryBijection

namespace Freezing1.Forward

open Freezing1.BinaryBijection MeasureTheory
open scoped Classical

/-- The unordered intrinsic class encoded by an intrinsic increasing state is unique. -/
theorem IncreasingLabelled.existsUnique_class {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    ∃! q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
      q.val.IsEncoding s :=
  ⟨h.toClass, h.toClass_isEncoding, fun q hq =>
    UnorderedIncreasingClass.eq_of_isEncoding q h.toClass hq h.toClass_isEncoding⟩

theorem exists_class_of_state {k n N : ℕ} {s : State} (h : IncreasingLabelled N s)
    (hk : s.active.card = k) (hn : s.vertices.card = n) :
    ∃ q : UnorderedIncreasingClass k n (Finset.Icc 1 N), q.val.IsEncoding s := by
  subst hk hn
  exact h.exists_class

/-- The intrinsic increasing forward states with $k$ active vertices and $n$ vertices. -/
def IntrinsicState (k n N : ℕ) : Type :=
  {s : State // IncreasingLabelled N s ∧ s.active.card = k ∧ s.vertices.card = n}

/-- The unique state encoding a class. -/
noncomputable def classToState {k n N : ℕ} (q : UnorderedIncreasingClass k n (Finset.Icc 1 N)) :
    IntrinsicState k n N :=
  ⟨(UnorderedIncreasingClass.existsUnique_state q).choose,
    IncreasingLabelled.of_class q (UnorderedIncreasingClass.existsUnique_state q).choose_spec.1,
    (UnorderedIncreasingClass.state_counts q
      (UnorderedIncreasingClass.existsUnique_state q).choose_spec.1).2,
    (UnorderedIncreasingClass.state_counts q
      (UnorderedIncreasingClass.existsUnique_state q).choose_spec.1).1⟩

theorem classToState_isEncoding {k n N : ℕ} (q : UnorderedIncreasingClass k n (Finset.Icc 1 N)) :
    q.val.IsEncoding (classToState q).val :=
  (UnorderedIncreasingClass.existsUnique_state q).choose_spec.1

/-- The unique class encoded by a state (the decoded class). -/
noncomputable def stateToClass {k n N : ℕ} (s : IntrinsicState k n N) :
    UnorderedIncreasingClass k n (Finset.Icc 1 N) :=
  (exists_class_of_state s.2.1 s.2.2.1 s.2.2.2).choose

theorem stateToClass_isEncoding {k n N : ℕ} (s : IntrinsicState k n N) :
    (stateToClass s).val.IsEncoding s.val :=
  (exists_class_of_state s.2.1 s.2.2.1 s.2.2.2).choose_spec

/-- The intrinsic class $\mathfrak T^+_{k,n}(\{1,\dots,N\})$ is in bijection with the set of
schedule-free increasing labelled forward states with $k$ active vertices and $n$ vertices, via
the encoding relation. -/
noncomputable def intrinsicClassEquiv (k n N : ℕ) :
    UnorderedIncreasingClass k n (Finset.Icc 1 N) ≃ IntrinsicState k n N where
  toFun := classToState
  invFun := stateToClass
  left_inv q :=
    UnorderedIncreasingClass.eq_of_isEncoding _ q (stateToClass_isEncoding _)
      (classToState_isEncoding q)
  right_inv s :=
    Subtype.ext
      ((UnorderedIncreasingClass.existsUnique_state (stateToClass s)).unique
        (classToState_isEncoding _) (stateToClass_isEncoding s))

/-- Every point of the support of `treeLaw x N` (for a schedule not extinct at `N`) encodes
exactly one unordered intrinsic class. -/
theorem treeLaw_support_existsUnique_class {x : SignSequence} {N : ℕ}
    (hN : (N : ℕ∞) ≤ extinctionTime x) {s : State} (hs : (treeLaw x N) {s} ≠ 0) :
    ∃! q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
      q.val.IsEncoding s :=
  ((treeLaw_singleton_ne_zero_iff_historyShape x N hN s).mp hs).increasingLabelled.existsUnique_class

/-- Almost surely the forward sample at time `N` encodes exactly one unordered intrinsic class. -/
theorem treeLaw_ae_existsUnique_class (x : SignSequence) (N : ℕ)
    (hN : (N : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂treeLaw x N,
      ∃! q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
        q.val.IsEncoding s := by
  filter_upwards [treeLaw_historyShape x N hN] with s hs
  exact hs.increasingLabelled.existsUnique_class

end Freezing1.Forward
