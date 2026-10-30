module

import Freezing1.ForwardStateDecodingUnique

open Freezing1 Freezing1.BinaryBijection MeasureTheory
open scoped Classical

/-! Not a `module` file, so that the worked example at the end can unfold the well-founded
recursive definitions `decodeTree`, `Rooted.nodeRecs`, ... by `simp`.

Authored exact-type reconstruction for the converse of A14/A16 (source lines 638-720): every
forward state with the schedule-free intrinsic increasing conditions is the encoding of a
labelled rooted tree with labels `1,...,N`, so the intrinsic class `T^+_{k,n}` is exactly the set of
trees obtainable by Algorithm 1 over all schedules, and `T_n` is an element of `T^+_{S_n,N_n}`.
The fixed-schedule support claim is false and is not claimed. -/

-- The decoder: children of `v` are the vertices `w` with `v < w ≤ N`, `w ∈ s.vertices`,
-- `parent w = v`, listed in increasing order; node label = freezing label.
example (s : Forward.State) (N v : ℕ) :
    decodeTree s N v = .node (s.frozenAt v)
      ((decChildren s N v).map (fun w => (w, decodeTree s N w))) :=
  decodeTree_eq s N v

example (s : Forward.State) (N v w : ℕ) :
    w ∈ decChildren s N v ↔ v < w ∧ w ≤ N ∧ w ∈ s.vertices ∧ s.parent w = v :=
  mem_decChildren

-- Deliverable 1: the decoder.
example {N : ℕ} {s : Forward.State} (h : Forward.IncreasingLabelled N s) :
    ∃ t : Rooted, t.HeapIncreasing ∧ t.labels = (Finset.Icc 1 N).val ∧ t.IsEncoding s :=
  h.exists_rooted

-- With sorted siblings and the vertex and active counts.
example {N : ℕ} {s : Forward.State} (h : Forward.IncreasingLabelled N s) :
    ∃ t : Rooted, t.Increasing ∧ t.vertexCount = s.vertices.card ∧
      t.activeCount = s.active.card ∧ t.labels = (Finset.Icc 1 N).val ∧ t.IsEncoding s :=
  h.exists_rooted_increasing

example {N : ℕ} {s : Forward.State} (h : Forward.IncreasingLabelled N s) :
    ∃ t : RootedClass s.active.card s.vertices.card (Finset.Icc 1 N), t.val.IsEncoding s :=
  h.exists_rootedClass

-- Numeric facts: `N + k + 1 = 2 n` (n - 1 edge labels, n - k vertex labels).
example {N : ℕ} {s : Forward.State} (h : Forward.IncreasingLabelled N s) :
    N + s.active.card + 1 = 2 * s.vertices.card :=
  h.card_param

example {N : ℕ} {s : Forward.State} (h : Forward.IncreasingLabelled N s) :
    N = 2 * s.vertices.card - s.active.card - 1 :=
  h.eq_two_mul_sub

example {N : ℕ} {s : Forward.State} (h : Forward.IncreasingLabelled N s) :
    (decodeTree s N 0).edgeLabels.card = s.vertices.card - 1 ∧
      (decodeTree s N 0).vertexLabels.card = s.vertices.card - s.active.card ∧
      N = (s.vertices.card - 1) + (s.vertices.card - s.active.card) :=
  h.label_counts

-- Deliverable 2: the unordered class.
example {N : ℕ} {s : Forward.State} (h : Forward.IncreasingLabelled N s) :
    ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
      q.val.IsEncoding s :=
  h.exists_class

example {N k n : ℕ} (q : UnorderedIncreasingClass k n (Finset.Icc 1 N)) {s : Forward.State}
    (hs : q.val.IsEncoding s) : Forward.IncreasingLabelled N s :=
  Forward.IncreasingLabelled.of_class q hs

-- Deliverable 3: the final iff theorem.
example {N : ℕ} {s : Forward.State} :
    Forward.IncreasingLabelled N s ↔
      ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
        q.val.IsEncoding s :=
  Forward.increasingLabelled_iff_exists_class

example {N : ℕ} {s : Forward.State} :
    Forward.IncreasingLabelled N s ↔ N = 2 * s.vertices.card - s.active.card - 1 ∧
      ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card
        (Finset.Icc 1 (2 * s.vertices.card - s.active.card - 1)), q.val.IsEncoding s :=
  Forward.increasingLabelled_iff_exists_paper_class

-- The trees obtainable by Algorithm 1 over all non-extinct schedules are exactly the encoded
-- classes of the intrinsic class.
example {N : ℕ} {s : Forward.State} :
    (∃ x : SignSequence, (N : ℕ∞) ≤ extinctionTime x ∧ (Forward.treeLaw x N) {s} ≠ 0) ↔
      ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
        q.val.IsEncoding s :=
  Forward.exists_support_iff_exists_class

-- Both directions at once, for every class (existing encoder direction + new decoder direction).
example (k n : ℕ) (q : UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1))) :
    ∃ s : Forward.State, q.val.IsEncoding s ∧ s.vertices.card = n ∧ s.active.card = k ∧
      ∃ x : SignSequence, ((2 * n - k - 1 : ℕ) : ℕ∞) ≤ extinctionTime x ∧
        (Forward.treeLaw x (2 * n - k - 1)) {s} ≠ 0 :=
  have h := UnorderedIncreasingClass.exists_forward_support q
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.1,
    h.choose_spec.2.2.2.choose, h.choose_spec.2.2.2.choose_spec.1,
    h.choose_spec.2.2.2.choose_spec.2.2.1⟩

-- The corollary for the actual forward sample: support points of `treeLaw x N`.
example {x : SignSequence} {N : ℕ} (hN : (N : ℕ∞) ≤ extinctionTime x) {s : Forward.State}
    (hs : (Forward.treeLaw x N) {s} ≠ 0) :
    N = 2 * s.vertices.card - s.active.card - 1 ∧
      ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
        q.val.IsEncoding s :=
  Forward.treeLaw_support_exists_class hN hs

-- The almost-sure version.
example (x : SignSequence) (N : ℕ) (hN : (N : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂Forward.treeLaw x N, N = 2 * s.vertices.card - s.active.card - 1 ∧
      ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
        q.val.IsEncoding s :=
  Forward.treeLaw_ae_exists_class x N hN

-- The almost-sure version with the paper's deterministic parameters `S_N` (active count) and
-- `N_N` (vertex count `plusCount + 1`).
example (x : SignSequence) (N : ℕ) (hN : (N : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂Forward.treeLaw x N, (s.active.card : ℤ) = activeCount x N ∧
      s.vertices.card = plusCount x N + 1 ∧
      ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
        q.val.IsEncoding s :=
  Forward.treeLaw_ae_exists_paper_class x N hN

-- Round trip: a heap-increasing tree with labels `1..N` encoded by `s` is sibling-equivalent to
-- the tree decoded from `s`; so a state encodes at most one unordered intrinsic class.
example {t : Rooted} {s : Forward.State} {N : ℕ} (he : t.IsEncoding s) (hi : t.HeapIncreasing)
    (hA : t.labels = (Finset.Icc 1 N).val) : t.UnorderedEq (decodeTree s N 0) :=
  he.unorderedEq_decodeTree hi hA

example {t t' : Rooted} {s : Forward.State} {N : ℕ} (he : t.IsEncoding s)
    (hi : t.HeapIncreasing) (hA : t.labels = (Finset.Icc 1 N).val) (he' : t'.IsEncoding s)
    (hi' : t'.HeapIncreasing) (hA' : t'.labels = (Finset.Icc 1 N).val) : t.UnorderedEq t' :=
  Rooted.IsEncoding.unorderedEq_of_encoding he hi hA he' hi' hA'

example {k n N : ℕ} (q q' : UnorderedIncreasingClass k n (Finset.Icc 1 N)) {s : Forward.State}
    (hq : q.val.IsEncoding s) (hq' : q'.val.IsEncoding s) : q = q' :=
  UnorderedIncreasingClass.eq_of_isEncoding q q' hq hq'

example {k n N : ℕ} (q : UnorderedIncreasingClass k n (Finset.Icc 1 N)) :
    ∃! s : Forward.State, q.val.IsEncoding s :=
  UnorderedIncreasingClass.existsUnique_state q

example {N : ℕ} {s : Forward.State} (h : Forward.IncreasingLabelled N s) :
    ∃! q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
      q.val.IsEncoding s :=
  h.existsUnique_class

-- Bijection between the intrinsic class and the intrinsic increasing forward states with the same
-- parameters, through the encoding relation.
noncomputable example (k n N : ℕ) :
    UnorderedIncreasingClass k n (Finset.Icc 1 N) ≃
      {s : Forward.State // Forward.IncreasingLabelled N s ∧ s.active.card = k ∧
        s.vertices.card = n} :=
  Forward.intrinsicClassEquiv k n N

example (k n N : ℕ) (q : UnorderedIncreasingClass k n (Finset.Icc 1 N)) :
    q.val.IsEncoding (Forward.intrinsicClassEquiv k n N q).val :=
  Forward.classToState_isEncoding q

example {x : SignSequence} {N : ℕ} (hN : (N : ℕ∞) ≤ extinctionTime x) {s : Forward.State}
    (hs : (Forward.treeLaw x N) {s} ≠ 0) :
    ∃! q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
      q.val.IsEncoding s :=
  Forward.treeLaw_support_existsUnique_class hN hs

example (x : SignSequence) (N : ℕ) (hN : (N : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂Forward.treeLaw x N,
      ∃! q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
        q.val.IsEncoding s :=
  Forward.treeLaw_ae_existsUnique_class x N hN

-- The worked example of the original non-module probe (a concrete three-vertex tree) is omitted in
-- this module port: under the module system `simp` cannot unfold the well-founded definitions it uses.
-- The original probe is kept in the development tree.

#print axioms Freezing1.BinaryBijection.decodeTree_eq
#print axioms Freezing1.BinaryBijection.decodeTree_heapIncreasing
#print axioms Freezing1.BinaryBijection.decodeTree_increasing
#print axioms Freezing1.BinaryBijection.decodeTree_encodes
#print axioms Freezing1.BinaryBijection.decode_count_step
#print axioms Freezing1.BinaryBijection.decodeTree_ids
#print axioms Freezing1.BinaryBijection.decodeTree_isEncoding
#print axioms Freezing1.BinaryBijection.decodeTree_labels
#print axioms Freezing1.Forward.IncreasingLabelled.card_param
#print axioms Freezing1.Forward.IncreasingLabelled.label_counts
#print axioms Freezing1.Forward.IncreasingLabelled.exists_rooted
#print axioms Freezing1.Forward.IncreasingLabelled.exists_rooted_increasing
#print axioms Freezing1.Forward.IncreasingLabelled.exists_rootedClass
#print axioms Freezing1.Forward.IncreasingLabelled.exists_class
#print axioms Freezing1.Forward.IncreasingLabelled.of_class
#print axioms Freezing1.Forward.increasingLabelled_iff_exists_class
#print axioms Freezing1.Forward.increasingLabelled_iff_exists_paper_class
#print axioms Freezing1.Forward.exists_support_iff_exists_class
#print axioms Freezing1.Forward.treeLaw_support_exists_class
#print axioms Freezing1.Forward.treeLaw_ae_exists_class
#print axioms Freezing1.Forward.treeLaw_ae_exists_paper_class
#print axioms Freezing1.BinaryBijection.DecHyp.le_decode
#print axioms Freezing1.BinaryBijection.DecHyp.unorderedEq_decode
#print axioms Freezing1.BinaryBijection.Rooted.IsEncoding.unorderedEq_decodeTree
#print axioms Freezing1.BinaryBijection.Rooted.IsEncoding.unorderedEq_of_encoding
#print axioms Freezing1.BinaryBijection.UnorderedIncreasingClass.eq_of_isEncoding
#print axioms Freezing1.BinaryBijection.UnorderedIncreasingClass.existsUnique_state
#print axioms Freezing1.Forward.IncreasingLabelled.existsUnique_class
#print axioms Freezing1.Forward.intrinsicClassEquiv
#print axioms Freezing1.Forward.treeLaw_support_existsUnique_class
#print axioms Freezing1.Forward.treeLaw_ae_existsUnique_class
