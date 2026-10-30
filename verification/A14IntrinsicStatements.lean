module

import Freezing1.RootedForwardEncodingMain

open Freezing1 Freezing1.BinaryBijection
open scoped Classical

/-! Not a `module` file, so that the worked example below can unfold the well-founded
recursive definitions `Rooted.nodeRecs`, `Rooted.vertexCount`, ... by `simp`.

Authored exact-type reconstruction for A14/A16 (source lines 638-720): the intrinsic class
`T^+_{k,n}(A)` (rooted trees with `n` vertices, `n-1` labelled edges and `n-k` labelled vertices,
`k` active vertices, labels `1,...,2n-k-1`, increasing away from the root and every vertex label
above its adjacent edges) is contained in the union over schedules of the forward supports.
The fixed-schedule version is false and is not claimed. -/

-- Encoding of a node with incoming identifier `i`: the freezing label at `i` is the vertex label
-- and every child edge has parent `i` and height one more than `i`, recursively.
example (s : Forward.State) (label : Option ℕ) (children : List (ℕ × Rooted)) (i : ℕ) :
    (Rooted.node label children).Encodes s i ↔
      s.frozenAt i = label ∧ ∀ p ∈ children,
        s.parent p.1 = i ∧ s.height p.1 = s.height i + 1 ∧ p.2.Encodes s p.1 :=
  Rooted.encodes_node_iff s label children i

-- The full encoding relation: vertices `{0} ∪ edge labels`, tree data, canonical defaults,
-- active set, parent graph.
example (t : Rooted) (s : Forward.State) :
    t.IsEncoding s ↔
      (s.vertices = insert 0 t.edgeLabels.toFinset ∧ t.Encodes s 0 ∧
        Forward.CanonicalDefaults s ∧ s.height 0 = 0 ∧
        s.active = s.vertices.filter (fun v => s.frozenAt v = none) ∧
        s.graph = SimpleGraph.fromRel
          (fun u v => u ∈ s.vertices ∧ v ∈ s.vertices ∧ u ≠ 0 ∧ s.parent u = v)) :=
  ⟨fun h => ⟨h.vertices_eq, h.encodes, h.defaults, h.height_zero, h.active_eq, h.graph_eq⟩,
    fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩

-- Existence of an encoding for distinct positive edge labels (explicit state `toState`).
example (t : Rooted) (hid : (0 ::ₘ t.edgeLabels).Nodup) : ∃ s : Forward.State, t.IsEncoding s :=
  Rooted.exists_isEncoding hid

-- Uniqueness: two encodings of a tree are equal (in particular agree on the vertex set).
example {t : Rooted} {s s' : Forward.State} (h : t.IsEncoding s) (h' : t.IsEncoding s') :
    s = s' ∧ s.vertices = s'.vertices :=
  ⟨h.unique h', h.vertices_eq.trans h'.vertices_eq.symm⟩

-- Encodings do not depend on the order of siblings (sibling-permutation quotient).
example {a b : Rooted} (h : a.UnorderedEq b) (s : Forward.State) :
    a.IsEncoding s ↔ b.IsEncoding s :=
  h.isEncoding_iff s

-- Heap-increasing trees with labels exactly `1,...,N` encode to schedule-free increasing states.
example {t : Rooted} {s : Forward.State} {N : ℕ} (he : t.IsEncoding s) (hi : t.HeapIncreasing)
    (hA : t.labels = (Finset.Icc 1 N).val) : Forward.IncreasingLabelled N s :=
  he.increasingLabelled hi hA

-- The union over schedules: some schedule not extinct at `N` makes the encoded state a support point.
example {t : Rooted} {s : Forward.State} {N : ℕ} (he : t.IsEncoding s) (hi : t.HeapIncreasing)
    (hA : t.labels = (Finset.Icc 1 N).val) :
    ∃ x : SignSequence, (N : ℕ∞) ≤ extinctionTime x ∧ Forward.HistoryShape x N s ∧
      (Forward.treeLaw x N) {s} ≠ 0 :=
  he.forward_support hi hA

-- Counts for the sorted canonical class `RootedClass` (increasing implies heap-increasing).
example (k n : ℕ) (t : RootedClass k n (Finset.Icc 1 (2 * n - k - 1))) :
    ∃ s : Forward.State, t.val.IsEncoding s ∧ s.vertices.card = n ∧ s.active.card = k ∧
      ∃ x : SignSequence, ((2 * n - k - 1 : ℕ) : ℕ∞) ≤ extinctionTime x ∧
        Forward.HistoryShape x (2 * n - k - 1) s ∧
        (Forward.treeLaw x (2 * n - k - 1)) {s} ≠ 0 ∧
        plusCount x (2 * n - k - 1) = n - 1 ∧ minusCount x (2 * n - k - 1) = n - k :=
  t.exists_forward_support

-- Main export on the actual unordered class: for every `k n` (with `1 ≤ n`; this is automatic for
-- a nonempty class) and every unordered increasing class `q`, its encoding state `s` has `n`
-- vertices and `k` active vertices, and some schedule `x` has `N = 2n-k-1 ≤ extinctionTime x`,
-- `HistoryShape x N s`, positive forward probability of `{s}`, and exactly `n-1` positive and
-- `n-k` negative steps among `1..N`.
example (k n : ℕ) (hn : 1 ≤ n) (q : UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1))) :
    ∃ s : Forward.State, q.val.IsEncoding s ∧ s.vertices.card = n ∧ s.active.card = k ∧
      ∃ x : SignSequence, ((2 * n - k - 1 : ℕ) : ℕ∞) ≤ extinctionTime x ∧
        Forward.HistoryShape x (2 * n - k - 1) s ∧
        (Forward.treeLaw x (2 * n - k - 1)) {s} ≠ 0 ∧
        plusCount x (2 * n - k - 1) = n - 1 ∧ minusCount x (2 * n - k - 1) = n - k :=
  have _ := hn
  UnorderedIncreasingClass.exists_forward_support q

-- The same for an arbitrary representative `t` of the class `q`.
example (k n : ℕ) (hn : 1 ≤ n) (q : UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1)))
    (t : LabelledRepresentative k n (Finset.Icc 1 (2 * n - k - 1)))
    (ht : (Quotient.mk _ t : UnorderedSourceClass k n (Finset.Icc 1 (2 * n - k - 1))) = q.val) :
    ∃ s : Forward.State, t.val.IsEncoding s ∧ s.vertices.card = n ∧ s.active.card = k ∧
      ∃ x : SignSequence, ((2 * n - k - 1 : ℕ) : ℕ∞) ≤ extinctionTime x ∧
        Forward.HistoryShape x (2 * n - k - 1) s ∧
        (Forward.treeLaw x (2 * n - k - 1)) {s} ≠ 0 ∧
        plusCount x (2 * n - k - 1) = n - 1 ∧ minusCount x (2 * n - k - 1) = n - k :=
  have _ := hn
  UnorderedIncreasingClass.exists_forward_support_of_representative q t ht

-- Every encoding state of a class is intrinsic increasing and has positive probability for
-- some schedule.
example (k n : ℕ) (q : UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1)))
    (s : Forward.State) (hs : q.val.IsEncoding s) :
    Forward.IncreasingLabelled (2 * n - k - 1) s ∧
      ∃ x : SignSequence, ((2 * n - k - 1 : ℕ) : ℕ∞) ≤ extinctionTime x ∧
        (Forward.treeLaw x (2 * n - k - 1)) {s} ≠ 0 :=
  ⟨q.increasingLabelled hs, q.exists_support_of_isEncoding hs⟩

-- The class has a unique encoding state (labels `1..N` are positive).
example (k n : ℕ) (q : UnorderedSourceClass k n (Finset.Icc 1 (2 * n - k - 1))) :
    ∃! s : Forward.State, q.IsEncoding s :=
  UnorderedSourceClass.existsUnique_isEncoding (fun _ ha => (Finset.mem_Icc.mp ha).1) q

-- The schedule counts hold for every legal-history schedule of the encoded state.
example {t : Rooted} {s : Forward.State} {N : ℕ} (he : t.IsEncoding s) (hi : t.HeapIncreasing)
    (hA : t.labels = (Finset.Icc 1 N).val) (hid : (0 ::ₘ t.edgeLabels).Nodup)
    {x : SignSequence} (hx : Forward.HistoryShape x N s) :
    plusCount x N = t.vertexCount - 1 ∧ minusCount x N = t.vertexCount - t.activeCount :=
  he.schedule_counts hi hA hid hx

-- The printed fixed-schedule support claim is false and not claimed; the union over schedules is
-- exactly the intrinsic class.
example {N : ℕ} {s : Forward.State} :
    Forward.IncreasingLabelled N s ↔
      ∃ x : SignSequence, (N : ℕ∞) ≤ extinctionTime x ∧ (Forward.treeLaw x N) {s} ≠ 0 :=
  Forward.increasingLabelled_iff_exists_support

-- The worked example of the original non-module probe (a concrete three-vertex tree) is omitted in
-- this module port: under the module system `simp` cannot unfold the well-founded definitions it uses.
-- The original probe is kept in the development tree.

#print axioms Freezing1.BinaryBijection.Rooted.encodes_node_iff
#print axioms Freezing1.BinaryBijection.Rooted.exists_isEncoding
#print axioms Freezing1.BinaryBijection.Rooted.IsEncoding.unique
#print axioms Freezing1.BinaryBijection.Rooted.UnorderedEq.isEncoding_iff
#print axioms Freezing1.BinaryBijection.Rooted.IsEncoding.increasingLabelled
#print axioms Freezing1.BinaryBijection.Rooted.IsEncoding.forward_support
#print axioms Freezing1.BinaryBijection.Rooted.IsEncoding.schedule_counts
#print axioms Freezing1.BinaryBijection.Rooted.exists_forward_support
#print axioms Freezing1.BinaryBijection.RootedClass.exists_forward_support
#print axioms Freezing1.BinaryBijection.UnorderedIncreasingClass.exists_forward_support
#print axioms Freezing1.BinaryBijection.UnorderedIncreasingClass.exists_forward_support_of_representative
#print axioms Freezing1.BinaryBijection.UnorderedIncreasingClass.increasingLabelled
#print axioms Freezing1.BinaryBijection.UnorderedSourceClass.existsUnique_isEncoding
