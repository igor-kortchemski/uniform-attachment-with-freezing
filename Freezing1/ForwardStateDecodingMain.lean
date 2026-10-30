module

public import Freezing1.ForwardStateDecodingCount

/-!
# Converse direction: every intrinsic increasing forward state is a labelled rooted tree

Together with the encoding of `Freezing1.RootedForwardEncodingMain` this gives the paper's claim
that $\mathfrak T^+_{k,n}$ is exactly the set of trees obtainable by Algorithm 1 over all
schedules, and that $\mathcal T_n$ is an element of $\mathfrak T^+_{S_n,N_n}$.

For a forward state `s` with the schedule-free intrinsic conditions `Forward.IncreasingLabelled N`,
the decoder `decodeTree` builds a heap-increasing (indeed sorted `Increasing`) rooted tree whose
labels are exactly $1,\dots,N$ and which `s` encodes. Hence, for $k$ active vertices and $n$
vertices of `s`, the class of the decoded tree is an element of the unordered intrinsic class
`UnorderedIncreasingClass k n (Finset.Icc 1 N)` encoded by `s`, and $N=2n-k-1$. Conversely every
class encoded by `s` forces `IncreasingLabelled N s`. For a schedule `x` not extinct at `N`, every
point of the support of the forward law `treeLaw x N`, hence almost every sample, encodes an
element of the intrinsic class.
-/

@[expose] public section

namespace Freezing1.Forward

open Freezing1.BinaryBijection MeasureTheory
open scoped Classical

/-- The labels $1,\dots,N$ split as $N=(n-1)+(n-k)$ into the $n-1$ edge labels and the $n-k$
vertex labels: $N+k+1=2n$ for $n$ vertices and $k$ active vertices. -/
theorem IncreasingLabelled.card_param {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    N + s.active.card + 1 = 2 * s.vertices.card :=
  decodeTree_card_param h

theorem IncreasingLabelled.eq_two_mul_sub {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    N = 2 * s.vertices.card - s.active.card - 1 := by
  have := h.card_param
  omega

/-- The decoded tree has $n-1$ edge labels, $n-k$ vertex labels and $N=(n-1)+(n-k)$ labels in
total, for $n$ vertices and $k$ active vertices of `s`. -/
theorem IncreasingLabelled.label_counts {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    (decodeTree s N 0).edgeLabels.card = s.vertices.card - 1 ∧
      (decodeTree s N 0).vertexLabels.card = s.vertices.card - s.active.card ∧
      N = (s.vertices.card - 1) + (s.vertices.card - s.active.card) := by
  have h1 := (decodeTree s N 0).edgeLabels_card
  have h2 := (decodeTree s N 0).labels_card
  have h3 : (decodeTree s N 0).labels.card = N := by
    rw [decodeTree_labels h]
    simp
  rw [(decodeTree s N 0).labels_eq_parts, Multiset.card_add] at h2 h3
  rw [decodeTree_vertexCount h] at h1 h2
  rw [decodeTree_activeCount h] at h2
  refine ⟨by omega, by omega, by omega⟩

/-- The decoder: every schedule-free increasing labelled forward state is encoded by a
heap-increasing rooted tree whose labels are exactly $1,\dots,N$. -/
theorem IncreasingLabelled.exists_rooted {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    ∃ t : Rooted, t.HeapIncreasing ∧ t.labels = (Finset.Icc 1 N).val ∧ t.IsEncoding s :=
  ⟨decodeTree s N 0, decodeTree_heapIncreasing h 0, decodeTree_labels h, decodeTree_isEncoding h⟩

/-- The decoded tree can be taken with sorted siblings (`Rooted.Increasing`), with the vertex and
active counts of the state. -/
theorem IncreasingLabelled.exists_rooted_increasing {N : ℕ} {s : State}
    (h : IncreasingLabelled N s) :
    ∃ t : Rooted, t.Increasing ∧ t.vertexCount = s.vertices.card ∧
      t.activeCount = s.active.card ∧ t.labels = (Finset.Icc 1 N).val ∧ t.IsEncoding s :=
  ⟨decodeTree s N 0, decodeTree_increasing h 0, decodeTree_vertexCount h,
    decodeTree_activeCount h, decodeTree_labels h, decodeTree_isEncoding h⟩

/-- The sorted decoded tree as an element of the canonical class `RootedClass`. -/
theorem IncreasingLabelled.exists_rootedClass {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    ∃ t : RootedClass s.active.card s.vertices.card (Finset.Icc 1 N), t.val.IsEncoding s :=
  ⟨⟨decodeTree s N 0, decodeTree_increasing h 0, decodeTree_vertexCount h,
    decodeTree_activeCount h, decodeTree_labels h⟩, decodeTree_isEncoding h⟩

/-- The unordered intrinsic class of the decoded tree. -/
noncomputable def IncreasingLabelled.toClass {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N) :=
  ⟨Quotient.mk _ (⟨decodeTree s N 0, decodeTree_vertexCount h, decodeTree_activeCount h,
    decodeTree_labels h⟩ : LabelledRepresentative s.active.card s.vertices.card (Finset.Icc 1 N)),
    decodeTree_heapIncreasing h 0⟩

theorem IncreasingLabelled.toClass_isEncoding {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    h.toClass.val.IsEncoding s :=
  decodeTree_isEncoding h

/-- Every state with the intrinsic increasing conditions encodes an element of the unordered
intrinsic class $\mathfrak T^+_{k,n}(\{1,\dots,N\})$, $k$ = active count, $n$ = vertex count. -/
theorem IncreasingLabelled.exists_class {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
      q.val.IsEncoding s :=
  ⟨h.toClass, h.toClass_isEncoding⟩

/-- A state encoding an element of an unordered intrinsic class (with any label set
`{1,...,N}`) satisfies the schedule-free intrinsic conditions. -/
theorem IncreasingLabelled.of_class {N k n : ℕ}
    (q : UnorderedIncreasingClass k n (Finset.Icc 1 N)) {s : State} (hs : q.val.IsEncoding s) :
    IncreasingLabelled N s := by
  obtain ⟨q, hq⟩ := q
  revert hs hq
  refine Quotient.inductionOn q ?_
  intro t hq hs
  exact Rooted.IsEncoding.increasingLabelled hs hq t.property.2.2

/-- The intrinsic conditions on a forward state are equivalent to encoding an element of the
unordered intrinsic class $\mathfrak T^+_{k,n}(\{1,\dots,N\})$, with $k$ the number of active
vertices and $n$ the number of vertices of the state. -/
theorem increasingLabelled_iff_exists_class {N : ℕ} {s : State} :
    IncreasingLabelled N s ↔
      ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
        q.val.IsEncoding s :=
  ⟨IncreasingLabelled.exists_class, fun ⟨q, hs⟩ => IncreasingLabelled.of_class q hs⟩

/-- The same equivalence in the paper's parametrization $N=2n-k-1$ of $\mathfrak T^+_{k,n}$. -/
theorem increasingLabelled_iff_exists_paper_class {N : ℕ} {s : State} :
    IncreasingLabelled N s ↔ N = 2 * s.vertices.card - s.active.card - 1 ∧
      ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card
        (Finset.Icc 1 (2 * s.vertices.card - s.active.card - 1)), q.val.IsEncoding s := by
  constructor
  · intro h
    have hN := h.eq_two_mul_sub
    refine ⟨hN, ?_⟩
    subst hN
    exact h.exists_class
  · rintro ⟨rfl, q, hs⟩
    exact IncreasingLabelled.of_class q hs

/-- The set of states that are encoded by an element of the intrinsic class is exactly the union
over all non-extinct schedules of the forward supports at time `N`: the trees obtainable by
Algorithm 1 are exactly the intrinsic increasing labelled trees. -/
theorem exists_support_iff_exists_class {N : ℕ} {s : State} :
    (∃ x : SignSequence, (N : ℕ∞) ≤ extinctionTime x ∧ (treeLaw x N) {s} ≠ 0) ↔
      ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
        q.val.IsEncoding s :=
  increasingLabelled_iff_exists_support.symm.trans increasingLabelled_iff_exists_class

/-- Every point of the support of the forward law `treeLaw x N` of a non-extinct schedule encodes
an element of the intrinsic class (the paper's "$\mathcal T_n\in\mathfrak T^+_{S_n,N_n}$"). -/
theorem treeLaw_support_exists_class {x : SignSequence} {N : ℕ}
    (hN : (N : ℕ∞) ≤ extinctionTime x) {s : State} (hs : (treeLaw x N) {s} ≠ 0) :
    N = 2 * s.vertices.card - s.active.card - 1 ∧
      ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
        q.val.IsEncoding s :=
  have h := ((treeLaw_singleton_ne_zero_iff_historyShape x N hN s).mp hs).increasingLabelled
  ⟨h.eq_two_mul_sub, h.exists_class⟩

/-- Almost surely, the forward sample at time `N` encodes an element of the unordered intrinsic
class with $k$ = number of active vertices and $n$ = number of vertices of the sample, and
$N=2n-k-1$. -/
theorem treeLaw_ae_exists_class (x : SignSequence) (N : ℕ) (hN : (N : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂treeLaw x N, N = 2 * s.vertices.card - s.active.card - 1 ∧
      ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
        q.val.IsEncoding s := by
  filter_upwards [treeLaw_historyShape x N hN] with s hs
  have h := hs.increasingLabelled
  exact ⟨h.eq_two_mul_sub, h.exists_class⟩

/-- The paper's statement with the deterministic parameters of the schedule: almost surely the
sample has $S_N$ active vertices and $N_N=\mathrm{plusCount}+1$ vertices and encodes an element of
$\mathfrak T^+_{S_N,N_N}$. -/
theorem treeLaw_ae_exists_paper_class (x : SignSequence) (N : ℕ)
    (hN : (N : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂treeLaw x N, (s.active.card : ℤ) = activeCount x N ∧
      s.vertices.card = plusCount x N + 1 ∧
      ∃ q : UnorderedIncreasingClass s.active.card s.vertices.card (Finset.Icc 1 N),
        q.val.IsEncoding s := by
  filter_upwards [treeLaw_counts x N hN, treeLaw_historyShape x N hN] with s hc hs
  exact ⟨hc.1, hc.2, hs.increasingLabelled.exists_class⟩

end Freezing1.Forward
