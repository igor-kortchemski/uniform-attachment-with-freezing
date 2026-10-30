module

public import Freezing1.RootedForwardEncodingIncreasing

/-!
# Intrinsic increasing labelled trees lie in the union of forward supports

For every heap-increasing rooted tree `t` with `n` vertices, `k` active vertices and labels
exactly `1, ..., 2n-k-1`, the encoding state `s` of `t` has positive forward probability for
some schedule `x` not yet extinct at `N = 2n-k-1`: `HistoryShape x N s` and
`(treeLaw x N) {s} ≠ 0`. The schedule has `n - 1` attachments and `n - k` freezings among
`1, ..., N`. The statement is transported to the sibling-permutation quotient: the encoding
predicate does not depend on the representative, so it is a predicate on the unordered class.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

/-- Any legal-history schedule for `s` agrees on `1, ..., N` with the schedule recording which
labels are vertex identifiers. -/
theorem HistoryShape.eq_scheduleOf {x : SignSequence} {N : ℕ} {s : State}
    (h : HistoryShape x N s) {u : ℕ} (hu1 : 1 ≤ u) (huN : u ≤ N) :
    x u = scheduleOf s u := by
  have hv := h.schedule.vertex_iff u
  by_cases hu : u ∈ s.vertices
  · have h2 := ((hv.mp hu).resolve_left (by omega)).2.2
    simp [scheduleOf, hu, h2]
  · have h2 : x u ≠ true := fun hx => hu (hv.mpr (Or.inr ⟨hu1, huN, hx⟩))
    simpa [scheduleOf, hu] using h2

end Freezing1.Forward

namespace Freezing1.BinaryBijection

open scoped Classical

theorem plusCount_eq_card_filter (x : SignSequence) (N : ℕ) :
    plusCount x N = ((Finset.Icc 1 N).filter (fun u => x u = true)).card := by
  rw [Finset.card_filter]
  induction N with
  | zero => simp [plusCount]
  | succ N ih =>
    have h1 : plusCount x (N + 1) = plusCount x N + if x (N + 1) = true then 1 else 0 := by
      unfold plusCount
      rw [Finset.sum_range_succ]
    rw [h1, ih, Finset.sum_Icc_succ_top (by omega)]

theorem minusCount_eq_card_filter (x : SignSequence) (N : ℕ) :
    minusCount x N = ((Finset.Icc 1 N).filter (fun u => x u = false)).card := by
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 N)
    (fun u => x u = true)
  have hneg : (Finset.Icc 1 N).filter (fun u => ¬x u = true) =
      (Finset.Icc 1 N).filter (fun u => x u = false) := by
    apply Finset.filter_congr
    intro u _
    simp
  rw [hneg, Nat.card_Icc, ← plusCount_eq_card_filter] at hsum
  unfold minusCount
  omega

/-- The counts of a schedule compatible with an encoding state. -/
theorem Rooted.IsEncoding.schedule_counts {t : Rooted} {s : Forward.State} {N : ℕ}
    (he : t.IsEncoding s) (hi : t.HeapIncreasing) (hA : t.labels = (Finset.Icc 1 N).val)
    (hid : (0 ::ₘ t.edgeLabels).Nodup) {x : SignSequence} (hx : Forward.HistoryShape x N s) :
    plusCount x N = t.vertexCount - 1 ∧ minusCount x N = t.vertexCount - t.activeCount := by
  have hx' : ∀ u ∈ Finset.Icc 1 N, x u = Forward.scheduleOf s u := fun u hu =>
    hx.eq_scheduleOf (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hu).2
  constructor
  · rw [plusCount_eq_card_filter, ← he.positive_steps hi hA hid]
    apply congrArg
    apply Finset.filter_congr
    intro u hu
    rw [hx' u hu]
  · rw [minusCount_eq_card_filter, ← he.negative_steps hi hA hid]
    apply congrArg
    apply Finset.filter_congr
    intro u hu
    rw [hx' u hu]

/-- Every encoding state of a heap-increasing tree with labels `1, ..., N` has positive
probability for some schedule that is not extinct at `N`. -/
theorem Rooted.IsEncoding.forward_support {t : Rooted} {s : Forward.State} {N : ℕ}
    (he : t.IsEncoding s) (hi : t.HeapIncreasing) (hA : t.labels = (Finset.Icc 1 N).val) :
    ∃ x : SignSequence, (N : ℕ∞) ≤ extinctionTime x ∧ Forward.HistoryShape x N s ∧
      (Forward.treeLaw x N) {s} ≠ 0 := by
  obtain ⟨x, hn, hs⟩ := (he.increasingLabelled hi hA).exists_schedule
  exact ⟨x, hn, hs, (Forward.treeLaw_singleton_ne_zero_iff_historyShape x N hn s).mpr hs⟩

/-- The rooted-tree form of the union-over-schedules membership with the paper's counts. -/
theorem Rooted.exists_forward_support {k n : ℕ} (t : Rooted) (hi : t.HeapIncreasing)
    (hn : t.vertexCount = n) (hk : t.activeCount = k)
    (hA : t.labels = (Finset.Icc 1 (2 * n - k - 1)).val) :
    ∃ s : Forward.State, t.IsEncoding s ∧ s.vertices.card = n ∧ s.active.card = k ∧
      ∃ x : SignSequence, ((2 * n - k - 1 : ℕ) : ℕ∞) ≤ extinctionTime x ∧
        Forward.HistoryShape x (2 * n - k - 1) s ∧
        (Forward.treeLaw x (2 * n - k - 1)) {s} ≠ 0 ∧
        plusCount x (2 * n - k - 1) = n - 1 ∧ minusCount x (2 * n - k - 1) = n - k := by
  have hid : (0 ::ₘ t.edgeLabels).Nodup :=
    Rooted.nodup_zero_cons_edgeLabels hA (fun a ha => (Finset.mem_Icc.mp ha).1)
  have he := Rooted.toState_isEncoding hid
  obtain ⟨x, hx, hs, hne⟩ := he.forward_support hi hA
  obtain ⟨hp, hm⟩ := he.schedule_counts hi hA hid hs
  refine ⟨t.toState, he, ?_, ?_, x, hx, hs, hne, ?_, ?_⟩
  · rw [he.vertices_card hid, hn]
  · rw [he.active_card hid, hk]
  · rw [hp, hn]
  · rw [hm, hn, hk]

/-- Every encoding state of a heap-increasing tree also exists (and is unique): the explicit
state of `Rooted.toState`. -/
theorem Rooted.existsUnique_isEncoding {t : Rooted} {A : Finset ℕ} (hA : t.labels = A.val)
    (hpos : ∀ a ∈ A, 0 < a) : ∃! s : Forward.State, t.IsEncoding s := by
  have hid := Rooted.nodup_zero_cons_edgeLabels hA hpos
  exact ⟨t.toState, Rooted.toState_isEncoding hid, fun s hs => hs.eq_toState hid⟩

/-- The encoding predicate on the sibling-permutation quotient of labelled representatives:
it does not depend on the chosen representative. -/
def UnorderedSourceClass.IsEncoding {k n : ℕ} {A : Finset ℕ} (q : UnorderedSourceClass k n A)
    (s : Forward.State) : Prop :=
  Quotient.lift (fun t : LabelledRepresentative k n A => t.val.IsEncoding s)
    (fun (a b : LabelledRepresentative k n A) (h : a.val.UnorderedEq b.val) =>
      propext (h.isEncoding_iff s)) q

theorem UnorderedSourceClass.isEncoding_mk {k n : ℕ} {A : Finset ℕ}
    (t : LabelledRepresentative k n A) (s : Forward.State) :
    UnorderedSourceClass.IsEncoding (Quotient.mk _ t) s ↔ t.val.IsEncoding s :=
  Iff.rfl

theorem UnorderedSourceClass.existsUnique_isEncoding {k n : ℕ} {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) (q : UnorderedSourceClass k n A) :
    ∃! s : Forward.State, q.IsEncoding s := by
  refine Quotient.inductionOn q ?_
  intro t
  exact Rooted.existsUnique_isEncoding t.property.2.2 hpos

/-- The union-over-schedules membership of every unordered increasing class, with the counts. -/
theorem UnorderedIncreasingClass.exists_forward_support {k n : ℕ}
    (q : UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1))) :
    ∃ s : Forward.State, q.val.IsEncoding s ∧ s.vertices.card = n ∧ s.active.card = k ∧
      ∃ x : SignSequence, ((2 * n - k - 1 : ℕ) : ℕ∞) ≤ extinctionTime x ∧
        Forward.HistoryShape x (2 * n - k - 1) s ∧
        (Forward.treeLaw x (2 * n - k - 1)) {s} ≠ 0 ∧
        plusCount x (2 * n - k - 1) = n - 1 ∧ minusCount x (2 * n - k - 1) = n - k := by
  obtain ⟨q, hq⟩ := q
  revert hq
  refine Quotient.inductionOn q ?_
  intro t hq
  exact Rooted.exists_forward_support t.val hq t.property.1 t.property.2.1 t.property.2.2

/-- Every encoding state of an unordered increasing class satisfies the schedule-free intrinsic
conditions, hence has positive forward probability for a schedule not extinct at `N`. -/
theorem UnorderedIncreasingClass.increasingLabelled {k n : ℕ}
    (q : UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1))) {s : Forward.State}
    (hs : q.val.IsEncoding s) : Forward.IncreasingLabelled (2 * n - k - 1) s := by
  obtain ⟨q, hq⟩ := q
  revert hs hq
  refine Quotient.inductionOn q ?_
  intro t hq hs
  exact Rooted.IsEncoding.increasingLabelled hs hq t.property.2.2

theorem UnorderedIncreasingClass.exists_support_of_isEncoding {k n : ℕ}
    (q : UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1))) {s : Forward.State}
    (hs : q.val.IsEncoding s) :
    ∃ x : SignSequence, ((2 * n - k - 1 : ℕ) : ℕ∞) ≤ extinctionTime x ∧
      (Forward.treeLaw x (2 * n - k - 1)) {s} ≠ 0 :=
  Forward.increasingLabelled_iff_exists_support.mp (q.increasingLabelled hs)

/-- The same statement for an arbitrary representative `t` of the class. -/
theorem UnorderedIncreasingClass.exists_forward_support_of_representative {k n : ℕ}
    (q : UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1)))
    (t : LabelledRepresentative k n (Finset.Icc 1 (2 * n - k - 1)))
    (ht : (Quotient.mk _ t : UnorderedSourceClass k n (Finset.Icc 1 (2 * n - k - 1))) = q.val) :
    ∃ s : Forward.State, t.val.IsEncoding s ∧ s.vertices.card = n ∧ s.active.card = k ∧
      ∃ x : SignSequence, ((2 * n - k - 1 : ℕ) : ℕ∞) ≤ extinctionTime x ∧
        Forward.HistoryShape x (2 * n - k - 1) s ∧
        (Forward.treeLaw x (2 * n - k - 1)) {s} ≠ 0 ∧
        plusCount x (2 * n - k - 1) = n - 1 ∧ minusCount x (2 * n - k - 1) = n - k := by
  have hq := q.property
  rw [← ht] at hq
  exact Rooted.exists_forward_support t.val hq t.property.1 t.property.2.1 t.property.2.2

/-- The statement for the canonical (sorted) representatives `RootedClass`. -/
theorem RootedClass.exists_forward_support {k n : ℕ}
    (t : RootedClass k n (Finset.Icc 1 (2 * n - k - 1))) :
    ∃ s : Forward.State, t.val.IsEncoding s ∧ s.vertices.card = n ∧ s.active.card = k ∧
      ∃ x : SignSequence, ((2 * n - k - 1 : ℕ) : ℕ∞) ≤ extinctionTime x ∧
        Forward.HistoryShape x (2 * n - k - 1) s ∧
        (Forward.treeLaw x (2 * n - k - 1)) {s} ≠ 0 ∧
        plusCount x (2 * n - k - 1) = n - 1 ∧ minusCount x (2 * n - k - 1) = n - k :=
  Rooted.exists_forward_support t.val
    ((t.val.increasing_iff_heap_canonical.mp t.property.1).1) t.property.2.1 t.property.2.2.1
    t.property.2.2.2

/-- A class is encoded by the same state as its sorted representative. -/
theorem UnorderedSourceClass.isEncoding_canonical_iff {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedSourceClass k n A) (s : Forward.State) :
    q.IsEncoding s ↔ ((unorderedCanonicalEquiv k n A q).val).IsEncoding s := by
  refine Quotient.inductionOn q ?_
  intro t
  exact (t.val.normalize_related.isEncoding_iff s).symm

end Freezing1.BinaryBijection
