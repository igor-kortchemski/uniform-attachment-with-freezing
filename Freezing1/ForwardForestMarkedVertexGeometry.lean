module

public import Freezing1.ForwardForestConditionalVertexMean

/-! The matched vertex indicators are the original vertex good-mark events. -/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

set_option backward.isDefEq.respectTransparency false

theorem slotForest_active_after_iff (q : State) {a v : ℕ} (hv : a < v) :
    v ∈ (slotForest q a).active ↔ v ∈ q.active := by
  let e := rootNormalizer a (cutRoots q a)
  have hev : e v = v := rootNormalizer_future a (cutRoots q a) v hv
  have hh := mem_active_relabel e (forestCut q a) v
  rw [hev] at hh
  exact hh

theorem cutHeight_slotForest_of_active_after {x : SignSequence} {b : ℕ} {q : State}
    (hq : HasHistory x b q) (hb : (b : ℕ∞) ≤ extinctionTime x) {a v : ℕ}
    (hv : a < v) (hvq : v ∈ q.active) : cutHeight (slotForest q a) a v = cutHeight q a v := by
  let e := rootNormalizer a (cutRoots q a)
  have hev : e v = v := rootNormalizer_future a (cutRoots q a) v hv
  have hh := cutHeight_relabel e (forestCut q a) a v (rootNormalizer_future a (cutRoots q a))
  rw [hev] at hh
  exact hh.trans (cutHeight_forestCut hq hb a (active_subset_cutVertices hq.current.valid a hvq))

theorem cutAncestor_slotForest_of_active_after {x : SignSequence} {b : ℕ} {q : State}
    (hq : HasHistory x b q) (hb : (b : ℕ∞) ≤ extinctionTime x) {a v : ℕ}
    (hv : a < v) (hvq : v ∈ q.active) :
    cutAncestor (slotForest q a) a v = rootNormalizer a (cutRoots q a) (cutAncestor q a v) := by
  let e := rootNormalizer a (cutRoots q a)
  have hev : e v = v := rootNormalizer_future a (cutRoots q a) v hv
  have hh := cutAncestor_relabel e (forestCut q a) a v (rootNormalizer_future a (cutRoots q a))
  rw [hev, cutAncestor_forestCut hq hb a (active_subset_cutVertices hq.current.valid a hvq)] at hh
  exact hh

theorem markedVertexIndicator_eq_actual {x : SignSequence} {b : ℕ} {q : State}
    (hq : HasHistory x b q) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (G : State → Finset ℕ) (a : ℕ) (t : ℝ) (v : ℕ) (hv : a < v) :
    markedVertexIndicator G a t v q =
      if v ∈ q.active ∧ cutAncestor q a v ∈ G (truncateAt q a) ∧ t < (cutHeight q a v : ℝ) then 1 else 0 := by
  by_cases hvq : v ∈ q.active
  · have hh := cutHeight_slotForest_of_active_after hq hb hv hvq
    have ha := cutAncestor_slotForest_of_active_after hq hb hv hvq
    have hmarks : rootNormalizer a (cutRoots q a) (cutAncestor q a v) ∈ rootMarks G a q ↔
        cutAncestor q a v ∈ G (truncateAt q a) := by simp [rootMarks]
    unfold markedVertexIndicator forestMarkedVertexIndicator
    simp only [slotForest_active_after_iff q hv, hvq, true_and, hh, ha, hmarks]
    simp only [and_comm]
  · unfold markedVertexIndicator forestMarkedVertexIndicator
    simp only [slotForest_active_after_iff q hv, hvq, false_and, ite_false]

theorem markedVertexIndicator_zero_before_cut (G : State → Finset ℕ) (a : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (v : ℕ) (hv : v ≤ a) (q : State) :
    markedVertexIndicator G a t v q = 0 := by
  have hz : cutHeight (slotForest q a) a v = 0 := cutHeightAux_eq_zero_of_le _ a _ v hv
  unfold markedVertexIndicator forestMarkedVertexIndicator
  simp only [hz, Nat.cast_zero, not_lt_of_ge ht, and_false, false_and, ite_false]

theorem forestVertexSeparated_slotForest_of_actual {x : SignSequence} {b : ℕ} {q : State}
    (hq : HasHistory x b q) (hb : (b : ℕ∞) ≤ extinctionTime x) {a v w : ℕ}
    (hv : a < v) (hw : a < w) (hvq : v ∈ q.active) (hwq : w ∈ q.active)
    (hsep : cutAncestor q a v ≠ cutAncestor q a w) : forestVertexSeparated (slotForest q a) a v w := by
  unfold forestVertexSeparated
  rw [cutAncestor_slotForest_of_active_after hq hb hv hvq,
    cutAncestor_slotForest_of_active_after hq hb hw hwq]
  exact fun hh => hsep ((rootNormalizer a (cutRoots q a)).injective hh)

theorem starForest_active_after_iff (q : State) {a v : ℕ} (hv : a < v) :
    v ∈ (starForest q a).active ↔ v ∈ q.active := by
  change v ∈ q.active ∪ cutRoots q a ↔ v ∈ q.active
  rw [Finset.mem_union]
  constructor
  · rintro (hq | hroot)
    · exact hq
    · have hle := ((mem_cutRoots q a v).mp hroot).2
      omega
  · exact Or.inl

end Freezing1.Forward
