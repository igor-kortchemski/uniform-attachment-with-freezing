module

public import Freezing1.ForwardForestChainVertexEvents
public import Freezing1.ForwardTerminalGoodPredicate

/-! Source A52: the old good mark is shared by an entire cut component. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

theorem treeLaw_inheritsBlocks_from_prefix (x : SignSequence) {C k₀ k b : ℕ}
    (hC : 1 ≤ C) (hab : C ^ k ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ q ∂treeLaw x b, InheritsBlocks (truncateAt q (C ^ k)) q C k₀ k := by
  let a := C ^ k
  have he : a + (b - a) = b := Nat.add_sub_of_le hab
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab : (a : ℕ∞) ≤ b).trans hb
  have hn : ((a + (b - a) : ℕ) : ℕ∞) ≤ extinctionTime x := by rw [he]; exact hb
  have hμ : treeLaw x b = (treeLaw x a).bind (continuationLaw x a (b - a)) := by
    rw [← treeLaw_add_eq_bind_continuation, he]
  rw [hμ]
  apply ae_bind_of_ae measurable_from_top.aemeasurable (by trivial)
  filter_upwards [treeLaw_hasHistory x a haτ] with past hpast
  filter_upwards [continuationLaw_inheritsBlocks (k₀ := k₀) x hpast.current.valid hC,
    continuationLaw_truncate_self hpast hn] with q hblocks hprefix
  rw [hprefix]
  exact hblocks

/-- Every true active vertex in a component carries its root's old mark.
There is no new-block tallness requirement in this statement. -/
theorem treeLaw_goodVertex_oldMark (x : SignSequence) {C k₀ k b : ℕ}
    (hC : 1 ≤ C) (hab : C ^ k ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) (t : ℝ) :
    ∀ᵐ q ∂treeLaw x b, ∀ v ∈ q.active,
      v ∈ goodSet q C k₀ k t ↔
        cutAncestor q (C ^ k) v ∈ goodSet (truncateAt q (C ^ k)) C k₀ k t := by
  filter_upwards [treeLaw_inheritsBlocks_from_prefix (k₀ := k₀) x hC hab hb] with q hq v hv
  simp only [goodSet, Finset.mem_filter]
  constructor
  · rintro ⟨_, htests⟩
    refine ⟨(hq v hv).1, ?_⟩
    intro ell hell
    rw [← (hq v hv).2 ell hell]
    exact htests ell hell
  · rintro ⟨_, htests⟩
    refine ⟨hv, ?_⟩
    intro ell hell
    rw [(hq v hv).2 ell hell]
    exact htests ell hell

/-- The source's componentwise all-good/all-bad assertion for the inherited
mark, before imposing the next block's height test. -/
theorem goodVertices_oldMark_same_component (x : SignSequence) {C k₀ k b : ℕ}
    (hC : 1 ≤ C) (hab : C ^ k ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) (t : ℝ) :
    ∀ᵐ q ∂treeLaw x b, ∀ v ∈ q.active, ∀ w ∈ q.active,
      cutAncestor q (C ^ k) v = cutAncestor q (C ^ k) w →
        (v ∈ goodSet q C k₀ k t ↔ w ∈ goodSet q C k₀ k t) := by
  filter_upwards [treeLaw_goodVertex_oldMark (k₀ := k₀) x hC hab hb t] with q hq v hv w hw hanc
  rw [hq v hv, hq w hw, hanc]

/-- The literal inherited height-test event is also constant on the marked
roots that the source declares active after they freeze. Membership in the
upper tree's genuine active set is not silently imposed on those roots. -/
theorem treeLaw_oldBlockTests_star_mark (x : SignSequence) {C k₀ k b : ℕ}
    (hC : 1 ≤ C) (hab : C ^ k ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) (t : ℝ) :
    ∀ᵐ q ∂treeLaw x b, ∀ v ∈ (starForest q (C ^ k)).active,
      (∀ ell ∈ Finset.Ico k₀ k, t < (blockHeight q (C ^ ell) (C ^ (ell + 1)) v : ℝ)) ↔
        cutAncestor q (C ^ k) v ∈ goodSet (truncateAt q (C ^ k)) C k₀ k t := by
  filter_upwards [treeLaw_goodVertex_oldMark (k₀ := k₀) x hC hab hb t,
    treeLaw_valid x b] with q hq hvalid v hv
  change v ∈ q.active ∪ cutRoots q (C ^ k) at hv
  rcases Finset.mem_union.mp hv with hv | hv
  · simpa only [goodSet, Finset.mem_filter, hv, true_and] using hq v hv
  · have hva : v ≤ C ^ k := ((mem_cutRoots q (C ^ k) v).mp hv).2
    have hvV : v ∈ q.vertices := (Finset.mem_filter.mp hv).1
    rw [cutAncestor_of_le q (C ^ k) v hva]
    change _ ↔ v ∈ (truncateAt q (C ^ k)).active.filter _
    rw [Finset.mem_filter]
    simp only [show v ∈ (truncateAt q (C ^ k)).active from hv, true_and,
      blockHeight_truncateAt hvalid _ _ _ hvV hva]

theorem oldBlockTests_star_same_component (x : SignSequence) {C k₀ k b : ℕ}
    (hC : 1 ≤ C) (hab : C ^ k ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) (t : ℝ) :
    ∀ᵐ q ∂treeLaw x b, ∀ v ∈ (starForest q (C ^ k)).active,
      ∀ w ∈ (starForest q (C ^ k)).active,
      cutAncestor q (C ^ k) v = cutAncestor q (C ^ k) w →
        ((∀ ell ∈ Finset.Ico k₀ k, t < (blockHeight q (C ^ ell) (C ^ (ell + 1)) v : ℝ)) ↔
          ∀ ell ∈ Finset.Ico k₀ k, t < (blockHeight q (C ^ ell) (C ^ (ell + 1)) w : ℝ)) := by
  filter_upwards [treeLaw_oldBlockTests_star_mark (k₀ := k₀) x hC hab hb t]
    with q hq v hv w hw hanc
  rw [hq v hv, hq w hw, hanc]

/-- Once the two new block heights exceed the threshold, both next-good
events are exactly the old good event of their common attachment vertex. -/
theorem goodVertices_next_same_component_iff_oldRoot (x : SignSequence) {C k₀ k : ℕ}
    (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x) (t : ℝ) :
    ∀ᵐ q ∂treeLaw x (C ^ (k + 1)), ∀ v ∈ q.active, ∀ w ∈ q.active,
      t < (cutHeight q (C ^ k) v : ℝ) → t < (cutHeight q (C ^ k) w : ℝ) →
      cutAncestor q (C ^ k) v = cutAncestor q (C ^ k) w →
        (v ∈ goodSet q C k₀ (k + 1) t ∧ w ∈ goodSet q C k₀ (k + 1) t ↔
          cutAncestor q (C ^ k) v ∈ goodSet (truncateAt q (C ^ k)) C k₀ k t) := by
  filter_upwards [treeLaw_goodSet_succ_eq_filter x hC hk hb t] with q hq v hv w hw htv htw hanc
  rw [hq]
  simp only [Finset.mem_filter, hv, hw, htv, htw, true_and, and_true, ← hanc, and_self]

end Freezing1.Forward
