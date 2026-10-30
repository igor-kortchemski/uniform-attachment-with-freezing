module

public import Freezing1.RootedLabelMap

/-!
# The unique increasing consecutive relabelling on actual unordered trees

Finite label sets are related by their actual order isomorphism. The induced
class equivalence changes only numeric labels, preserves rooted incidences
and active marks, and maps edge and frozen-vertex labels by that same map.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

noncomputable def labelOrderMap {A B : Finset ℕ} (e : A ≃o B) (a : ℕ) : ℕ :=
  if ha : a ∈ A then (e ⟨a, ha⟩).val else 0

@[simp] theorem labelOrderMap_apply {A B : Finset ℕ} (e : A ≃o B) (a : A) :
    labelOrderMap e a.val = (e a).val := by simp [labelOrderMap, a.property]

theorem labelOrderMap_strictMonoOn {A B : Finset ℕ} (e : A ≃o B) :
    StrictMonoOn (labelOrderMap e) (A : Set ℕ) := by
  intro a ha b hb hab
  rw [show labelOrderMap e a = (e ⟨a, ha⟩).val from labelOrderMap_apply e ⟨a, ha⟩,
    show labelOrderMap e b = (e ⟨b, hb⟩).val from labelOrderMap_apply e ⟨b, hb⟩]
  exact e.strictMono hab

theorem labelOrderMap_injOn {A B : Finset ℕ} (e : A ≃o B) :
    Set.InjOn (labelOrderMap e) (A : Set ℕ) := (labelOrderMap_strictMonoOn e).injOn

theorem labelOrderMap_symm_apply {A B : Finset ℕ} (e : A ≃o B) {a : ℕ} (ha : a ∈ A) :
    labelOrderMap e.symm (labelOrderMap e a) = a := by
  change labelOrderMap e.symm (labelOrderMap e (⟨a, ha⟩ : A).val) = a
  rw [labelOrderMap_apply, labelOrderMap_apply]
  exact congrArg Subtype.val (e.symm_apply_apply ⟨a, ha⟩)

@[simp] theorem labelOrderMap_symm_target {A B : Finset ℕ} (e : A ≃o B) (b : B) :
    labelOrderMap e (e.symm b).val = b.val := by
  rw [labelOrderMap_apply]
  exact congrArg Subtype.val (e.apply_symm_apply b)

theorem labelOrderMap_image {A B : Finset ℕ} (e : A ≃o B) :
    A.image (labelOrderMap e) = B := by
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    rw [show labelOrderMap e a = (e ⟨a, ha⟩).val from labelOrderMap_apply e ⟨a, ha⟩]
    exact (e ⟨a, ha⟩).property
  · intro hb
    exact Finset.mem_image.mpr ⟨(e.symm ⟨b, hb⟩).val, (e.symm ⟨b, hb⟩).property,
      labelOrderMap_symm_target e ⟨b, hb⟩⟩

theorem labelOrderMap_multiset {A B : Finset ℕ} (e : A ≃o B) :
    A.val.map (labelOrderMap e) = B.val := by
  have hh := Finset.image_val_of_injOn (labelOrderMap_injOn e)
  rw [labelOrderMap_image e] at hh
  exact hh.symm

/-- Increasing bijections of finite linearly ordered label sets are unique. -/
theorem finset_orderIso_unique {A B : Finset ℕ} (e f : A ≃o B) : e = f := by
  ext a
  let u := A.orderIsoOfFin rfl
  let v := B.orderIsoOfFin rfl
  have he : (v.symm (e a)).val = (u.symm a).val := by
    simpa only [OrderIso.trans_apply, OrderIso.apply_symm_apply] using
      Fin.coe_orderIso_apply (u.trans (e.trans v.symm)) (u.symm a)
  have hf : (v.symm (f a)).val = (u.symm a).val := by
    simpa only [OrderIso.trans_apply, OrderIso.apply_symm_apply] using
      Fin.coe_orderIso_apply (u.trans (f.trans v.symm)) (u.symm a)
  exact congrArg Subtype.val (v.symm.injective (Fin.ext (he.trans hf.symm)))

noncomputable def BinaryClass.relabel {k n : ℕ} {A B : Finset ℕ}
    (e : A ≃o B) (t : BinaryClass k n A) : BinaryClass k n B := by
  refine ⟨t.val.relabel (labelOrderMap e), ?_,
    (FullBinary.relabel_leafCount _ _).trans t.property.2.1,
    (FullBinary.relabel_activeCount _ _).trans t.property.2.2.1, ?_⟩
  · apply FullBinary.relabel_increasing _ t.property.1 ?_ (labelOrderMap_strictMonoOn e)
    intro a ha
    rw [t.property.2.2.2] at ha
    exact ha
  · rw [FullBinary.relabel_labels, t.property.2.2.2, labelOrderMap_multiset]

noncomputable def binaryRelabelEquiv {k n : ℕ} {A B : Finset ℕ} (e : A ≃o B) :
    BinaryClass k n A ≃ BinaryClass k n B where
  toFun := BinaryClass.relabel e
  invFun := BinaryClass.relabel e.symm
  left_inv t := by
    apply Subtype.ext
    change (t.val.relabel (labelOrderMap e)).relabel (labelOrderMap e.symm) = t.val
    rw [FullBinary.relabel_comp]
    calc
      _ = t.val.relabel id := FullBinary.relabel_congr_on_labels t.val (by
        intro a ha
        have haA : a ∈ A := by rw [t.property.2.2.2] at ha; exact ha
        exact labelOrderMap_symm_apply e haA)
      _ = _ := FullBinary.relabel_id t.val
  right_inv t := by
    apply Subtype.ext
    change (t.val.relabel (labelOrderMap e.symm)).relabel (labelOrderMap e) = t.val
    rw [FullBinary.relabel_comp]
    calc
      _ = t.val.relabel id := FullBinary.relabel_congr_on_labels t.val (by
        intro a ha
        have haB : a ∈ B := by rw [t.property.2.2.2] at ha; exact ha
        exact labelOrderMap_symm_apply e.symm haB)
      _ = _ := FullBinary.relabel_id t.val

noncomputable def rootedRelabelEquiv {k n : ℕ} {A B : Finset ℕ} (e : A ≃o B) :
    RootedClass k n A ≃ RootedClass k n B :=
  (increasingEquiv k n A).trans ((binaryRelabelEquiv e).trans (increasingEquiv k n B).symm)

theorem rootedRelabelEquiv_val {k n : ℕ} {A B : Finset ℕ} (e : A ≃o B)
    (t : RootedClass k n A) :
    (rootedRelabelEquiv e t).val = t.val.relabel (labelOrderMap e) := rfl

/-- A genuine equivalence of the actual sibling-permutation quotient
classes, obtained using P01's proved canonical representative theorem. -/
noncomputable def unorderedRelabelEquiv {k n : ℕ} {A B : Finset ℕ} (e : A ≃o B) :
    UnorderedIncreasingClass k n A ≃ UnorderedIncreasingClass k n B :=
  (unorderedIncreasingCanonicalEquiv k n A).trans
    ((rootedRelabelEquiv e).trans (unorderedIncreasingCanonicalEquiv k n B).symm)

theorem unorderedRelabelEquiv_canonical_val {k n : ℕ} {A B : Finset ℕ} (e : A ≃o B)
    (q : UnorderedIncreasingClass k n A) :
    (unorderedIncreasingCanonicalEquiv k n B (unorderedRelabelEquiv e q)).val =
      (unorderedIncreasingCanonicalEquiv k n A q).val.relabel (labelOrderMap e) := by
  simp only [unorderedRelabelEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact rootedRelabelEquiv_val e _

theorem unorderedCanonical_edgeLabels {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedIncreasingClass k n A) :
    (unorderedIncreasingCanonicalEquiv k n A q).val.edgeLabels = q.val.edgeLabels := by
  have hh := unorderedIncreasingEquiv_edgeLabels q
  change (phi (unorderedIncreasingCanonicalEquiv k n A q).val).edgeLabels = _ at hh
  rw [phi_edgeLabels] at hh
  exact hh

theorem unorderedCanonical_vertexLabels {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedIncreasingClass k n A) :
    (unorderedIncreasingCanonicalEquiv k n A q).val.vertexLabels = q.val.vertexLabels := by
  have hh := unorderedIncreasingEquiv_vertexLabels q
  change (phi (unorderedIncreasingCanonicalEquiv k n A q).val).vertexLabels = _ at hh
  rw [phi_vertexLabels] at hh
  exact hh

theorem unorderedRelabelEquiv_edgeLabels {k n : ℕ} {A B : Finset ℕ} (e : A ≃o B)
    (q : UnorderedIncreasingClass k n A) :
    (unorderedRelabelEquiv e q).val.edgeLabels = q.val.edgeLabels.map (labelOrderMap e) := by
  rw [← unorderedCanonical_edgeLabels (unorderedRelabelEquiv e q),
    unorderedRelabelEquiv_canonical_val, Rooted.relabel_edgeLabels, unorderedCanonical_edgeLabels]

theorem unorderedRelabelEquiv_vertexLabels {k n : ℕ} {A B : Finset ℕ} (e : A ≃o B)
    (q : UnorderedIncreasingClass k n A) :
    (unorderedRelabelEquiv e q).val.vertexLabels = q.val.vertexLabels.map (labelOrderMap e) := by
  rw [← unorderedCanonical_vertexLabels (unorderedRelabelEquiv e q),
    unorderedRelabelEquiv_canonical_val, Rooted.relabel_vertexLabels, unorderedCanonical_vertexLabels]

noncomputable def UnorderedIncreasingClass.numericSkeleton {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedIncreasingClass k n A) : Rooted :=
  (unorderedIncreasingCanonicalEquiv k n A q).val.numericSkeleton

theorem unorderedRelabelEquiv_numericSkeleton {k n : ℕ} {A B : Finset ℕ} (e : A ≃o B)
    (q : UnorderedIncreasingClass k n A) :
    (unorderedRelabelEquiv e q).numericSkeleton = q.numericSkeleton := by
  unfold UnorderedIncreasingClass.numericSkeleton
  rw [unorderedRelabelEquiv_canonical_val, Rooted.relabel_numericSkeleton]

/-- This predicate states the literal per-incidence relabelling operation,
not merely equal multisets of labels or equal class parameters. -/
noncomputable def OrderedRelabelling {k n : ℕ} {A B : Finset ℕ} (e : A ≃o B)
    (q : UnorderedIncreasingClass k n A) (r : UnorderedIncreasingClass k n B) : Prop :=
  (unorderedIncreasingCanonicalEquiv k n B r).val =
    (unorderedIncreasingCanonicalEquiv k n A q).val.relabel (labelOrderMap e)

theorem existsUnique_orderedRelabelling {k n : ℕ} {A B : Finset ℕ} (e : A ≃o B)
    (q : UnorderedIncreasingClass k n A) :
    ∃! r : UnorderedIncreasingClass k n B, OrderedRelabelling e q r := by
  refine ⟨unorderedRelabelEquiv e q, unorderedRelabelEquiv_canonical_val e q, ?_⟩
  intro r hr
  apply (unorderedIncreasingCanonicalEquiv k n B).injective
  apply Subtype.ext
  exact hr.trans (unorderedRelabelEquiv_canonical_val e q).symm

noncomputable def consecutiveLabelIso (A : Finset ℕ) :
    A ≃o Finset.Icc 1 A.card :=
  (A.orderIsoOfFin rfl).symm.trans ((Finset.Icc 1 A.card).orderIsoOfFin (by simp))

theorem unorderedIncreasing_label_card {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedIncreasingClass k n A) : A.card = 2 * n - k - 1 :=
  RootedClass.label_card (unorderedIncreasingCanonicalEquiv k n A q)

noncomputable def paperLabelIso {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedIncreasingClass k n A) : A ≃o Finset.Icc 1 (2 * n - k - 1) :=
  (A.orderIsoOfFin (unorderedIncreasing_label_card q)).symm.trans
    ((Finset.Icc 1 (2 * n - k - 1)).orderIsoOfFin (by simp))

/-- The source's f from consecutive labels into the original set A is
precisely the inverse of the canonical rank relabelling map. -/
noncomputable def paperIncreasingBijection {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedIncreasingClass k n A) : Finset.Icc 1 (2 * n - k - 1) ≃o A :=
  (paperLabelIso q).symm

theorem paperIncreasingBijection_unique {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedIncreasingClass k n A) (f : Finset.Icc 1 (2 * n - k - 1) ≃o A) :
    f = paperIncreasingBijection q := finset_orderIso_unique _ _

/-- A28: the unique actual unordered increasing tree on consecutive labels,
with every original edge/frozen vertex relabelled by the source's unique f. -/
theorem existsUnique_paper_consecutive_relabelling {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedIncreasingClass k n A) :
    ∃! r : UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1)),
      OrderedRelabelling (paperLabelIso q) q r :=
  existsUnique_orderedRelabelling (paperLabelIso q) q

end Freezing1.BinaryBijection
