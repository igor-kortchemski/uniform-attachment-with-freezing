module

public import Freezing1.IncreasingRelabelling

/-! Author statement and trust probes for A28's unique consecutive relabelling. -/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

set_option backward.isDefEq.respectTransparency false

example {k n : ℕ} {A : Finset ℕ} (q : UnorderedIncreasingClass k n A) :
    A.card = 2 * n - k - 1 := unorderedIncreasing_label_card q

example {k n : ℕ} {A : Finset ℕ} (q : UnorderedIncreasingClass k n A)
    (f : Finset.Icc 1 (2 * n - k - 1) ≃o A) : f = paperIncreasingBijection q :=
  paperIncreasingBijection_unique q f

/-- The source's f(i)-label occurs at the corresponding i-label after
relabelling, with both directions and the one-based interval explicit. -/
theorem paper_label_condition {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedIncreasingClass k n A) (a : A) (i : Finset.Icc 1 (2 * n - k - 1)) :
    labelOrderMap (paperLabelIso q) a.val = i.val ↔ a = paperIncreasingBijection q i := by
  rw [labelOrderMap_apply]
  constructor
  · intro h
    have hh : paperLabelIso q a = i := Subtype.ext h
    change a = (paperLabelIso q).symm i
    simpa only [OrderIso.symm_apply_apply] using congrArg (paperLabelIso q).symm hh
  · intro h
    change a = (paperLabelIso q).symm i at h
    rw [h]
    exact congrArg Subtype.val ((paperLabelIso q).apply_symm_apply i)

example {k n : ℕ} {A : Finset ℕ} (q : UnorderedIncreasingClass k n A) :
    ∃! r : UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1)),
      (unorderedIncreasingCanonicalEquiv k n _ r).val =
        (unorderedIncreasingCanonicalEquiv k n A q).val.relabel (labelOrderMap (paperLabelIso q)) :=
  existsUnique_paper_consecutive_relabelling q

example {k n : ℕ} {A : Finset ℕ} (q : UnorderedIncreasingClass k n A) :
    let r := unorderedRelabelEquiv (paperLabelIso q) q
    r.val.edgeLabels = q.val.edgeLabels.map (labelOrderMap (paperLabelIso q)) ∧
      r.val.vertexLabels = q.val.vertexLabels.map (labelOrderMap (paperLabelIso q)) ∧
      r.numericSkeleton = q.numericSkeleton :=
  ⟨unorderedRelabelEquiv_edgeLabels _ q, unorderedRelabelEquiv_vertexLabels _ q,
    unorderedRelabelEquiv_numericSkeleton _ q⟩

#print axioms Rooted.relabel_node
#print axioms finset_orderIso_unique
#print axioms unorderedRelabelEquiv
#print axioms unorderedRelabelEquiv_edgeLabels
#print axioms unorderedRelabelEquiv_vertexLabels
#print axioms unorderedRelabelEquiv_numericSkeleton
#print axioms existsUnique_paper_consecutive_relabelling
#print axioms paper_label_condition

end Freezing1.BinaryBijection
