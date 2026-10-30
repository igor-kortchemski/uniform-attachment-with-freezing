module

import Freezing1.UnorderedBinaryBijection

open Freezing1.BinaryBijection

namespace UnorderedBinaryAudit

example (k n : ℕ) :
    UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1)) ≃
      {t : FullBinary // t.Increasing ∧ t.leafCount = n ∧ t.activeCount = k ∧
        t.labels = (Finset.Icc 1 (2 * n - k - 1)).val} := unorderedPaperEquiv k n

example (k n : ℕ) (A : Finset ℕ) :
    Quotient (labelledUnorderedSetoid k n A) ≃
      {t : Rooted // t.Canonical ∧ t.vertexCount = n ∧ t.activeCount = k ∧ t.labels = A.val} :=
  unorderedCanonicalEquiv k n A

example (t : Rooted) (h : t.labels.Nodup) :
    ∃! s : Rooted, s.Canonical ∧ s.UnorderedEq t := t.exists_unique_canonical h

example {k n : ℕ} {A : Finset ℕ} (t : LabelledRepresentative k n A)
    (ht : t.val.HeapIncreasing) :
    (unorderedIncreasingEquiv k n A ⟨Quotient.mk _ t, ht⟩).val = phi t.val.normalize := rfl

example {k n : ℕ} {A : Finset ℕ} (t : BinaryClass k n A) :
    (psiRepresentative t).val = psi t.val := rfl

example {k n : ℕ} {A : Finset ℕ} (q : UnorderedIncreasingClass k n A) :
    (unorderedIncreasingEquiv k n A q).val.edgeLabels = q.val.edgeLabels ∧
    (unorderedIncreasingEquiv k n A q).val.vertexLabels = q.val.vertexLabels ∧
    (unorderedIncreasingEquiv k n A q).val.vertexCount = 2 * n - 1 :=
  ⟨unorderedIncreasingEquiv_edgeLabels q, unorderedIncreasingEquiv_vertexLabels q,
    unorderedIncreasingEquiv_vertexCount q⟩

#print axioms Rooted.normalize_related
#print axioms Rooted.exists_unique_canonical
#print axioms Rooted.UnorderedEq.normalize_eq
#print axioms Rooted.UnorderedEq.heapIncreasing_iff
#print axioms unorderedCanonicalEquiv
#print axioms unorderedIncreasingCanonicalEquiv
#print axioms unorderedPaperEquiv
#print axioms phi_paper_bijective
#print axioms unorderedIncreasingEquiv_edgeLabels
#print axioms unorderedIncreasingEquiv_vertexLabels
#print axioms unordered_figure_parameter_error

end UnorderedBinaryAudit
