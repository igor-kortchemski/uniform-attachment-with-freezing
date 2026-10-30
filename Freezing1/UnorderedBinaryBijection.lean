module

public import Freezing1.RootedNormalization

/-!
# The paper's bijection on actual unordered rooted-tree classes

Source trees are quotients by the sibling-permutation/subtree-isomorphism
relation. The canonical representative is constructed and proved unique;
no equivalence between an unordered source and an ordered coding is assumed.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

def LabelledRepresentative (k n : ℕ) (A : Finset ℕ) :=
  {t : Rooted // t.vertexCount = n ∧ t.activeCount = k ∧ t.labels = A.val}

def labelledUnorderedSetoid (k n : ℕ) (A : Finset ℕ) : Setoid (LabelledRepresentative k n A) where
  r s t := s.val.UnorderedEq t.val
  iseqv := ⟨fun t => .refl t.val, fun h => .symm h, fun h1 h2 => .trans h1 h2⟩

def UnorderedSourceClass (k n : ℕ) (A : Finset ℕ) := Quotient (labelledUnorderedSetoid k n A)

def UnorderedSourceClass.edgeLabels {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedSourceClass k n A) : Multiset ℕ :=
  Quotient.lift (fun t : LabelledRepresentative k n A => t.val.edgeLabels)
    (fun (s t : LabelledRepresentative k n A) (h : s.val.UnorderedEq t.val) =>
      h.edge_vertex_labels_eq.1) q

def UnorderedSourceClass.vertexLabels {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedSourceClass k n A) : Multiset ℕ :=
  Quotient.lift (fun t : LabelledRepresentative k n A => t.val.vertexLabels)
    (fun (s t : LabelledRepresentative k n A) (h : s.val.UnorderedEq t.val) =>
      h.edge_vertex_labels_eq.2) q

def normalizeRepresentative {k n : ℕ} {A : Finset ℕ} (t : LabelledRepresentative k n A) :
    SourceRootedClass k n A := by
  have hnd : t.val.labels.Nodup := by rw [t.property.2.2]; exact A.nodup
  exact ⟨t.val.normalize, t.val.normalize_canonical hnd,
    t.val.normalize_vertexCount.trans t.property.1,
    t.val.normalize_activeCount.trans t.property.2.1,
    t.val.normalize_labels.trans t.property.2.2⟩

theorem normalizeRepresentative_respects {k n : ℕ} {A : Finset ℕ}
    {s t : LabelledRepresentative k n A} (h : s.val.UnorderedEq t.val) :
    normalizeRepresentative s = normalizeRepresentative t := by
  apply Subtype.ext
  exact h.normalize_eq (by rw [s.property.2.2]; exact A.nodup)

/-- Existence and uniqueness of the sorted representative is proved by
normalization, actual unordered equivalence, and normalization invariance. -/
def unorderedCanonicalEquiv (k n : ℕ) (A : Finset ℕ) :
    UnorderedSourceClass k n A ≃ SourceRootedClass k n A where
  toFun := Quotient.lift normalizeRepresentative (fun _ _ h => normalizeRepresentative_respects h)
  invFun t := Quotient.mk _ ⟨t.val, t.property.2⟩
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro t
    exact Quotient.sound t.val.normalize_related
  right_inv t := Subtype.ext (t.val.normalize_eq_self t.property.1)

def UnorderedSourceClass.Increasing {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedSourceClass k n A) : Prop :=
  Quotient.lift (fun t : LabelledRepresentative k n A => t.val.HeapIncreasing)
    (fun (s t : LabelledRepresentative k n A) (h : s.val.UnorderedEq t.val) =>
      propext h.heapIncreasing_iff) q

theorem unorderedCanonical_heap_iff {k n : ℕ} {A : Finset ℕ} (q : UnorderedSourceClass k n A) :
    ((unorderedCanonicalEquiv k n A q).val).HeapIncreasing ↔ q.Increasing := by
  refine Quotient.inductionOn q ?_
  intro t
  exact t.val.normalize_heapIncreasing

/-- The source increasing class retains only intrinsic label conditions;
it imposes no arbitrary order on siblings. -/
def UnorderedIncreasingClass (k n : ℕ) (A : Finset ℕ) :=
  {q : UnorderedSourceClass k n A // q.Increasing}

def increasingCanonicalEquiv (k n : ℕ) (A : Finset ℕ) :
    {t : SourceRootedClass k n A // t.val.HeapIncreasing} ≃ RootedClass k n A where
  toFun t := ⟨t.val.val,
    (t.val.val.increasing_iff_heap_canonical).mpr ⟨t.property, t.val.property.1⟩, t.val.property.2⟩
  invFun t := ⟨t.toSource, (t.val.increasing_iff_heap_canonical).mp t.property.1 |>.1⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

def unorderedIncreasingCanonicalEquiv (k n : ℕ) (A : Finset ℕ) :
    UnorderedIncreasingClass k n A ≃ RootedClass k n A :=
  ((unorderedCanonicalEquiv k n A).subtypeEquiv (fun q => (unorderedCanonical_heap_iff q).symm)).trans
    (increasingCanonicalEquiv k n A)

/-- Proposition P01 with the source interpreted as actual unordered rooted
trees and the target as full plane binary trees. -/
def unorderedIncreasingEquiv (k n : ℕ) (A : Finset ℕ) :
    UnorderedIncreasingClass k n A ≃ BinaryClass k n A :=
  (unorderedIncreasingCanonicalEquiv k n A).trans (increasingEquiv k n A)

def unorderedPaperEquiv (k n : ℕ) :
    UnorderedIncreasingClass k n (Finset.Icc 1 (2 * n - k - 1)) ≃
      BinaryClass k n (Finset.Icc 1 (2 * n - k - 1)) := unorderedIncreasingEquiv k n _

theorem phi_paper_bijective (k n : ℕ) : Function.Bijective (unorderedPaperEquiv k n) :=
  (unorderedPaperEquiv k n).bijective

/-- The least-edge construction is also well-defined on the unrestricted
unordered source union, independently of its increasing subclass. -/
def unorderedSourcePhi (k n : ℕ) (A : Finset ℕ) :
    UnorderedSourceClass k n A → SourceBinaryClass k n A :=
  fun q => sourcePhi k n A (unorderedCanonicalEquiv k n A q)

theorem unorderedSourcePhi_mk {k n : ℕ} {A : Finset ℕ} (t : LabelledRepresentative k n A) :
    (unorderedSourcePhi k n A (Quotient.mk _ t)).val = phi t.val.normalize := rfl

theorem unorderedIncreasingEquiv_mk {k n : ℕ} {A : Finset ℕ}
    (t : LabelledRepresentative k n A) (ht : t.val.HeapIncreasing) :
    (unorderedIncreasingEquiv k n A ⟨Quotient.mk _ t, ht⟩).val = phi t.val.normalize := rfl

def psiRepresentative {k n : ℕ} {A : Finset ℕ} (t : BinaryClass k n A) : LabelledRepresentative k n A :=
  let s := (increasingEquiv k n A).symm t
  ⟨s.val, s.property.2⟩

theorem psiRepresentative_val {k n : ℕ} {A : Finset ℕ} (t : BinaryClass k n A) :
    (psiRepresentative t).val = psi t.val := rfl

theorem unorderedIncreasingEquiv_symm {k n : ℕ} {A : Finset ℕ} (t : BinaryClass k n A) :
    ((unorderedIncreasingEquiv k n A).symm t).val = Quotient.mk _ (psiRepresentative t) := rfl

theorem unorderedSourcePhi_edgeLabels {k n : ℕ} {A : Finset ℕ} (q : UnorderedSourceClass k n A) :
    (unorderedSourcePhi k n A q).val.edgeLabels = q.edgeLabels := by
  refine Quotient.inductionOn q ?_
  intro t
  change (phi t.val.normalize).edgeLabels = t.val.edgeLabels
  rw [phi_edgeLabels, Rooted.normalize_edgeLabels]

theorem unorderedSourcePhi_vertexLabels {k n : ℕ} {A : Finset ℕ} (q : UnorderedSourceClass k n A) :
    (unorderedSourcePhi k n A q).val.vertexLabels = q.vertexLabels := by
  refine Quotient.inductionOn q ?_
  intro t
  change (phi t.val.normalize).vertexLabels = t.val.vertexLabels
  rw [phi_vertexLabels, Rooted.normalize_vertexLabels]

theorem unorderedIncreasingEquiv_agrees {k n : ℕ} {A : Finset ℕ} (q : UnorderedIncreasingClass k n A) :
    (unorderedIncreasingEquiv k n A q).val = (unorderedSourcePhi k n A q.val).val := rfl

theorem unorderedIncreasingEquiv_edgeLabels {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedIncreasingClass k n A) :
    (unorderedIncreasingEquiv k n A q).val.edgeLabels = q.val.edgeLabels := by
  rw [unorderedIncreasingEquiv_agrees]
  exact unorderedSourcePhi_edgeLabels q.val

theorem unorderedIncreasingEquiv_vertexLabels {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedIncreasingClass k n A) :
    (unorderedIncreasingEquiv k n A q).val.vertexLabels = q.val.vertexLabels := by
  rw [unorderedIncreasingEquiv_agrees]
  exact unorderedSourcePhi_vertexLabels q.val

theorem unorderedIncreasingEquiv_vertexCount {k n : ℕ} {A : Finset ℕ}
    (q : UnorderedIncreasingClass k n A) :
    (unorderedIncreasingEquiv k n A q).val.vertexCount = 2 * n - 1 :=
  (unorderedIncreasingEquiv k n A q).vertexCount

theorem unordered_figure_parameter_error {A : Finset ℕ} (q : UnorderedIncreasingClass 4 8 A) :
    (unorderedIncreasingEquiv 4 8 A q).val.vertexCount = 15 ∧
      ¬∃ b : BinaryClass 4 15 A, b.val = (unorderedIncreasingEquiv 4 8 A q).val := by
  have h15 : (unorderedIncreasingEquiv 4 8 A q).val.vertexCount = 15 := by
    simpa using unorderedIncreasingEquiv_vertexCount q
  refine ⟨h15, ?_⟩
  rintro ⟨b, hb⟩
  have h29 := b.vertexCount
  rw [hb] at h29
  omega

end Freezing1.BinaryBijection
