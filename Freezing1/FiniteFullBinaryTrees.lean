module

public import Freezing1.UnorderedBinaryBijection
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree

/-!
# Genuine finite classes for the tangent-number enumeration

Finite candidates are built from labelled leaves and all smaller pairs of
full binary subtrees. They contain the actual increasing classes, rather
than an assumed sequence of cardinalities. The tangent/Bernoulli formula
requires further counting and analytic theorems.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical BigOperators

def leafCandidates (A : Finset ℕ) : Finset FullBinary :=
  insert (.leaf none) (A.image (fun label => .leaf (some label)))

def binaryCandidates (A : Finset ℕ) : ℕ → Finset FullBinary
  | 0 => ∅
  | m + 1 => (if m = 0 then leafCandidates A else ∅) ∪
      (Finset.antidiagonal m).attach.biUnion (fun ij =>
        A.biUnion (fun edge =>
          ((binaryCandidates A ij.val.1) ×ˢ (binaryCandidates A ij.val.2)).image
            (fun p => .fork edge p.1 p.2)))
termination_by m => m
decreasing_by
  all_goals have hm := Finset.mem_antidiagonal.mp ij.property
  all_goals omega

theorem binaryCandidates_succ (A : Finset ℕ) (m : ℕ) :
    binaryCandidates A (m + 1) = (if m = 0 then leafCandidates A else ∅) ∪
      (Finset.antidiagonal m).biUnion (fun ij => A.biUnion (fun edge =>
        ((binaryCandidates A ij.1) ×ˢ (binaryCandidates A ij.2)).image
          (fun p => .fork edge p.1 p.2))) := by
  rw [binaryCandidates]
  ext t
  simp

def FullBinary.LabelsIn (t : FullBinary) (A : Finset ℕ) : Prop := ∀ label ∈ t.labels, label ∈ A

theorem FullBinary.labelsIn_fork (edge : ℕ) (left right : FullBinary) (A : Finset ℕ) :
    (FullBinary.fork edge left right).LabelsIn A ↔
      edge ∈ A ∧ left.LabelsIn A ∧ right.LabelsIn A := by
  simp [FullBinary.LabelsIn, FullBinary.labels, or_imp, forall_and]

theorem FullBinary.mem_binaryCandidates (t : FullBinary) (A : Finset ℕ) (hA : t.LabelsIn A) :
    t ∈ binaryCandidates A t.vertexCount := by
  induction t with
  | leaf label =>
    cases label with
    | none => simp [FullBinary.vertexCount, binaryCandidates_succ, leafCandidates]
    | some label =>
      have hm : label ∈ A := hA label (by simp [FullBinary.labels])
      simp [FullBinary.vertexCount, binaryCandidates_succ, leafCandidates, hm]
  | fork edge left right ihl ihr =>
    rcases (FullBinary.labelsIn_fork edge left right A).mp hA with ⟨he, hl, hr⟩
    rw [FullBinary.vertexCount, show 1 + left.vertexCount + right.vertexCount =
      (left.vertexCount + right.vertexCount) + 1 by omega, binaryCandidates_succ]
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨(left.vertexCount, right.vertexCount), by simp, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨edge, he, ?_⟩
    exact Finset.mem_image.mpr ⟨(left, right), Finset.mem_product.mpr ⟨ihl hl, ihr hr⟩, rfl⟩

noncomputable instance finite_size_labels (A : Finset ℕ) (N : ℕ) :
    Fintype {t : FullBinary // t.vertexCount = N ∧ t.LabelsIn A} :=
  Fintype.ofInjective
    (fun t => (⟨t.val, by
      simpa only [t.property.1] using t.val.mem_binaryCandidates A t.property.2⟩ :
      {t : FullBinary // t ∈ binaryCandidates A N}))
    (fun _ _ h => Subtype.ext
      (congrArg (fun q : {t : FullBinary // t ∈ binaryCandidates A N} => q.val) h))

theorem FullBinary.labels_card_total (t : FullBinary) : t.labels.card + t.activeCount = t.vertexCount := by
  induction t with
  | leaf label => cases label <;> simp [FullBinary.labels, FullBinary.activeCount, FullBinary.vertexCount]
  | fork edge left right ihl ihr =>
    simp_all [FullBinary.labels, FullBinary.activeCount, FullBinary.vertexCount]
    omega

noncomputable instance binaryClass_fintype (k n : ℕ) (A : Finset ℕ) : Fintype (BinaryClass k n A) :=
  Fintype.ofInjective
    (fun t => (⟨t.val, t.vertexCount, by
      intro label hl
      rw [t.property.2.2.2] at hl
      exact hl⟩ : {t : FullBinary // t.vertexCount = 2 * n - 1 ∧ t.LabelsIn A}))
    (fun _ _ h => Subtype.ext
      (congrArg (fun q : {t : FullBinary // t.vertexCount = 2 * n - 1 ∧ t.LabelsIn A} => q.val) h))

def FullyFrozenClass (A : Finset ℕ) :=
  {t : FullBinary // t.Increasing ∧ t.activeCount = 0 ∧ t.labels = A.val}

noncomputable instance fullyFrozen_fintype (A : Finset ℕ) : Fintype (FullyFrozenClass A) :=
  Fintype.ofInjective
    (fun t => (⟨t.val, by
      have hh := t.val.labels_card_total
      rw [t.property.2.1, t.property.2.2, add_zero] at hh
      exact hh.symm,
      by intro label hl; rw [t.property.2.2] at hl; exact hl⟩ :
      {t : FullBinary // t.vertexCount = A.card ∧ t.LabelsIn A}))
    (fun _ _ h => Subtype.ext
      (congrArg (fun q : {t : FullBinary // t.vertexCount = A.card ∧ t.LabelsIn A} => q.val) h))

noncomputable def frozenBinaryCount (A : Finset ℕ) : ℕ := Nat.card (FullyFrozenClass A)

def fullyFrozenEquiv (n : ℕ) (hn : 0 < n) (A : Finset ℕ) (hA : A.card = 2 * n - 1) :
    BinaryClass 0 n A ≃ FullyFrozenClass A where
  toFun t := ⟨t.val, t.property.1, t.property.2.2⟩
  invFun t := by
    refine ⟨t.val, t.property.1, ?_, t.property.2⟩
    have hh := t.val.labels_card_total
    rw [t.property.2.1, t.property.2.2, add_zero] at hh
    have hs := t.val.vertexCount_eq
    change A.card = t.val.vertexCount at hh
    rw [hA] at hh
    omega
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem source_fullyFrozen_card (n : ℕ) (hn : 0 < n) :
    Nat.card (UnorderedIncreasingClass 0 n (Finset.Icc 1 (2 * n - 1))) =
      frozenBinaryCount (Finset.Icc 1 (2 * n - 1)) := by
  apply Nat.card_congr
  exact (unorderedPaperEquiv 0 n).trans
    (fullyFrozenEquiv n hn _ (by simp [Nat.card_Icc]))

end Freezing1.BinaryBijection
