module

public import Freezing1.FiniteFullBinaryTrees
public import Freezing1.FullBinaryMaxLabel

/-!
# The genuine one-label growth bijection for increasing binary trees

At stage `m` the integer labels are exactly `1,...,m`. A marked active leaf
is either frozen or split. Deleting the largest label supplies an actual
inverse and proves the one-step bijection used in the counting recurrence.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

theorem FullBinary.labels_eq_edge_vertex (t : FullBinary) : t.labels = t.edgeLabels + t.vertexLabels := by
  induction t with
  | leaf label => cases label <;> simp [labels, edgeLabels, vertexLabels, labelMultiset]
  | fork edge left right ihl ihr =>
    simp only [labels, edgeLabels, vertexLabels, ihl, ihr]
    ac_rfl

theorem FullBinary.vertexCount_le_labels (t : FullBinary) : t.vertexCount ≤ 2 * t.labels.card + 1 := by
  have he := t.edgeLabels_card
  have hv := t.vertexCount_eq
  have hc : t.edgeLabels.card ≤ t.labels.card := by
    rw [labels_eq_edge_vertex, Multiset.card_add]
    omega
  omega

def IncreasingStage (m : ℕ) :=
  {t : FullBinary // t.Increasing ∧ t.labels = (Finset.Icc 1 m).val}

theorem IncreasingStage.label_le {m : ℕ} (t : IncreasingStage m) (label : ℕ) (hl : label ∈ t.val.labels) :
    label ≤ m := by
  rw [t.property.2] at hl
  exact (Finset.mem_Icc.mp hl).2

theorem IncreasingStage.next_label_absent {m : ℕ} (t : IncreasingStage m) : m + 1 ∉ t.val.labels := by
  intro hh
  have := t.label_le (m + 1) hh
  omega

def boundedBinaryCandidates (A : Finset ℕ) (N : ℕ) : Finset FullBinary :=
  (Finset.range (N + 1)).biUnion (binaryCandidates A)

theorem FullBinary.mem_boundedBinaryCandidates (t : FullBinary) (A : Finset ℕ) {N : ℕ}
    (hsize : t.vertexCount ≤ N) (hA : t.LabelsIn A) : t ∈ boundedBinaryCandidates A N :=
  Finset.mem_biUnion.mpr ⟨t.vertexCount, Finset.mem_range.mpr (by omega), t.mem_binaryCandidates A hA⟩

theorem IncreasingStage.vertexCount_bound {m : ℕ} (t : IncreasingStage m) : t.val.vertexCount ≤ 2 * m + 1 := by
  have hh := t.val.vertexCount_le_labels
  rw [t.property.2] at hh
  simpa [Nat.card_Icc] using hh

noncomputable instance increasingStage_fintype (m : ℕ) : Fintype (IncreasingStage m) :=
  Fintype.ofInjective
    (fun t => (⟨t.val, t.val.mem_boundedBinaryCandidates _ t.vertexCount_bound (by
      intro label hl
      rw [t.property.2] at hl
      exact hl)⟩ : {t : FullBinary // t ∈ boundedBinaryCandidates (Finset.Icc 1 m) (2 * m + 1)}))
    (fun _ _ h => Subtype.ext (congrArg
      (fun q : {t : FullBinary // t ∈ boundedBinaryCandidates (Finset.Icc 1 m) (2 * m + 1)} => q.val) h))

theorem stage_labels_succ (m : ℕ) :
    (Finset.Icc 1 m).val + {m + 1} = (Finset.Icc 1 (m + 1)).val := by
  have hs : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
    ext label
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hs, Finset.insert_val_of_notMem (by simp), add_comm, Multiset.singleton_add]

def GrowthInput (m : ℕ) := Σ t : IncreasingStage m, t.val.ActiveLeaf × Bool

noncomputable instance growthInput_fintype (m : ℕ) : Fintype (GrowthInput m) := by
  unfold GrowthInput
  infer_instance

def growStage (m : ℕ) (p : GrowthInput m) : IncreasingStage (m + 1) := by
  rcases p with ⟨t, v, split⟩
  refine ⟨t.val.growActive v (m + 1) split,
    t.val.growActive_increasing v (m + 1) split t.property.1
      (fun label hl => by have := t.label_le label hl; omega), ?_⟩
  rw [FullBinary.growActive_labels, t.property.2, stage_labels_succ]

theorem growStage_injective (m : ℕ) : Function.Injective (growStage m) := by
  rintro ⟨s, v, split⟩ ⟨t, w, split'⟩ hh
  have he := congrArg Subtype.val hh
  have hbase : s.val = t.val := by
    have he' := congrArg (FullBinary.eraseLabel (m + 1)) he
    change (s.val.growActive v (m + 1) split).eraseLabel (m + 1) =
      (t.val.growActive w (m + 1) split').eraseLabel (m + 1) at he'
    rwa [FullBinary.eraseLabel_growActive _ _ _ _ s.next_label_absent,
      FullBinary.eraseLabel_growActive _ _ _ _ t.next_label_absent] at he'
  have hs : s = t := Subtype.ext hbase
  cases hs
  have hleaf : (v, split) = (w, split') := s.val.growActive_injective (m + 1) he
  cases hleaf
  rfl

theorem growStage_surjective (m : ℕ) : Function.Surjective (growStage m) := by
  intro t
  have hnd : t.val.labels.Nodup := by rw [t.property.2]; exact (Finset.Icc 1 (m + 1)).nodup
  have hmem : m + 1 ∈ t.val.labels := by rw [t.property.2]; simp
  obtain ⟨v, split, hv⟩ := t.val.max_growth_decomposition (m + 1) t.property.1 hnd
    (fun label hl => t.label_le label hl) hmem
  have hlabels : (t.val.eraseLabel (m + 1)).labels = (Finset.Icc 1 m).val := by
    have hh := congrArg FullBinary.labels hv
    rw [FullBinary.growActive_labels, t.property.2] at hh
    exact add_right_cancel (hh.trans (stage_labels_succ m).symm)
  let s : IncreasingStage m := ⟨t.val.eraseLabel (m + 1),
    t.val.eraseLabel_increasing (m + 1) t.property.1, hlabels⟩
  exact ⟨⟨s, v, split⟩, Subtype.ext hv⟩

noncomputable def growthEquiv (m : ℕ) : GrowthInput m ≃ IncreasingStage (m + 1) :=
  Equiv.ofBijective (growStage m) ⟨growStage_injective m, growStage_surjective m⟩

theorem growStage_activeCount (m : ℕ) (p : GrowthInput m) :
    (growStage m p).val.activeCount = if p.2.2 then p.1.val.activeCount + 1 else p.1.val.activeCount - 1 :=
  p.1.val.growActive_activeCount p.2.1 (m + 1) p.2.2

end Freezing1.BinaryBijection
