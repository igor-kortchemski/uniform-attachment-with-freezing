module

public import Freezing1.FullBinaryActiveLeaves

/-!
# Removing the largest label gives the unique preceding growth event

The largest label of an increasing full binary tree is a frozen leaf or
a fork with two active leaves. Deletion and the marked-leaf update are
proved on the actual tree datatype, rather than assumed counting rules.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

theorem eventReplacement_increasing (label : ℕ) (split : Bool) :
    (eventReplacement label split).Increasing := by
  cases split <;> simp [eventReplacement, FullBinary.Increasing, Above, FullBinary.labels]

theorem FullBinary.growActive_increasing (t : FullBinary) (v : t.ActiveLeaf) (label : ℕ) (split : Bool)
    (hi : t.Increasing) (hmax : ∀ l ∈ t.labels, l < label) :
    (t.growActive v label split).Increasing := by
  induction t with
  | leaf frozen =>
    cases frozen with
    | none => exact eventReplacement_increasing label split
    | some _ => exact Empty.elim v
  | fork edge left right ihl ihr =>
    rcases hi with ⟨hl, hr, hbl, hbr⟩
    have he : edge < label := hmax edge (by simp [labels])
    cases v with
    | inl v =>
      change (FullBinary.fork edge (left.growActive v label split) right).Increasing
      refine ⟨ihl v hl (fun l hh => hmax l (by simp [labels, hh])), hr, ?_, hbr⟩
      rw [growActive_labels]
      intro l hh
      rcases Multiset.mem_add.mp hh with hh | hh
      · exact hbl l hh
      · simp only [Multiset.mem_singleton] at hh
        simpa only [hh] using he
    | inr v =>
      change (FullBinary.fork edge left (right.growActive v label split)).Increasing
      refine ⟨hl, ihr v hr (fun l hh => hmax l (by simp [labels, hh])), hbl, ?_⟩
      rw [growActive_labels]
      intro l hh
      rcases Multiset.mem_add.mp hh with hh | hh
      · exact hbr l hh
      · simp only [Multiset.mem_singleton] at hh
        simpa only [hh] using he

theorem FullBinary.eraseLabel_labels_le (t : FullBinary) (label : ℕ) :
    (t.eraseLabel label).labels ≤ t.labels := by
  induction t with
  | leaf frozen =>
    cases frozen with
    | none => exact le_rfl
    | some frozen =>
      by_cases hf : frozen = label
      · simp [eraseLabel, hf, labels]
      · simp [eraseLabel, hf, labels]
  | fork edge left right ihl ihr =>
    rw [eraseLabel]
    split_ifs
    · simp [labels]
    · simp only [labels]
      exact add_le_add (add_le_add le_rfl ihl) ihr

theorem FullBinary.eraseLabel_increasing (t : FullBinary) (label : ℕ) (hi : t.Increasing) :
    (t.eraseLabel label).Increasing := by
  induction t with
  | leaf frozen => cases frozen <;> simp [eraseLabel, FullBinary.Increasing]; split_ifs <;> trivial
  | fork edge left right ihl ihr =>
    rcases hi with ⟨hl, hr, hbl, hbr⟩
    rw [eraseLabel]
    split_ifs
    · trivial
    · exact ⟨ihl hl, ihr hr,
        fun l hh => hbl l (Multiset.mem_of_le (left.eraseLabel_labels_le label) hh),
        fun l hh => hbr l (Multiset.mem_of_le (right.eraseLabel_labels_le label) hh)⟩

theorem FullBinary.labels_eq_zero_iff (t : FullBinary) : t.labels = 0 ↔ t = .leaf none := by
  cases t with
  | leaf label => cases label <;> simp [labels]
  | fork edge left right =>
    constructor
    · intro hh
      have hm : edge ∈ (FullBinary.fork edge left right).labels := by simp [labels]
      rw [hh] at hm
      simp at hm
    · intro hh
      cases hh

theorem FullBinary.not_mem_right_of_mem_left {edge label : ℕ} {left right : FullBinary}
    (hnd : (FullBinary.fork edge left right).labels.Nodup) (hl : label ∈ left.labels) :
    label ∉ right.labels := by
  intro hr
  have hc := Multiset.nodup_iff_count_le_one.mp hnd label
  simp only [labels, Multiset.count_add] at hc
  have hcl := Multiset.count_pos.mpr hl
  have hcr := Multiset.count_pos.mpr hr
  omega

theorem FullBinary.max_growth_decomposition (t : FullBinary) (label : ℕ)
    (hi : t.Increasing) (hnd : t.labels.Nodup) (hmax : ∀ l ∈ t.labels, l ≤ label)
    (hmem : label ∈ t.labels) :
    ∃ v : (t.eraseLabel label).ActiveLeaf, ∃ split : Bool,
      (t.eraseLabel label).growActive v label split = t := by
  induction t with
  | leaf frozen =>
    cases frozen with
    | none => simp [labels] at hmem
    | some frozen =>
      have he : frozen = label := (Multiset.mem_singleton.mp hmem).symm
      subst frozen
      have herase : (FullBinary.leaf (some label)).eraseLabel label = .leaf none := by simp [eraseLabel]
      rw [herase]
      refine ⟨(), false, ?_⟩
      simp [growActive, replaceActive, eventReplacement]
  | fork edge left right ihl ihr =>
    rcases hi with ⟨hl, hr, hbl, hbr⟩
    by_cases he : edge = label
    · subst edge
      have hleft : left.labels = 0 := by
        apply Multiset.eq_zero_of_forall_notMem
        intro l hm
        have hh := hmax l (by simp [labels, hm])
        exact (not_lt_of_ge hh) (hbl l hm)
      have hright : right.labels = 0 := by
        apply Multiset.eq_zero_of_forall_notMem
        intro l hm
        have hh := hmax l (by simp [labels, hm])
        exact (not_lt_of_ge hh) (hbr l hm)
      have hl0 := left.labels_eq_zero_iff.mp hleft
      have hr0 := right.labels_eq_zero_iff.mp hright
      subst left
      subst right
      have herase : (FullBinary.fork label (.leaf none) (.leaf none)).eraseLabel label = .leaf none := by
        simp [eraseLabel]
      rw [herase]
      refine ⟨(), true, ?_⟩
      simp [growActive, replaceActive, eventReplacement]
    · have hndL : left.labels.Nodup := Multiset.nodup_of_le
        ((Multiset.le_add_left left.labels {edge}).trans (Multiset.le_add_right _ _)) hnd
      have hndR : right.labels.Nodup := Multiset.nodup_of_le (Multiset.le_add_left _ _) hnd
      by_cases hml : label ∈ left.labels
      · have hmr := not_mem_right_of_mem_left hnd hml
        obtain ⟨v, split, hv⟩ := ihl hl hndL (fun l hh => hmax l (by simp [labels, hh])) hml
        rw [eraseLabel, ite_eq_right he, right.eraseLabel_of_not_mem label hmr]
        refine ⟨Sum.inl v, split, ?_⟩
        change FullBinary.fork edge ((left.eraseLabel label).growActive v label split) right =
          FullBinary.fork edge left right
        rw [hv]
      · have hmr : label ∈ right.labels := by
          simpa [labels, Ne.symm he, hml] using hmem
        obtain ⟨v, split, hv⟩ := ihr hr hndR (fun l hh => hmax l (by simp [labels, hh])) hmr
        rw [eraseLabel, ite_eq_right he, left.eraseLabel_of_not_mem label hml]
        refine ⟨Sum.inr v, split, ?_⟩
        change FullBinary.fork edge left ((right.eraseLabel label).growActive v label split) =
          FullBinary.fork edge left right
        rw [hv]

end Freezing1.BinaryBijection
