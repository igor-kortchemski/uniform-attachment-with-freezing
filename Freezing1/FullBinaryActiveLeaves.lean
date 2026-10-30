module

public import Freezing1.IncreasingBinaryBijection

/-!
# Actual active-leaf updates in a labelled full binary tree

An active leaf can be frozen with a new integer label or split into a
labelled fork with two active leaves. Marked leaves are a genuine finite
type whose cardinality is the actual active-leaf count.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

def FullBinary.ActiveLeaf : FullBinary → Type
  | .leaf none => Unit
  | .leaf (some _) => Empty
  | .fork _ left right => left.ActiveLeaf ⊕ right.ActiveLeaf

instance FullBinary.activeLeafFintype : (t : FullBinary) → Fintype t.ActiveLeaf
  | .leaf none => by change Fintype Unit; infer_instance
  | .leaf (some _) => by change Fintype Empty; infer_instance
  | .fork _ left right => by
      letI := left.activeLeafFintype
      letI := right.activeLeafFintype
      change Fintype (left.ActiveLeaf ⊕ right.ActiveLeaf)
      exact inferInstance

theorem FullBinary.activeLeaf_card (t : FullBinary) : Fintype.card t.ActiveLeaf = t.activeCount := by
  induction t with
  | leaf label => cases label <;> simp [ActiveLeaf, activeCount]
  | fork edge left right ihl ihr => simp only [ActiveLeaf, Fintype.card_sum, ihl, ihr, activeCount]

def FullBinary.replaceActive : (t : FullBinary) → t.ActiveLeaf → FullBinary → FullBinary
  | .leaf none, _, replacement => replacement
  | .leaf (some _), v, _ => Empty.elim v
  | .fork edge left right, .inl v, replacement => .fork edge (left.replaceActive v replacement) right
  | .fork edge left right, .inr v, replacement => .fork edge left (right.replaceActive v replacement)

theorem FullBinary.replaceActive_original (t : FullBinary) (v : t.ActiveLeaf) :
    t.replaceActive v (.leaf none) = t := by
  induction t with
  | leaf label =>
    cases label with
    | none => cases v; rfl
    | some _ => exact Empty.elim v
  | fork edge left right ihl ihr =>
    cases v with
    | inl v => rw [replaceActive, ihl v]
    | inr v => rw [replaceActive, ihr v]

theorem FullBinary.replaceActive_labels (t : FullBinary) (v : t.ActiveLeaf) (replacement : FullBinary) :
    (t.replaceActive v replacement).labels = t.labels + replacement.labels := by
  induction t with
  | leaf label =>
    cases label with
    | none => simp [replaceActive, labels]
    | some _ => exact Empty.elim v
  | fork edge left right ihl ihr =>
    cases v with
    | inl v => simp only [replaceActive, labels, ihl v]; ac_rfl
    | inr v => simp only [replaceActive, labels, ihr v]; ac_rfl

theorem FullBinary.replaceActive_activeCount (t : FullBinary) (v : t.ActiveLeaf) (replacement : FullBinary) :
    (t.replaceActive v replacement).activeCount + 1 = t.activeCount + replacement.activeCount := by
  induction t with
  | leaf label =>
    cases label with
    | none => simp [replaceActive, activeCount, Nat.add_comm]
    | some _ => exact Empty.elim v
  | fork edge left right ihl ihr =>
    cases v with
    | inl v => simp only [replaceActive, activeCount]; have := ihl v; omega
    | inr v => simp only [replaceActive, activeCount]; have := ihr v; omega

def eventReplacement (label : ℕ) (split : Bool) : FullBinary :=
  if split then .fork label (.leaf none) (.leaf none) else .leaf (some label)

def FullBinary.growActive (t : FullBinary) (v : t.ActiveLeaf) (label : ℕ) (split : Bool) : FullBinary :=
  t.replaceActive v (eventReplacement label split)

theorem eventReplacement_labels (label : ℕ) (split : Bool) : (eventReplacement label split).labels = {label} := by
  cases split <;> simp [eventReplacement, FullBinary.labels]

theorem FullBinary.growActive_labels (t : FullBinary) (v : t.ActiveLeaf) (label : ℕ) (split : Bool) :
    (t.growActive v label split).labels = t.labels + {label} := by
  rw [growActive, replaceActive_labels, eventReplacement_labels]

theorem FullBinary.growActive_label_card (t : FullBinary) (v : t.ActiveLeaf) (label : ℕ) (split : Bool) :
    (t.growActive v label split).labels.card = t.labels.card + 1 := by
  rw [growActive_labels, Multiset.card_add, Multiset.card_singleton]

theorem FullBinary.growActive_activeCount (t : FullBinary) (v : t.ActiveLeaf) (label : ℕ) (split : Bool) :
    (t.growActive v label split).activeCount = if split then t.activeCount + 1 else t.activeCount - 1 := by
  have hh := t.replaceActive_activeCount v (eventReplacement label split)
  unfold growActive
  cases split
  all_goals simp [eventReplacement, activeCount] at hh ⊢
  all_goals omega

def FullBinary.eraseLabel (label : ℕ) : FullBinary → FullBinary
  | .leaf none => .leaf none
  | .leaf (some frozen) => if frozen = label then .leaf none else .leaf (some frozen)
  | .fork edge left right => if edge = label then .leaf none else
      .fork edge (eraseLabel label left) (eraseLabel label right)

theorem FullBinary.eraseLabel_of_not_mem (t : FullBinary) (label : ℕ) (hlabel : label ∉ t.labels) :
    t.eraseLabel label = t := by
  induction t with
  | leaf frozen =>
    cases frozen with
    | none => rfl
    | some frozen =>
      have hf : frozen ≠ label := by
        intro he
        apply hlabel
        simp [labels, he]
      simp [eraseLabel, hf]
  | fork edge left right ihl ihr =>
    simp only [labels, Multiset.mem_add, Multiset.mem_singleton, not_or] at hlabel
    simp [eraseLabel, Ne.symm hlabel.1.1, ihl hlabel.1.2, ihr hlabel.2]

theorem FullBinary.eraseLabel_replaceActive (t : FullBinary) (v : t.ActiveLeaf)
    (label : ℕ) (replacement : FullBinary) (hlabel : label ∉ t.labels) :
    (t.replaceActive v replacement).eraseLabel label =
      t.replaceActive v (replacement.eraseLabel label) := by
  induction t with
  | leaf frozen =>
    cases frozen with
    | none => rfl
    | some _ => exact Empty.elim v
  | fork edge left right ihl ihr =>
    simp only [labels, Multiset.mem_add, Multiset.mem_singleton, not_or] at hlabel
    cases v with
    | inl v =>
      simp only [replaceActive, eraseLabel, ite_eq_right (Ne.symm hlabel.1.1),
        ihl v hlabel.1.2, right.eraseLabel_of_not_mem label hlabel.2]
    | inr v =>
      simp only [replaceActive, eraseLabel, ite_eq_right (Ne.symm hlabel.1.1),
        ihr v hlabel.2, left.eraseLabel_of_not_mem label hlabel.1.2]

theorem eraseLabel_eventReplacement (label : ℕ) (split : Bool) :
    (eventReplacement label split).eraseLabel label = .leaf none := by
  cases split <;> simp [eventReplacement, FullBinary.eraseLabel]

theorem FullBinary.eraseLabel_growActive (t : FullBinary) (v : t.ActiveLeaf) (label : ℕ) (split : Bool)
    (hlabel : label ∉ t.labels) : (t.growActive v label split).eraseLabel label = t := by
  rw [growActive, eraseLabel_replaceActive _ _ _ _ hlabel,
    eraseLabel_eventReplacement, replaceActive_original]

theorem FullBinary.growActive_injective (t : FullBinary) (label : ℕ) :
    Function.Injective (fun p : t.ActiveLeaf × Bool => t.growActive p.1 label p.2) := by
  induction t with
  | leaf frozen =>
    cases frozen with
    | none =>
      rintro ⟨⟨⟩, b⟩ ⟨⟨⟩, c⟩ h
      cases b <;> cases c <;> simp_all [growActive, replaceActive, eventReplacement]
    | some frozen => rintro ⟨v, _⟩; exact Empty.elim v
  | fork edge left right ihl ihr =>
    rintro ⟨v, b⟩ ⟨w, c⟩ h
    cases v with
    | inl v =>
      cases w with
      | inl w =>
        have hh := (FullBinary.fork.inj h).2.1
        have he : (v, b) = (w, c) := ihl hh
        cases he
        rfl
      | inr w =>
        have hh := congrArg (fun s : FullBinary => s.labels.card) (FullBinary.fork.inj h).2.1
        change (left.growActive v label b).labels.card = left.labels.card at hh
        rw [growActive_label_card] at hh
        omega
    | inr v =>
      cases w with
      | inl w =>
        have hh := congrArg (fun s : FullBinary => s.labels.card) (FullBinary.fork.inj h).2.2
        change (right.growActive v label b).labels.card = right.labels.card at hh
        rw [growActive_label_card] at hh
        omega
      | inr w =>
        have hh := (FullBinary.fork.inj h).2.2
        have he : (v, b) = (w, c) := ihr hh
        cases he
        rfl

end Freezing1.BinaryBijection
