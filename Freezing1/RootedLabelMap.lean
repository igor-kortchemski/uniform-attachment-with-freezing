module

public import Freezing1.UnorderedBinaryBijection
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Fin.Basic

/-!
# Literal label maps on the source rooted-tree representation

The map changes only numeric edge and frozen-vertex labels. The rooted
incidences and every active/frozen mark are retained. It commutes with the
proved rooted/binary bijection and has an explicit rooted-node equation.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

def FullBinary.relabel (f : ℕ → ℕ) : FullBinary → FullBinary
  | .leaf label => .leaf (label.map f)
  | .fork edge left right => .fork (f edge) (left.relabel f) (right.relabel f)

theorem FullBinary.relabel_comp (t : FullBinary) (f g : ℕ → ℕ) :
    (t.relabel f).relabel g = t.relabel (g ∘ f) := by
  induction t with
  | leaf label => cases label <;> rfl
  | fork edge left right ihl ihr => simp only [relabel, ihl, ihr, Function.comp_apply]

theorem FullBinary.relabel_id (t : FullBinary) : t.relabel id = t := by
  induction t with
  | leaf label => cases label <;> rfl
  | fork edge left right ihl ihr => simp only [relabel, ihl, ihr, id_eq]

theorem FullBinary.relabel_leafCount (t : FullBinary) (f : ℕ → ℕ) :
    (t.relabel f).leafCount = t.leafCount := by
  induction t with
  | leaf label => rfl
  | fork edge left right ihl ihr => simp only [relabel, leafCount, ihl, ihr]

theorem FullBinary.relabel_activeCount (t : FullBinary) (f : ℕ → ℕ) :
    (t.relabel f).activeCount = t.activeCount := by
  induction t with
  | leaf label => cases label <;> rfl
  | fork edge left right ihl ihr => simp only [relabel, activeCount, ihl, ihr]

theorem labelMultiset_map (label : Option ℕ) (f : ℕ → ℕ) :
    labelMultiset (label.map f) = (labelMultiset label).map f := by
  cases label <;> simp [labelMultiset]

theorem FullBinary.relabel_labels (t : FullBinary) (f : ℕ → ℕ) :
    (t.relabel f).labels = t.labels.map f := by
  induction t with
  | leaf label => cases label <;> simp [relabel, labels]
  | fork edge left right ihl ihr => simp [relabel, labels, ihl, ihr, Multiset.map_add]

theorem FullBinary.relabel_edgeLabels (t : FullBinary) (f : ℕ → ℕ) :
    (t.relabel f).edgeLabels = t.edgeLabels.map f := by
  induction t with
  | leaf label => rfl
  | fork edge left right ihl ihr => simp [relabel, edgeLabels, ihl, ihr, Multiset.map_add]

theorem FullBinary.relabel_vertexLabels (t : FullBinary) (f : ℕ → ℕ) :
    (t.relabel f).vertexLabels = t.vertexLabels.map f := by
  induction t with
  | leaf label => exact labelMultiset_map label f
  | fork edge left right ihl ihr => simp [relabel, vertexLabels, ihl, ihr, Multiset.map_add]

theorem FullBinary.relabel_congr_on_labels (t : FullBinary) {f g : ℕ → ℕ}
    (h : ∀ a ∈ t.labels, f a = g a) : t.relabel f = t.relabel g := by
  induction t with
  | leaf label =>
    cases label with
    | none => rfl
    | some a => simp only [relabel, Option.map_some]; rw [h a (by simp [labels])]
  | fork edge left right ihl ihr =>
    rw [relabel, relabel, h edge (by simp [labels]),
      ihl (fun a ha => h a (by simp [labels, ha])),
      ihr (fun a ha => h a (by simp [labels, ha]))]

/-- Strict increase is required only on labels actually present in the
source label set; the total extension outside that finite set is irrelevant. -/
theorem FullBinary.relabel_increasing (t : FullBinary) {A : Finset ℕ} {f : ℕ → ℕ}
    (ht : t.Increasing) (hA : ∀ a ∈ t.labels, a ∈ A) (hf : StrictMonoOn f (A : Set ℕ)) :
    (t.relabel f).Increasing := by
  induction t with
  | leaf label => trivial
  | fork edge left right ihl ihr =>
    rcases ht with ⟨hl, hr, hbl, hbr⟩
    have he : edge ∈ A := hA edge (by simp [labels])
    have hAl : ∀ a ∈ left.labels, a ∈ A := fun a ha => hA a (by simp [labels, ha])
    have hAr : ∀ a ∈ right.labels, a ∈ A := fun a ha => hA a (by simp [labels, ha])
    change (left.relabel f).Increasing ∧ (right.relabel f).Increasing ∧ _ ∧ _
    refine ⟨ihl hl hAl, ihr hr hAr, ?_, ?_⟩
    · rw [relabel_labels]
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
      exact hf he (hAl a ha) (hbl a ha)
    · rw [relabel_labels]
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
      exact hf he (hAr a ha) (hbr a ha)

def Rooted.relabel (f : ℕ → ℕ) (t : Rooted) : Rooted := psi ((phi t).relabel f)

theorem Rooted.phi_relabel (t : Rooted) (f : ℕ → ℕ) :
    phi (t.relabel f) = (phi t).relabel f := phi_psi _

/-- The exact original rooted-tree operation: each same child is retained,
each edge is relabelled, and only frozen vertex labels are mapped. -/
theorem Rooted.relabel_node (f : ℕ → ℕ) (label : Option ℕ) (children : List (ℕ × Rooted)) :
    (Rooted.node label children).relabel f =
      Rooted.node (label.map f) (children.map (fun p => (f p.1, p.2.relabel f))) := by
  induction children with
  | nil => simp [Rooted.relabel, phi, FullBinary.relabel, psi]
  | cons p rest ih =>
    rcases p with ⟨edge, child⟩
    rw [Rooted.relabel, phi, FullBinary.relabel, psi]
    change (match (Rooted.node label rest).relabel f with
      | Rooted.node label' rest' => Rooted.node label' ((f edge, child.relabel f) :: rest')) = _
    rw [ih]
    rfl

theorem Rooted.relabel_comp (t : Rooted) (f g : ℕ → ℕ) :
    (t.relabel f).relabel g = t.relabel (g ∘ f) := by
  unfold relabel
  rw [phi_psi, FullBinary.relabel_comp]

theorem Rooted.relabel_vertexCount (t : Rooted) (f : ℕ → ℕ) :
    (t.relabel f).vertexCount = t.vertexCount := by
  calc
    _ = (phi (t.relabel f)).leafCount := (phi_leafCount _).symm
    _ = ((phi t).relabel f).leafCount := by rw [phi_relabel]
    _ = (phi t).leafCount := FullBinary.relabel_leafCount _ _
    _ = _ := phi_leafCount t

theorem Rooted.relabel_activeCount (t : Rooted) (f : ℕ → ℕ) :
    (t.relabel f).activeCount = t.activeCount := by
  calc
    _ = (phi (t.relabel f)).activeCount := (phi_activeCount _).symm
    _ = ((phi t).relabel f).activeCount := by rw [phi_relabel]
    _ = (phi t).activeCount := FullBinary.relabel_activeCount _ _
    _ = _ := phi_activeCount t

theorem Rooted.relabel_edgeLabels (t : Rooted) (f : ℕ → ℕ) :
    (t.relabel f).edgeLabels = t.edgeLabels.map f := by
  calc
    _ = (phi (t.relabel f)).edgeLabels := (phi_edgeLabels _).symm
    _ = ((phi t).relabel f).edgeLabels := by rw [phi_relabel]
    _ = (phi t).edgeLabels.map f := FullBinary.relabel_edgeLabels _ _
    _ = _ := by rw [phi_edgeLabels]

theorem Rooted.relabel_vertexLabels (t : Rooted) (f : ℕ → ℕ) :
    (t.relabel f).vertexLabels = t.vertexLabels.map f := by
  calc
    _ = (phi (t.relabel f)).vertexLabels := (phi_vertexLabels _).symm
    _ = ((phi t).relabel f).vertexLabels := by rw [phi_relabel]
    _ = (phi t).vertexLabels.map f := FullBinary.relabel_vertexLabels _ _
    _ = _ := by rw [phi_vertexLabels]

/-- Numeric erasure retains rooted incidences and active/frozen marks. -/
def Rooted.numericSkeleton (t : Rooted) : Rooted := t.relabel (fun _ => 0)

theorem Rooted.relabel_numericSkeleton (t : Rooted) (f : ℕ → ℕ) :
    (t.relabel f).numericSkeleton = t.numericSkeleton := by
  unfold numericSkeleton
  rw [relabel_comp]
  rfl

end Freezing1.BinaryBijection
