module

public import Freezing1.BinaryTreeRotation

/-!
# Increasing labelled rooted trees and full plane binary trees

The rooted predicate checks the source's local incident-edge/vertex label
conditions and orders the root children by their distinct edge labels.
The binary predicate checks strict increase of integer labels away from
the root. Active labels occur only on the binary leaves.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

def labelAbove (bound : ℕ) : Option ℕ → Prop
  | none => True
  | some label => bound < label

def Above (bound : ℕ) (labels : Multiset ℕ) : Prop := ∀ label ∈ labels, bound < label

def Rooted.rootAbove : Rooted → ℕ → Prop
  | .node label children, bound =>
      labelAbove bound label ∧ ∀ p ∈ children, bound < p.1

/-- An incoming edge is smaller than every adjacent outgoing edge and
every frozen endpoint label; the first child edge is the least root edge. -/
def Rooted.Increasing : Rooted → Prop
  | .node _ [] => True
  | .node label ((edge, child) :: rest) =>
      child.Increasing ∧ (Rooted.node label rest).Increasing ∧
        child.rootAbove edge ∧ (Rooted.node label rest).rootAbove edge
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

def FullBinary.Increasing : FullBinary → Prop
  | .leaf _ => True
  | .fork edge left right =>
      left.Increasing ∧ right.Increasing ∧ Above edge left.labels ∧ Above edge right.labels

theorem above_cons (bound edge : ℕ) (label : Option ℕ) (child : Rooted)
    (rest : List (ℕ × Rooted)) :
    Above bound (Rooted.node label ((edge, child) :: rest)).labels ↔
      bound < edge ∧ Above bound child.labels ∧ Above bound (Rooted.node label rest).labels := by
  constructor
  · intro hh
    refine ⟨hh edge (by simp [Rooted.labels]), ?_, ?_⟩
    · intro v hv
      exact hh v (by simp [Rooted.labels, hv])
    · intro v hv
      exact hh v (by simp [Rooted.labels, hv])
  · rintro ⟨hedge, hchild, hrest⟩ v hv
    simp only [Rooted.labels, Multiset.mem_add, Multiset.mem_singleton] at hv
    rcases hv with (hv | hv) | hv
    · simpa only [hv] using hedge
    · exact hchild v hv
    · exact hrest v hv

theorem labelAbove_mono {a b : ℕ} (hab : a ≤ b) {label : Option ℕ}
    (hl : labelAbove b label) : labelAbove a label := by
  cases label <;> simp_all [labelAbove]
  omega

theorem Rooted.rootAbove_mono {a b : ℕ} (hab : a ≤ b) {t : Rooted}
    (ht : t.rootAbove b) : t.rootAbove a := by
  cases t with
  | node label children =>
    exact ⟨labelAbove_mono hab ht.1, fun p hp => hab.trans_lt (ht.2 p hp)⟩

theorem Rooted.rootAbove_of_above (t : Rooted) (bound : ℕ) (ht : Above bound t.labels) :
    t.rootAbove bound := by
  cases t with
  | node label children =>
    induction children with
    | nil =>
      cases label with
      | none => simp [Rooted.rootAbove, labelAbove]
      | some label => simpa [Rooted.rootAbove, labelAbove, Above, Rooted.labels] using ht
    | cons p rest ih =>
      rcases p with ⟨edge, child⟩
      have hh := (above_cons bound edge label child rest).mp ht
      have hrest := ih hh.2.2
      refine ⟨hrest.1, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with he | hp
      · simpa only [he] using hh.1
      · exact hrest.2 p hp

theorem Rooted.above_of_increasing : ∀ (t : Rooted) (bound : ℕ),
    t.Increasing → t.rootAbove bound → Above bound t.labels
  | .node label [], bound, _, hb => by
      cases label with
      | none => simp [Above, Rooted.labels]
      | some label => simpa [Above, Rooted.labels, labelAbove] using hb.1
  | .node label ((edge, child) :: rest), bound, hi, hb => by
      rw [Rooted.Increasing] at hi
      rcases hi with ⟨hc, hr, hbc, hbr⟩
      have hbe : bound < edge := hb.2 (edge, child) (by simp)
      exact (above_cons bound edge label child rest).mpr ⟨hbe,
        above_of_increasing child bound hc (rootAbove_mono hbe.le hbc),
        above_of_increasing (.node label rest) bound hr (rootAbove_mono hbe.le hbr)⟩
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem phi_increasing_iff : ∀ t : Rooted, (phi t).Increasing ↔ t.Increasing
  | .node label [] => by simp [phi, FullBinary.Increasing, Rooted.Increasing]
  | .node label ((edge, child) :: rest) => by
      rw [phi, FullBinary.Increasing, Rooted.Increasing,
        phi_increasing_iff child, phi_increasing_iff (.node label rest), phi_labels, phi_labels]
      constructor
      · rintro ⟨hc, hr, hbc, hbr⟩
        exact ⟨hc, hr, child.rootAbove_of_above edge hbc,
          (Rooted.node label rest).rootAbove_of_above edge hbr⟩
      · rintro ⟨hc, hr, hbc, hbr⟩
        exact ⟨hc, hr, child.above_of_increasing edge hc hbc,
          (Rooted.node label rest).above_of_increasing edge hr hbr⟩
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- The source local conditions, written without referring to the binary
map: sorted sibling edges, increasing child trees, increasing edges along
paths, and each frozen vertex label greater than every adjacent edge. -/
theorem Rooted.increasing_node_iff (label : Option ℕ) (children : List (ℕ × Rooted)) :
    (Rooted.node label children).Increasing ↔
      children.Pairwise (fun p q => p.1 < q.1) ∧
        ∀ p ∈ children, p.2.Increasing ∧ p.2.rootAbove p.1 ∧ labelAbove p.1 label := by
  induction children with
  | nil => simp [Rooted.Increasing]
  | cons p rest ih =>
    rcases p with ⟨edge, child⟩
    rw [Rooted.Increasing, ih, List.pairwise_cons]
    constructor
    · rintro ⟨hc, ⟨hs, hrest⟩, hrootc, hrootr⟩
      refine ⟨⟨?_, hs⟩, ?_⟩
      · exact fun p hp => hrootr.2 p hp
      · intro p hp
        rcases List.mem_cons.mp hp with he | hp
        · simpa only [he] using (show child.Increasing ∧ child.rootAbove edge ∧
            labelAbove edge label from ⟨hc, hrootc, hrootr.1⟩)
        · exact hrest p hp
    · rintro ⟨⟨hfirst, hs⟩, hall⟩
      have hhead := hall (edge, child) (by simp)
      refine ⟨hhead.1, ⟨hs, ?_⟩, hhead.2.1, ⟨hhead.2.2, hfirst⟩⟩
      intro p hp
      exact hall p (List.mem_cons_of_mem _ hp)

/-- Canonical representatives of the source's unordered rooted trees.
The strict sibling edge order is forced by `Increasing`; integer labels
are globally distinct and exactly the specified set `A`. -/
def RootedClass (k n : ℕ) (A : Finset ℕ) :=
  {t : Rooted // t.Increasing ∧ t.vertexCount = n ∧ t.activeCount = k ∧ t.labels = A.val}

/-- The parameter `n` is the number of binary leaves, so these full plane
binary trees have `2*n-1` total vertices. -/
def BinaryClass (k n : ℕ) (A : Finset ℕ) :=
  {t : FullBinary // t.Increasing ∧ t.leafCount = n ∧ t.activeCount = k ∧ t.labels = A.val}

/-- The paper's recursive map and its explicitly constructed inverse give
the claimed bijection, with no bijectivity or representation premise. -/
def increasingEquiv (k n : ℕ) (A : Finset ℕ) : RootedClass k n A ≃ BinaryClass k n A where
  toFun t := by
    rcases t with ⟨t, hi, hn, hk, hA⟩
    exact ⟨phi t, (phi_increasing_iff t).mpr hi,
      (phi_leafCount t).trans hn, (phi_activeCount t).trans hk, (phi_labels t).trans hA⟩
  invFun t := by
    rcases t with ⟨t, hi, hn, hk, hA⟩
    refine ⟨psi t, (phi_increasing_iff (psi t)).mp (by simpa only [phi_psi] using hi), ?_, ?_, ?_⟩
    · rw [← phi_leafCount, phi_psi, hn]
    · rw [← phi_activeCount, phi_psi, hk]
    · rw [← phi_labels, phi_psi, hA]
  left_inv t := Subtype.ext (psi_phi t.val)
  right_inv t := Subtype.ext (phi_psi t.val)

/-- Exactly the proposition's standard label set `1,...,2*n-k-1`. -/
def paperEquiv (k n : ℕ) :
    RootedClass k n (Finset.Icc 1 (2 * n - k - 1)) ≃
      BinaryClass k n (Finset.Icc 1 (2 * n - k - 1)) :=
  increasingEquiv k n _

theorem increasingEquiv_apply (k n : ℕ) (A : Finset ℕ) (t : RootedClass k n A) :
    (increasingEquiv k n A t).val = phi t.val := rfl

theorem increasingEquiv_symm_apply (k n : ℕ) (A : Finset ℕ) (t : BinaryClass k n A) :
    ((increasingEquiv k n A).symm t).val = psi t.val := rfl

theorem BinaryClass.vertexCount {k n : ℕ} {A : Finset ℕ} (t : BinaryClass k n A) :
    t.val.vertexCount = 2 * n - 1 := by
  have hh := t.val.vertexCount_eq
  rw [t.property.2.1] at hh
  omega

theorem RootedClass.parameter_card {k n : ℕ} {A : Finset ℕ} (t : RootedClass k n A) :
    A.card + k + 1 = 2 * n := by
  have hh := t.val.labels_card
  rw [t.property.2.1, t.property.2.2.1, t.property.2.2.2] at hh
  exact hh

theorem RootedClass.label_card {k n : ℕ} {A : Finset ℕ} (t : RootedClass k n A) :
    A.card = 2 * n - k - 1 := by
  have hh := t.parameter_card
  omega

theorem RootedClass.positive_parameter {k n : ℕ} {A : Finset ℕ} (t : RootedClass k n A) :
    0 < n := by rw [← t.property.2.1]; exact t.val.vertexCount_pos

theorem FullBinary.activeCount_le_leafCount (t : FullBinary) : t.activeCount ≤ t.leafCount := by
  induction t with
  | leaf label => simp [FullBinary.activeCount, FullBinary.leafCount]; split_ifs <;> omega
  | fork edge left right ihl ihr => simp only [FullBinary.activeCount, FullBinary.leafCount]; omega

theorem RootedClass.active_le_parameter {k n : ℕ} {A : Finset ℕ} (t : RootedClass k n A) :
    k ≤ n := by
  have hh := (phi t.val).activeCount_le_leafCount
  rwa [phi_activeCount, phi_leafCount, t.property.2.1, t.property.2.2.1] at hh

def Rooted.edgeLabels : Rooted → Multiset ℕ
  | .node _ [] => 0
  | .node label ((edge, child) :: rest) => {edge} + child.edgeLabels + (Rooted.node label rest).edgeLabels
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

def Rooted.vertexLabels : Rooted → Multiset ℕ
  | .node label [] => labelMultiset label
  | .node label ((_, child) :: rest) => child.vertexLabels + (Rooted.node label rest).vertexLabels
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

def FullBinary.edgeLabels : FullBinary → Multiset ℕ
  | .leaf _ => 0
  | .fork edge left right => {edge} + left.edgeLabels + right.edgeLabels

def FullBinary.vertexLabels : FullBinary → Multiset ℕ
  | .leaf label => labelMultiset label
  | .fork _ left right => left.vertexLabels + right.vertexLabels

theorem phi_edgeLabels (t : Rooted) : (phi t).edgeLabels = t.edgeLabels := by
  fun_induction phi t <;> simp_all [FullBinary.edgeLabels, Rooted.edgeLabels]

theorem phi_vertexLabels (t : Rooted) : (phi t).vertexLabels = t.vertexLabels := by
  fun_induction phi t <;> simp_all [FullBinary.vertexLabels, Rooted.vertexLabels]

theorem Rooted.labels_eq_parts (t : Rooted) : t.labels = t.edgeLabels + t.vertexLabels := by
  fun_induction phi t
  · rename_i label
    cases label <;> simp [Rooted.labels, Rooted.edgeLabels, Rooted.vertexLabels, labelMultiset]
  · simp_all [Rooted.labels, Rooted.edgeLabels, Rooted.vertexLabels]
    ac_rfl

theorem FullBinary.vertexLabels_card (t : FullBinary) : t.vertexLabels.card + t.activeCount = t.leafCount := by
  induction t with
  | leaf label => cases label <;> simp [vertexLabels, activeCount, leafCount, labelMultiset]
  | fork edge left right ihl ihr => simp_all [vertexLabels, activeCount, leafCount]; omega

theorem FullBinary.edgeLabels_card (t : FullBinary) : t.edgeLabels.card + 1 = t.leafCount := by
  induction t with
  | leaf label => simp [edgeLabels, leafCount]
  | fork edge left right ihl ihr => simp_all [edgeLabels, leafCount]; omega

theorem RootedClass.edge_labels_count {k n : ℕ} {A : Finset ℕ} (t : RootedClass k n A) :
    t.val.edgeLabels.card = n - 1 := by
  have hh := (phi t.val).edgeLabels_card
  rw [phi_edgeLabels, phi_leafCount, t.property.2.1] at hh
  omega

theorem RootedClass.frozen_labels_count {k n : ℕ} {A : Finset ℕ} (t : RootedClass k n A) :
    t.val.vertexLabels.card = n - k := by
  have hh := (phi t.val).vertexLabels_card
  rw [phi_vertexLabels, phi_activeCount, phi_leafCount, t.property.2.1, t.property.2.2.1] at hh
  omega

theorem increasingEquiv_edgeLabels {k n : ℕ} {A : Finset ℕ} (t : RootedClass k n A) :
    (increasingEquiv k n A t).val.edgeLabels = t.val.edgeLabels := phi_edgeLabels _

theorem increasingEquiv_vertexLabels {k n : ℕ} {A : Finset ℕ} (t : RootedClass k n A) :
    (increasingEquiv k n A t).val.vertexLabels = t.val.vertexLabels := phi_vertexLabels _

/-- The example's `n=8` parameter means fifteen binary vertices. -/
theorem figure_binary_vertices {A : Finset ℕ} (t : RootedClass 4 8 A) :
    (increasingEquiv 4 8 A t).val.vertexCount = 15 := by
  simpa using (increasingEquiv 4 8 A t).vertexCount

/-- Source caption/prose error S20: parameter fifteen would instead require
twenty-nine binary vertices, so it cannot describe the displayed image. -/
theorem figure_parameter_fifteen_impossible {A : Finset ℕ} (t : RootedClass 4 8 A) :
    ¬∃ b : BinaryClass 4 15 A, b.val = (increasingEquiv 4 8 A t).val := by
  rintro ⟨b, hb⟩
  have h15 := figure_binary_vertices t
  have h29 := b.vertexCount
  rw [hb] at h29
  omega

end Freezing1.BinaryBijection
