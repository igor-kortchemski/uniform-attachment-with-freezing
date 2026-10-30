module

public import Mathlib.Data.Tree.Basic
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Tactic

/-!
# The recursive edge-to-binary rotation

Rooted edge-labelled trees are stored with an explicit child list. The
increasing source class will require the canonical increasing edge order.
Active vertices have label `none`; frozen vertices have a natural label.
The binary target has ordered children and retains labels on its leaves.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

inductive Rooted where
  | node (label : Option ℕ) (children : List (ℕ × Rooted)) : Rooted
  deriving Repr

/-- Unlike Mathlib's `BinaryTree`, the source target also labels leaves. -/
inductive FullBinary where
  | leaf (label : Option ℕ) : FullBinary
  | fork (label : ℕ) (left right : FullBinary) : FullBinary
  deriving DecidableEq, Repr

def phi : Rooted → FullBinary
  | .node label [] => .leaf label
  | .node label ((edge, child) :: rest) =>
      .fork edge (phi child) (phi (.node label rest))
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

def psi : FullBinary → Rooted
  | .leaf label => .node label []
  | .fork edge left right =>
      match psi right with
      | .node label rest => .node label ((edge, psi left) :: rest)

theorem psi_phi (t : Rooted) : psi (phi t) = t := by
  fun_induction phi t <;> simp_all [psi]

theorem phi_psi (t : FullBinary) : phi (psi t) = t := by
  induction t with
  | leaf label => simp [psi, phi]
  | fork edge left right ihl ihr =>
    cases he : psi right with
    | node label rest =>
      simp only [psi, he, phi, ihl]
      congr 1
      simpa only [he] using ihr

def rawEquiv : Rooted ≃ FullBinary where
  toFun := phi
  invFun := psi
  left_inv := psi_phi
  right_inv := phi_psi

def Rooted.vertexCount : Rooted → ℕ
  | .node _ [] => 1
  | .node label ((_, child) :: rest) => child.vertexCount + (Rooted.node label rest).vertexCount
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

def Rooted.activeCount : Rooted → ℕ
  | .node label [] => if label = none then 1 else 0
  | .node label ((_, child) :: rest) => child.activeCount + (Rooted.node label rest).activeCount
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

def Rooted.labels : Rooted → Multiset ℕ
  | .node none [] => 0
  | .node (some label) [] => {label}
  | .node label ((edge, child) :: rest) => {edge} + child.labels + (Rooted.node label rest).labels
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

def Rooted.edgeCount : Rooted → ℕ
  | .node _ [] => 0
  | .node label ((_, child) :: rest) => 1 + child.edgeCount + (Rooted.node label rest).edgeCount
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

def labelMultiset : Option ℕ → Multiset ℕ
  | none => 0
  | some label => {label}

theorem Rooted.vertexCount_node (label : Option ℕ) (children : List (ℕ × Rooted)) :
    (Rooted.node label children).vertexCount = 1 + (children.map (fun p => p.2.vertexCount)).sum := by
  induction children with
  | nil => simp [vertexCount]
  | cons p rest ih =>
    rcases p with ⟨edge, child⟩
    simp only [vertexCount, List.map_cons, List.sum_cons, ih]
    omega

theorem Rooted.activeCount_node (label : Option ℕ) (children : List (ℕ × Rooted)) :
    (Rooted.node label children).activeCount =
      (if label = none then 1 else 0) + (children.map (fun p => p.2.activeCount)).sum := by
  induction children with
  | nil => simp [activeCount]
  | cons p rest ih =>
    rcases p with ⟨edge, child⟩
    simp only [activeCount, List.map_cons, List.sum_cons, ih]
    omega

theorem Rooted.labels_node (label : Option ℕ) (children : List (ℕ × Rooted)) :
    (Rooted.node label children).labels =
      labelMultiset label + (children.map (fun p => ({p.1} : Multiset ℕ) + p.2.labels)).sum := by
  induction children with
  | nil => cases label <;> simp [labels, labelMultiset]
  | cons p rest ih =>
    rcases p with ⟨edge, child⟩
    simp only [labels, List.map_cons, List.sum_cons, ih]
    ac_rfl

def FullBinary.leafCount : FullBinary → ℕ
  | .leaf _ => 1
  | .fork _ left right => left.leafCount + right.leafCount

def FullBinary.vertexCount : FullBinary → ℕ
  | .leaf _ => 1
  | .fork _ left right => 1 + left.vertexCount + right.vertexCount

def FullBinary.activeCount : FullBinary → ℕ
  | .leaf label => if label = none then 1 else 0
  | .fork _ left right => left.activeCount + right.activeCount

def FullBinary.labels : FullBinary → Multiset ℕ
  | .leaf none => 0
  | .leaf (some label) => {label}
  | .fork edge left right => {edge} + left.labels + right.labels

theorem phi_leafCount (t : Rooted) : (phi t).leafCount = t.vertexCount := by
  fun_induction phi t <;> simp_all [FullBinary.leafCount, Rooted.vertexCount]

theorem phi_activeCount (t : Rooted) : (phi t).activeCount = t.activeCount := by
  fun_induction phi t <;> simp_all [FullBinary.activeCount, Rooted.activeCount]

theorem phi_labels (t : Rooted) : (phi t).labels = t.labels := by
  fun_induction phi t
  · rename_i label
    cases label <;> simp [FullBinary.labels, Rooted.labels]
  · simp_all [FullBinary.labels, Rooted.labels]

theorem FullBinary.vertexCount_eq (t : FullBinary) : t.vertexCount + 1 = 2 * t.leafCount := by
  induction t with
  | leaf label => rfl
  | fork edge left right ihl ihr =>
    simp only [vertexCount, leafCount]
    omega

theorem phi_vertexCount (t : Rooted) : (phi t).vertexCount = 2 * t.vertexCount - 1 := by
  have hh := (phi t).vertexCount_eq
  rw [phi_leafCount] at hh
  omega

theorem FullBinary.leafCount_pos (t : FullBinary) : 0 < t.leafCount := by
  induction t <;> simp_all [leafCount]

theorem Rooted.vertexCount_pos (t : Rooted) : 0 < t.vertexCount := by
  rw [← phi_leafCount]
  exact FullBinary.leafCount_pos _

theorem Rooted.edgeCount_succ (t : Rooted) : t.edgeCount + 1 = t.vertexCount := by
  fun_induction phi t
  all_goals simp_all [Rooted.edgeCount, Rooted.vertexCount]
  all_goals omega

theorem Rooted.labels_card (t : Rooted) : t.labels.card + t.activeCount + 1 = 2 * t.vertexCount := by
  fun_induction phi t
  · rename_i label
    cases label <;> simp [Rooted.labels, Rooted.activeCount, Rooted.vertexCount]
  · simp_all [Rooted.labels, Rooted.activeCount, Rooted.vertexCount]
    omega

end Freezing1.BinaryBijection
