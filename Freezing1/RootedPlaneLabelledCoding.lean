module

public import Freezing1.RootedPlaneCoding

/-! The finite plane coding retains the actual arbitrary vertex and edge labels. -/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

def Rooted.incoming (t : Rooted) : PlaneTree.Address → Option ℕ
  | [] => none
  | j :: u => if j = 0 then none else (t.children[j - 1]?).bind (fun p =>
      match u with
      | [] => some p.1
      | _ :: _ => p.2.incoming u)

theorem Rooted.incoming_isSome (t : Rooted) (u : PlaneTree.Address) :
    (t.incoming u).isSome = if u = [] then false else (t.subtree u).isSome := by
  induction u generalizing t with
  | nil => rfl
  | cons j u ih =>
    by_cases hj : j = 0
    · simp [incoming, subtree, hj]
    · cases hc : t.children[j - 1]? with
      | none => simp [incoming, subtree, hj, hc]
      | some p =>
        cases u with
        | nil => simp [incoming, subtree, hj, hc]
        | cons k u => simpa [incoming, subtree, hj, hc] using ih p.2

def Rooted.vertexCode (t : Rooted) (u : PlaneTree.Address) : PlaneLabelled.LabelSlot (Option ℕ) :=
  ⟨(t.subtree u).map Rooted.rootLabel⟩

def Rooted.edgeCode (t : Rooted) (u : PlaneTree.Address) : PlaneLabelled.LabelSlot ℕ :=
  ⟨t.incoming u⟩

theorem Rooted.presence_toPlaneTree (t : Rooted) (u : PlaneTree.Address) :
    PlaneLabelled.presence t.toPlaneTree u = (t.subtree u).isSome := by
  unfold PlaneLabelled.presence
  rw [present_iff_subtree]
  simp

def Rooted.toPlaneLabelled (t : Rooted) : PlaneLabelled.Tree (Option ℕ) ℕ := by
  refine ⟨(t.toPlaneTree, t.vertexCode, t.edgeCode), ?_⟩
  intro u
  constructor
  · change ((t.subtree u).map Rooted.rootLabel).isSome = PlaneLabelled.presence t.toPlaneTree u
    rw [Option.isSome_map, presence_toPlaneTree]
  · change (t.incoming u).isSome = PlaneLabelled.edgePresence t.toPlaneTree u
    rw [incoming_isSome]
    by_cases hu : u = [] <;> simp [PlaneLabelled.edgePresence, hu, presence_toPlaneTree]

@[simp] theorem Rooted.shape_toPlaneLabelled (t : Rooted) :
    PlaneLabelled.shape t.toPlaneLabelled = t.toPlaneTree := rfl

@[simp] theorem Rooted.vertexSlot_toPlaneLabelled (t : Rooted) (u : PlaneTree.Address) :
    PlaneLabelled.vertexSlot t.toPlaneLabelled u = t.vertexCode u := rfl

@[simp] theorem Rooted.edgeSlot_toPlaneLabelled (t : Rooted) (u : PlaneTree.Address) :
    PlaneLabelled.edgeSlot t.toPlaneLabelled u = t.edgeCode u := rfl

theorem Rooted.vertexCode_truncate (t : Rooted) (u : PlaneTree.Address) (H : ℕ) (hu : u.length ≤ H) :
    (t.truncate H).vertexCode u = t.vertexCode u := by
  apply PlaneLabelled.LabelSlot.ext_label
  unfold vertexCode
  rw [subtree_truncate t u H hu]
  simp only [Option.map_map, Function.comp_def, rootLabel_truncate]

theorem Rooted.incoming_truncate (t : Rooted) (u : PlaneTree.Address) (H : ℕ) (hu : u.length ≤ H) :
    (t.truncate H).incoming u = t.incoming u := by
  induction u generalizing t H with
  | nil => rfl
  | cons j u ih =>
    cases H with
    | zero => simp at hu
    | succ H =>
      cases t with
      | node label children =>
        by_cases hj : j = 0
        · simp [incoming, hj]
        · simp only [Rooted.truncate_succ, incoming, ite_eq_right hj, Rooted.children,
            List.getElem?_map]
          cases hc : children[j - 1]? with
          | none => simp
          | some p =>
            simp only [Option.map_some, Option.bind_some]
            cases u with
            | nil => rfl
            | cons k u => exact ih p.2 H (by simp only [List.length_cons] at hu ⊢; omega)

theorem Rooted.edgeCode_truncate (t : Rooted) (u : PlaneTree.Address) (H : ℕ) (hu : u.length ≤ H) :
    (t.truncate H).edgeCode u = t.edgeCode u := by
  apply PlaneLabelled.LabelSlot.ext_label
  exact incoming_truncate t u H hu

theorem Rooted.planeBall_truncate (t : Rooted) (h H : ℕ) (hh : h ≤ H) :
    PlaneTree.ball (t.truncate H).toPlaneTree h = PlaneTree.ball t.toPlaneTree h := by
  ext u
  simp only [PlaneTree.mem_ball, present_iff_subtree]
  by_cases hu : u.length ≤ h
  · rw [subtree_isSome_truncate t u H (hu.trans hh)]
  · simp only [hu, and_false]

theorem Rooted.labelledBall_truncate (t : Rooted) (h H : ℕ) (hh : h ≤ H) :
    PlaneLabelled.ball (t.truncate H).toPlaneLabelled h = PlaneLabelled.ball t.toPlaneLabelled h := by
  ext ⟨u, v, e⟩
  simp only [PlaneLabelled.mem_ball, shape_toPlaneLabelled, vertexSlot_toPlaneLabelled,
    edgeSlot_toPlaneLabelled, present_iff_subtree]
  by_cases hu : u.length ≤ h
  · rw [subtree_isSome_truncate t u H (hu.trans hh), vertexCode_truncate t u H (hu.trans hh),
      edgeCode_truncate t u H (hu.trans hh)]
  · simp only [hu, false_and, and_false]

end Freezing1.BinaryBijection
