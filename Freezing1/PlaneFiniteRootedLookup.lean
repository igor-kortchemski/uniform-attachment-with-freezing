module

public import Freezing1.PlaneFiniteRooted

/-! Exact lookup correctness for the actual finite truncation reader. -/

@[expose] public section

namespace Freezing1.PlaneLabelled

open BinaryBijection
open scoped Classical

theorem valid_first_index_of_present (T : Tree (Option ℕ) ℕ) (u : PlaneTree.Address)
    (j : ℕ) (w : PlaneTree.Address) (hp : PlaneTree.Present (shape T) (u ++ j :: w)) :
    1 ≤ j ∧ j ≤ (shape T).val u := by
  have hs : PlaneTree.Present (shape T) (u ++ [j]) :=
    PlaneTree.present_of_prefix ⟨w, by simp [List.append_assoc]⟩ hp
  exact ((PlaneTree.present_append_singleton _ _ _).mp hs).2

@[simp] theorem finiteRootedAt_rootLabel (T : Tree (Option ℕ) ℕ) (u : Vertex (shape T)) (h : ℕ) :
    (finiteRootedAt T u h).rootLabel = vertexLabel T u := by cases h <;> rfl

theorem subtree_finiteRootedAt (T : Tree (Option ℕ) ℕ) (u : Vertex (shape T))
    (h : ℕ) (w : PlaneTree.Address) (hw : w.length ≤ h) :
    (finiteRootedAt T u h).subtree w =
      if hp : PlaneTree.Present (shape T) (u.val ++ w) then
        some (finiteRootedAt T ⟨u.val ++ w, hp⟩ (h - w.length)) else none := by
  induction w generalizing h u with
  | nil => simp [Rooted.subtree, u.property]
  | cons j w ih =>
    cases h with
    | zero => simp at hw
    | succ h =>
      by_cases hj0 : j = 0
      · have hnp : ¬PlaneTree.Present (shape T) (u.val ++ j :: w) := by
          intro hp
          have hh := valid_first_index_of_present T u.val j w hp
          omega
        subst j
        simp [Rooted.subtree, hnp]
      · by_cases hjb : j ≤ (shape T).val u.val
        · have hjl : j - 1 < (shape T).val u.val := by omega
          let idx : Fin ((shape T).val u.val) := ⟨j - 1, hjl⟩
          have haddr : (childVertex T u idx).val ++ w = u.val ++ j :: w := by
            simp [childVertex, idx, List.append_assoc, Nat.sub_add_cancel (by omega : 1 ≤ j)]
          have hh := ih (childVertex T u idx) h (by simp only [List.length_cons] at hw; omega)
          rw [haddr] at hh
          simpa only [finiteRootedAt_succ, Rooted.subtree, ite_eq_right hj0,
            Rooted.children, List.getElem?_ofFn, dite_eq_left hjl, Option.bind_some,
            List.length_cons, Nat.add_sub_add_right] using hh
        · have hjl : ¬j - 1 < (shape T).val u.val := by omega
          have hnp : ¬PlaneTree.Present (shape T) (u.val ++ j :: w) := by
            intro hp
            exact hjb (valid_first_index_of_present T u.val j w hp).2
          simp [finiteRootedAt_succ, Rooted.subtree, Rooted.children, hj0, hjl, hnp]

theorem subtree_finiteRootedAt_isSome (T : Tree (Option ℕ) ℕ) (u : Vertex (shape T))
    (h : ℕ) (w : PlaneTree.Address) (hw : w.length ≤ h) :
    ((finiteRootedAt T u h).subtree w).isSome =
      decide (PlaneTree.Present (shape T) (u.val ++ w)) := by
  rw [subtree_finiteRootedAt T u h w hw]
  split <;> simp_all

theorem vertexCode_finiteRootedAt (T : Tree (Option ℕ) ℕ) (u : Vertex (shape T))
    (h : ℕ) (w : PlaneTree.Address) (hw : w.length ≤ h) :
    (finiteRootedAt T u h).vertexCode w = vertexSlot T (u.val ++ w) := by
  apply LabelSlot.ext_label
  change ((finiteRootedAt T u h).subtree w).map Rooted.rootLabel = _
  rw [subtree_finiteRootedAt T u h w hw]
  split
  next hp =>
    simp only [Option.map_some, finiteRootedAt_rootLabel]
    exact some_vertexLabel T ⟨u.val ++ w, hp⟩
  next hp =>
    rw [vertexSlot_empty_of_absent T _ hp]
    rfl

theorem finiteRootedAt_children_length (T : Tree (Option ℕ) ℕ) (u : Vertex (shape T))
    (h : ℕ) (hh : 0 < h) : (finiteRootedAt T u h).children.length = (shape T).val u.val := by
  cases h with
  | zero => omega
  | succ h => simp [finiteRootedAt_succ, Rooted.children]

theorem offspring_finiteRootedAt (T : Tree (Option ℕ) ℕ) (u : Vertex (shape T))
    (h : ℕ) (w : PlaneTree.Address) (hw : w.length < h) :
    (finiteRootedAt T u h).offspring w = (shape T).val (u.val ++ w) := by
  unfold Rooted.offspring
  rw [subtree_finiteRootedAt T u h w hw.le]
  split
  next hp =>
    simp only [Option.map_some, Option.getD_some]
    exact finiteRootedAt_children_length T ⟨u.val ++ w, hp⟩ _ (by omega)
  next hp =>
    simp only [Option.map_none, Option.getD_none]
    exact (PlaneTree.not_present_offspring_zero (shape T) _ hp).symm

end Freezing1.PlaneLabelled
