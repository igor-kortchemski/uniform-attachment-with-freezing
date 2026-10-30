module

public import Freezing1.PlaneFiniteRootedLookup
public import Freezing1.PlaneTreeGraph

/-! The finite truncation reader also retains every actual incoming-edge label. -/

@[expose] public section

namespace Freezing1.BinaryBijection

theorem Rooted.incoming_cons_of_ne_nil (t : Rooted) (j : ℕ) (u : PlaneTree.Address) (hu : u ≠ []) :
    t.incoming (j :: u) = if j = 0 then none else
      (t.children[j - 1]?).bind (fun p => p.2.incoming u) := by
  cases u with
  | nil => exact (hu rfl).elim
  | cons k u => rfl

theorem Rooted.incoming_append_singleton (t : Rooted) (u : PlaneTree.Address) (j : ℕ) :
    t.incoming (u ++ [j]) = (t.subtree u).bind (fun s =>
      if j = 0 then none else (s.children[j - 1]?).map Prod.fst) := by
  induction u generalizing t with
  | nil =>
    change (if j = 0 then none else (t.children[j - 1]?).bind (fun p => some p.1)) =
      (if j = 0 then none else (t.children[j - 1]?).map Prod.fst)
    by_cases hj : j = 0
    · simp only [ite_eq_left hj]
    · simp only [ite_eq_right hj]
      cases t.children[j - 1]? <;> rfl
  | cons k u ih =>
    rw [List.cons_append, incoming_cons_of_ne_nil _ _ _ (by simp), subtree]
    by_cases hk : k = 0
    · simp [hk]
    · simp only [ite_eq_right hk]
      cases hc : t.children[k - 1]? with
      | none => simp
      | some p => simpa only [Option.bind_some] using ih p.2

end Freezing1.BinaryBijection

namespace Freezing1.PlaneLabelled

open BinaryBijection
open scoped Classical

theorem edgeCode_finiteRooted (T : Tree (Option ℕ) ℕ) (h : ℕ) (w : PlaneTree.Address)
    (hw : w.length ≤ h) : (finiteRooted T h).edgeCode w = edgeSlot T w := by
  apply LabelSlot.ext_label
  by_cases hw0 : w = []
  · subst w
    rw [root_edgeSlot]
    rfl
  · obtain ⟨v, j, rfl⟩ := PlaneTree.exists_append_singleton_of_ne_nil w hw0
    have hv : v.length < h := by simp only [List.length_append, List.length_singleton] at hw; omega
    change (finiteRooted T h).incoming (v ++ [j]) = (edgeSlot T (v ++ [j])).label
    rw [Rooted.incoming_append_singleton]
    have hs := subtree_finiteRootedAt T ⟨[], PlaneTree.present_nil _⟩ h v hv.le
    simp only [List.nil_append] at hs
    change (finiteRooted T h).subtree v = _ at hs
    rw [hs]
    by_cases hp : PlaneTree.Present (shape T) v
    · rw [dite_eq_left hp, Option.bind_some]
      have hrem : 0 < h - v.length := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrem)
      rw [hk, finiteRootedAt_succ, Rooted.children]
      by_cases hj0 : j = 0
      · have hnp : ¬PlaneTree.Present (shape T) (v ++ [j]) := by
          intro hh
          have := ((PlaneTree.present_append_singleton _ _ _).mp hh).2.1
          omega
        rw [edgeSlot_empty_of_absent T _ hnp]
        simp [hj0, emptySlot]
      · rw [ite_eq_right hj0]
        by_cases hjb : j ≤ (shape T).val v
        · have hjl : j - 1 < (shape T).val v := by omega
          let idx : Fin ((shape T).val v) := ⟨j - 1, hjl⟩
          rw [List.getElem?_ofFn, dite_eq_left hjl, Option.map_some]
          have hlabel := some_edgeLabel T (childEdge T ⟨v, hp⟩ idx)
          simpa only [childEdge, childVertex, idx,
            Nat.sub_add_cancel (by omega : 1 ≤ j)] using hlabel
        · have hjl : ¬j - 1 < (shape T).val v := by omega
          have hnp : ¬PlaneTree.Present (shape T) (v ++ [j]) := by
            intro hh
            exact hjb ((PlaneTree.present_append_singleton _ _ _).mp hh).2.2
          rw [edgeSlot_empty_of_absent T _ hnp]
          simp [hjl, emptySlot]
    · have hnp : ¬PlaneTree.Present (shape T) (v ++ [j]) := by
        intro hh
        exact hp ((PlaneTree.present_append_singleton _ _ _).mp hh).1
      rw [dite_eq_right hp, Option.bind_none, edgeSlot_empty_of_absent T _ hnp]
      rfl

theorem vertexCode_finiteRooted (T : Tree (Option ℕ) ℕ) (h : ℕ) (w : PlaneTree.Address)
    (hw : w.length ≤ h) : (finiteRooted T h).vertexCode w = vertexSlot T w := by
  simpa only [finiteRooted, List.nil_append] using
    vertexCode_finiteRootedAt T ⟨[], PlaneTree.present_nil _⟩ h w hw

theorem offspring_finiteRooted (T : Tree (Option ℕ) ℕ) (h : ℕ) (w : PlaneTree.Address)
    (hw : w.length < h) : (finiteRooted T h).offspring w = (shape T).val w := by
  simpa only [finiteRooted, List.nil_append] using
    offspring_finiteRootedAt T ⟨[], PlaneTree.present_nil _⟩ h w hw

end Freezing1.PlaneLabelled
