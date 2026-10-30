module

public import Freezing1.UnorderedFiniteTruncation
public import Freezing1.PlaneTreeLabellings

/-!
# Actual Ulam--Harris coding of finite rooted labelled trees

The child-list order is retained only for this auxiliary plane coding.
Integer edge labels and optional natural vertex labels are arbitrary.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open scoped Classical

def Rooted.rootLabel : Rooted → Option ℕ
  | .node label _ => label

def Rooted.children : Rooted → List (ℕ × Rooted)
  | .node _ children => children

def Rooted.subtree (t : Rooted) : PlaneTree.Address → Option Rooted
  | [] => some t
  | j :: u => if j = 0 then none else
      (t.children[j - 1]?).bind (fun p => p.2.subtree u)

theorem Rooted.subtree_append (t : Rooted) (u v : PlaneTree.Address) :
    t.subtree (u ++ v) = (t.subtree u).bind (fun s => s.subtree v) := by
  induction u generalizing t with
  | nil => rfl
  | cons j u ih =>
    by_cases hj : j = 0
    · simp [subtree, hj]
    · simp only [List.cons_append, subtree, ite_eq_right hj]
      cases hc : t.children[j - 1]? with
      | none => simp
      | some p => simpa only [hc, Option.bind_some] using ih p.2

def Rooted.offspring (t : Rooted) (u : PlaneTree.Address) : ℕ :=
  ((t.subtree u).map (fun s => s.children.length)).getD 0

theorem Rooted.canonical_offspring (t : Rooted) : PlaneTree.Canonical t.offspring := by
  intro u j hj
  rw [offspring, subtree_append]
  cases hs : t.subtree u with
  | none => simp
  | some s =>
    have hbad : ¬(1 ≤ j ∧ j ≤ s.children.length) := by
      simpa only [offspring, hs, Option.map_some, Option.getD_some] using hj
    by_cases hj0 : j = 0
    · simp [subtree, hj0]
    · have hlen : s.children.length ≤ j - 1 := by omega
      simp [subtree, hj0, List.getElem?_eq_none hlen]

def Rooted.toPlaneTree (t : Rooted) : PlaneTree.Tree :=
  ⟨t.offspring, t.canonical_offspring⟩

theorem Rooted.present_iff_subtree (t : Rooted) (u : PlaneTree.Address) :
    PlaneTree.Present t.toPlaneTree u ↔ (t.subtree u).isSome := by
  induction u using List.reverseRecOn with
  | nil => simp [subtree]
  | append_singleton u j ih =>
    rw [PlaneTree.present_append_singleton, ih, subtree_append]
    cases hs : t.subtree u with
    | none => simp
    | some s =>
      change ((some s).isSome ∧ 1 ≤ j ∧ j ≤ t.offspring u) ↔ _
      simp only [offspring, hs, Option.map_some, Option.getD_some, Option.isSome_some,
        true_and, Option.bind_some]
      by_cases hj : j = 0
      · simp [subtree, hj]
      · cases hc : s.children[j - 1]? with
        | none =>
          have hlen := List.getElem?_eq_none_iff.mp hc
          simp [subtree, hj, hc]
          omega
        | some p =>
          obtain ⟨hlen, _⟩ := List.getElem?_eq_some_iff.mp hc
          simp [subtree, hj, hc]
          omega

@[simp] theorem Rooted.rootLabel_truncate (t : Rooted) (h : ℕ) :
    (t.truncate h).rootLabel = t.rootLabel := by cases h <;> cases t <;> rfl

theorem Rooted.subtree_truncate (t : Rooted) (u : PlaneTree.Address) (H : ℕ) (hu : u.length ≤ H) :
    (t.truncate H).subtree u = (t.subtree u).map (Rooted.truncate (H - u.length)) := by
  induction u generalizing t H with
  | nil => simp [subtree]
  | cons j u ih =>
    cases H with
    | zero => simp at hu
    | succ H =>
      cases t with
      | node label children =>
        by_cases hj : j = 0
        · simp [subtree, hj]
        · simp only [Rooted.truncate_succ, subtree, ite_eq_right hj, Rooted.children,
            List.getElem?_map]
          cases hc : children[j - 1]? with
          | none => simp
          | some p =>
            simp only [Option.map_some, Option.bind_some]
            simpa only [List.length_cons, Nat.add_sub_add_right] using
              ih p.2 H (by simp only [List.length_cons] at hu; omega)

theorem Rooted.subtree_isSome_truncate (t : Rooted) (u : PlaneTree.Address) (H : ℕ) (hu : u.length ≤ H) :
    ((t.truncate H).subtree u).isSome = (t.subtree u).isSome := by
  rw [subtree_truncate t u H hu, Option.isSome_map]

theorem Rooted.offspring_truncate (t : Rooted) (u : PlaneTree.Address) (H : ℕ) (hu : u.length < H) :
    (t.truncate H).offspring u = t.offspring u := by
  unfold offspring
  rw [subtree_truncate t u H hu.le]
  cases hs : t.subtree u with
  | none => rfl
  | some s =>
    have hpos : 0 < H - u.length := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    rw [hk]
    cases s
    simp [Rooted.truncate_succ, children]

end Freezing1.BinaryBijection
