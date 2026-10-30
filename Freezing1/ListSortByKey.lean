module

public import Mathlib.Data.List.Sort

/-! Canonical sorting by distinct natural-number keys. -/

@[expose] public section

namespace Freezing1.ListSortByKey

variable {α : Type*}

def sort (key : α → ℕ) (l : List α) : List α :=
  l.mergeSort (fun a b => decide (key a ≤ key b))

theorem sort_perm (key : α → ℕ) (l : List α) : (sort key l).Perm l :=
  List.mergeSort_perm _ _

theorem sort_pairwise_le (key : α → ℕ) (l : List α) :
    (sort key l).Pairwise (fun a b => key a ≤ key b) := by
  have h := List.pairwise_mergeSort (le := fun a b : α => decide (key a ≤ key b))
    (fun a b c hab hbc => by simp_all; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  simpa only [decide_eq_true_eq, sort] using h

theorem sort_pairwise (key : α → ℕ) (l : List α) (hnd : (l.map key).Nodup) :
    (sort key l).Pairwise (fun a b => key a < key b) := by
  have hn : ((sort key l).map key).Nodup := ((sort_perm key l).map key).nodup_iff.mpr hnd
  have hne : (sort key l).Pairwise (fun a b => key a ≠ key b) := List.pairwise_map.mp hn
  exact (List.pairwise_and_iff.mpr ⟨sort_pairwise_le key l, hne⟩).imp
    (fun h => lt_of_le_of_ne h.1 h.2)

theorem sort_eq_self (key : α → ℕ) (l : List α)
    (hsorted : l.Pairwise (fun a b => key a < key b)) : sort key l = l := by
  have hnd : (l.map key).Nodup := List.pairwise_map.mpr (hsorted.imp (fun h => ne_of_lt h))
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => False.elim (not_lt_of_ge hab.le hba))
    (sort_pairwise key l hnd) hsorted (sort_perm key l)

theorem sort_eq_of_perm (key : α → ℕ) {l l' : List α} (hperm : l.Perm l')
    (hnd : (l.map key).Nodup) : sort key l = sort key l' := by
  have hnd' : (l'.map key).Nodup := (hperm.map key).nodup_iff.mp hnd
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => False.elim (not_lt_of_ge hab.le hba))
    (sort_pairwise key l hnd) (sort_pairwise key l' hnd')
    ((sort_perm key l).trans (hperm.trans (sort_perm key l').symm))

end Freezing1.ListSortByKey
