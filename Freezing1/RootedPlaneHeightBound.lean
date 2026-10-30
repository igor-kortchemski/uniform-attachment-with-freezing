module

public import Freezing1.RootedPlaneLabelledCoding

/-! A truncated actual finite rooted tree has no vertices outside its radius. -/

@[expose] public section

namespace Freezing1.BinaryBijection

theorem Rooted.subtree_truncate_none (t : Rooted) (u : PlaneTree.Address) (H : ℕ)
    (hu : H < u.length) : (t.truncate H).subtree u = none := by
  induction u generalizing t H with
  | nil => simp at hu
  | cons j u ih =>
    cases H with
    | zero =>
      cases t
      simp [Rooted.truncate_zero, Rooted.subtree, Rooted.children]
    | succ H =>
      cases t with
      | node label children =>
        by_cases hj : j = 0
        · simp [Rooted.subtree, hj]
        · simp only [Rooted.truncate_succ, Rooted.subtree, ite_eq_right hj, Rooted.children,
            List.getElem?_map]
          cases hc : children[j - 1]? with
          | none => simp
          | some p =>
            simp only [Option.map_some, Option.bind_some]
            exact ih p.2 H (by simp only [List.length_cons] at hu; omega)

theorem Rooted.present_truncate_bound (t : Rooted) (u : PlaneTree.Address) (H : ℕ)
    (hu : PlaneTree.Present (t.truncate H).toPlaneTree u) : u.length ≤ H := by
  by_contra hh
  have hn := subtree_truncate_none t u H (by omega)
  rw [present_iff_subtree, hn] at hu
  simp at hu

theorem Rooted.present_length_of_fits (t : Rooted) (H : ℕ) (ht : t.truncate H = t)
    (u : PlaneTree.Address) (hu : PlaneTree.Present t.toPlaneTree u) : u.length ≤ H := by
  apply present_truncate_bound t u H
  simpa only [ht] using hu

end Freezing1.BinaryBijection
