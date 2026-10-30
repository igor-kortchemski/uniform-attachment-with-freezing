module

public import Freezing1.ChronologicalPlaneVertices
public import Freezing1.PlaneTreeGraph

/-! Birth-ordered addresses biject all actual chronological vertices. -/

@[expose] public section

namespace Freezing1.LocalTree

open scoped Classical

theorem follow_append_singleton_eq_some_iff (T : Tree) (s : ℕ)
    (u : PlaneTree.Address) (j b : ℕ) :
    follow T s (u ++ [j]) = some b ↔
      ∃ p, follow T s u = some p ∧ j ≠ 0 ∧ (childList T p)[j - 1]? = some b := by
  rw [follow_append]
  cases hp : follow T s u with
  | none => simp
  | some p =>
    by_cases hj : j = 0
    · simp [follow, hj]
    · cases hc : (childList T p)[j - 1]? <;> simp [follow, hj, hc]

theorem exists_follow_of_vertex (T : Tree) (v : Vertex T) :
    ∃ u : PlaneTree.Address, follow T 0 u = some v.val.birth := by
  generalize hb : v.val.birth = b
  induction b using Nat.strong_induction_on generalizing v with
  | h b ih =>
    by_cases hv : v = root T
    · subst v
      refine ⟨[], ?_⟩
      rw [follow]
      exact congrArg some (by simpa only [root_birth] using hb)
    · obtain ⟨p, hp, _, hlt⟩ := exists_parent T v hv
      obtain ⟨u, hu⟩ := ih p.val.birth (by omega) p rfl
      have hne : v.val.birth ≠ 0 := fun he => hv ((eq_root_iff T v).mpr he)
      have hm : v.val.birth ∈ childList T p.val.birth :=
        (mem_childList_iff T p v).mpr ⟨hne, hp.symm⟩
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
      refine ⟨u ++ [i + 1], ?_⟩
      rw [follow_append, hu, Option.bind_some]
      simp [follow, hi, hb]

theorem follow_zero_eq_unique (T : Tree) (u v : PlaneTree.Address) (b : ℕ)
    (hu : follow T 0 u = some b) (hv : follow T 0 v = some b) : u = v := by
  induction b using Nat.strong_induction_on generalizing u v with
  | h b ih =>
    by_cases hu0 : u = []
    · subst u
      have hb : b = 0 := (Option.some.inj hu).symm
      obtain ⟨w, hwb, hwh⟩ := exists_vertex_of_follow T (root T) v b (by simpa only [root_birth] using hv)
      have hh := vertex_height_le_birth T w
      rw [root_height, zero_add] at hwh
      have hvl : v.length = 0 := by omega
      exact (List.length_eq_zero_iff.mp hvl).symm
    · by_cases hv0 : v = []
      · subst v
        have hb : b = 0 := (Option.some.inj hv).symm
        obtain ⟨w, hwb, hwh⟩ := exists_vertex_of_follow T (root T) u b (by simpa only [root_birth] using hu)
        have hh := vertex_height_le_birth T w
        rw [root_height, zero_add] at hwh
        have hul : u.length = 0 := by omega
        exact List.length_eq_zero_iff.mp hul
      · obtain ⟨up, j, rfl⟩ := PlaneTree.exists_append_singleton_of_ne_nil u hu0
        obtain ⟨vp, k, rfl⟩ := PlaneTree.exists_append_singleton_of_ne_nil v hv0
        obtain ⟨p, hup, hj, hjp⟩ := (follow_append_singleton_eq_some_iff T 0 up j b).mp hu
        obtain ⟨q, hvp, hk, hkq⟩ := (follow_append_singleton_eq_some_iff T 0 vp k b).mp hv
        obtain ⟨w, hwb, _⟩ := exists_vertex_of_follow T (root T) (up ++ [j]) b
          (by simpa only [root_birth] using hu)
        obtain ⟨pv, hpv, _⟩ := exists_vertex_of_follow T (root T) up p
          (by simpa only [root_birth] using hup)
        obtain ⟨qv, hqv, _⟩ := exists_vertex_of_follow T (root T) vp q
          (by simpa only [root_birth] using hvp)
        have hmp : w.val.birth ∈ childList T pv.val.birth := by
          rw [hwb, hpv]
          exact List.mem_of_getElem? hjp
        have hmq : w.val.birth ∈ childList T qv.val.birth := by
          rw [hwb, hqv]
          exact List.mem_of_getElem? hkq
        have hparp := (mem_childList_iff T pv w).mp hmp
        have hparq := (mem_childList_iff T qv w).mp hmq
        have hpq : p = q := by omega
        have hpb : p < b := by
          have hh := (parent_data_of_birth_eq T hparp.1 hparp.2).2
          omega
        have hprefix : up = vp := ih p hpb up vp hup (by simpa only [hpq] using hvp)
        rw [← hpq] at hkq
        obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hjp
        obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hkq
        have hidx : j - 1 = k - 1 := (childList_nodup T p).getElem_inj_iff.mp (hje.trans hke.symm)
        have hjk : j = k := by omega
        rw [hprefix, hjk]

theorem addressVertex_injective (T : Tree) : Function.Injective (addressVertex T) := by
  intro u v he
  apply Subtype.ext
  have hb := congrArg (fun w : Vertex T => w.val.birth) he
  have hv := follow_addressVertex T v
  rw [← hb] at hv
  exact follow_zero_eq_unique T u.val v.val (addressVertex T u).val.birth (follow_addressVertex T u) hv

theorem addressVertex_surjective (T : Tree) : Function.Surjective (addressVertex T) := by
  intro v
  obtain ⟨u, hu⟩ := exists_follow_of_vertex T v
  have hp : PlaneTree.Present (toPlaneTree T) u := by
    apply (present_toPlaneTree_iff_follow T u).mpr
    rw [hu]
    simp
  exact ⟨⟨u, hp⟩, addressVertex_eq_of_follow T _ v hu⟩

noncomputable def chronologicalAddressEquiv (T : Tree) :
    PlaneLabelled.Vertex (toPlaneTree T) ≃ Vertex T :=
  Equiv.ofBijective (addressVertex T) ⟨addressVertex_injective T, addressVertex_surjective T⟩

end Freezing1.LocalTree
