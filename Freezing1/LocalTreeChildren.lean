module

public import Freezing1.LocalTreeGraph
public import Mathlib.Data.Finset.Sort

/-!
# Children ordered by their actual birth timestamps

Every vertex has height at most its birth ID, so its record is recoverable
from a fixed finite ball. Children are the actual parent edges, ordered by
increasing birth ID. This is the chronological plane ordering in the paper.
-/

@[expose] public section

namespace Freezing1.LocalTree

open scoped Classical

theorem vertex_height_le_birth (T : Tree) (v : Vertex T) :
    v.val.height ≤ v.val.birth := by
  generalize hb : v.val.birth = b
  induction b using Nat.strong_induction_on generalizing v with
  | h b ih =>
    by_cases hv : v = root T
    · subst v
      rw [root_height]
      exact Nat.zero_le _
    · obtain ⟨w, hp, hh, hwb⟩ := exists_parent T v hv
      have hw := ih w.val.birth (by omega) w rfl
      omega

noncomputable def findRecord (B : Ball) (v : ℕ) : Option VertexRecord :=
  if h : ∃ r ∈ B, r.birth = v then some h.choose else none

theorem findRecord_eq_some_iff {B : Ball} {h : ℕ} (hB : ValidBall h B)
    (v : ℕ) (r : VertexRecord) :
    findRecord B v = some r ↔ r ∈ B ∧ r.birth = v := by
  unfold findRecord
  split_ifs with he
  · constructor
    · intro hh
      have hr : he.choose = r := Option.some.inj hh
      simpa only [hr] using he.choose_spec
    · rintro ⟨hr, hb⟩
      have hh := hB.unique he.choose he.choose_spec.1 r hr (he.choose_spec.2.trans hb.symm)
      rw [hh]
  · constructor
    · intro hh
      contradiction
    · rintro ⟨hr, hb⟩
      exact (he ⟨r, hr, hb⟩).elim

noncomputable def recordAt (T : Tree) (v : ℕ) : Option VertexRecord :=
  findRecord (T.val v) v

theorem recordAt_eq_some_iff (T : Tree) (v : ℕ) (r : VertexRecord) :
    recordAt T v = some r ↔ (∃ h, r ∈ T.val h) ∧ r.birth = v := by
  rw [recordAt, findRecord_eq_some_iff (T.property v).1]
  constructor
  · rintro ⟨hr, hb⟩
    exact ⟨⟨v, hr⟩, hb⟩
  · rintro ⟨hr, hb⟩
    have hh := vertex_height_le_birth T ⟨r, hr⟩
    exact ⟨(vertex_mem_ball_iff T ⟨r, hr⟩ v).mpr (by simpa only [hb] using hh), hb⟩

theorem recordAt_vertex (T : Tree) (v : Vertex T) :
    recordAt T v.val.birth = some v.val :=
  (recordAt_eq_some_iff T _ _).mpr ⟨v.property, rfl⟩

noncomputable def childIDs (T : Tree) (v : ℕ) : Finset ℕ :=
  match recordAt T v with
  | none => ∅
  | some r => ((T.val (r.height + 1)).filter
      (fun q => q.birth ≠ 0 ∧ q.parent = v)).image VertexRecord.birth

theorem mem_childIDs_iff (T : Tree) (v w : Vertex T) :
    w.val.birth ∈ childIDs T v.val.birth ↔
      w.val.birth ≠ 0 ∧ w.val.parent = v.val.birth := by
  rw [childIDs, recordAt_vertex]
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨r, ⟨hr, hpar⟩, hb⟩
    have he := T.records_unique ⟨v.val.height + 1, hr⟩ w.property hb
    simpa only [he] using hpar
  · intro hpar
    have hh := (parent_data_of_birth_eq T hpar.1 hpar.2).1
    refine ⟨w.val, ⟨?_, hpar⟩, rfl⟩
    exact (vertex_mem_ball_iff T w (v.val.height + 1)).mpr hh.ge

noncomputable def childList (T : Tree) (v : ℕ) : List ℕ :=
  (childIDs T v).sort (· ≤ ·)

theorem length_childList (T : Tree) (v : ℕ) :
    (childList T v).length = (childIDs T v).card := Finset.length_sort _

theorem childList_nodup (T : Tree) (v : ℕ) : (childList T v).Nodup :=
  Finset.sort_nodup _ _

theorem mem_childList_iff (T : Tree) (v w : Vertex T) :
    w.val.birth ∈ childList T v.val.birth ↔
      w.val.birth ≠ 0 ∧ w.val.parent = v.val.birth := by
  rw [childList, Finset.mem_sort, mem_childIDs_iff]

end Freezing1.LocalTree
