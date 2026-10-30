module

public import Freezing1.ForwardLocalGraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Coherent finite balls decode to a locally finite rooted tree

Vertices are precisely the records occurring in some ball; their birth IDs
are globally injective. Parent edges form a connected acyclic graph. Its
actual graph-distance balls recover the original records exactly, and every
neighbourhood is finite. Thus the local space consists of genuine locally
finite rooted trees, rather than merely consistent families of finite data.
-/

@[expose] public section

namespace Freezing1.LocalTree

open scoped Classical

abbrev Vertex (T : Tree) := {r : VertexRecord // ∃ h, r ∈ T.val h}

theorem Tree.balls_mono (T : Tree) {h H : ℕ} (hh : h ≤ H) : T.val h ⊆ T.val H := by
  rw [← T.restrict_ball hh]
  exact Finset.filter_subset _ _

theorem Tree.records_unique (T : Tree) {r s : VertexRecord}
    (hr : ∃ h, r ∈ T.val h) (hs : ∃ h, s ∈ T.val h) (he : r.birth = s.birth) : r = s := by
  obtain ⟨h, hr⟩ := hr
  obtain ⟨H, hs⟩ := hs
  exact (T.property (max h H)).1.unique r
    (T.balls_mono (le_max_left _ _) hr) s (T.balls_mono (le_max_right _ _) hs) he

theorem vertex_birth_injective (T : Tree) :
    Function.Injective (fun v : Vertex T => v.val.birth) := by
  intro v w he
  exact Subtype.ext (T.records_unique v.property w.property he)

theorem vertex_mem_ball_iff (T : Tree) (v : Vertex T) (h : ℕ) :
    v.val ∈ T.val h ↔ v.val.height ≤ h := by
  constructor
  · exact (T.property h).1.bounded v.val
  · intro hv
    obtain ⟨H, hH⟩ := v.property
    have hm := T.balls_mono (le_max_left H h) hH
    rw [← T.restrict_ball (le_max_right H h)]
    exact Finset.mem_filter.mpr ⟨hm, hv⟩

noncomputable def root (T : Tree) : Vertex T :=
  ⟨(T.property 0).1.root.choose, 0, (T.property 0).1.root.choose_spec.1⟩

theorem root_birth (T : Tree) : (root T).val.birth = 0 :=
  (T.property 0).1.root.choose_spec.2

theorem root_height (T : Tree) : (root T).val.height = 0 :=
  ((T.property 0).1.root_data _ (T.property 0).1.root.choose_spec.1 (root_birth T)).2

theorem eq_root_iff (T : Tree) (v : Vertex T) : v = root T ↔ v.val.birth = 0 := by
  constructor
  · rintro rfl; exact root_birth T
  · intro hv
    exact vertex_birth_injective T (hv.trans (root_birth T).symm)

theorem exists_parent (T : Tree) (v : Vertex T) (hv : v ≠ root T) :
    ∃ w : Vertex T, w.val.birth = v.val.parent ∧
      w.val.height + 1 = v.val.height ∧ w.val.birth < v.val.birth := by
  obtain ⟨h, hh⟩ := v.property
  obtain ⟨w, hw, hp, hd, hb⟩ := (T.property h).1.parent_data v.val hh
    (fun he => hv ((eq_root_iff T v).mpr he))
  exact ⟨⟨w, h, hw⟩, hp, hd, hb⟩

def graph (T : Tree) : SimpleGraph (Vertex T) where
  Adj u v := u ≠ v ∧
    ((u.val.birth ≠ 0 ∧ u.val.parent = v.val.birth) ∨
      (v.val.birth ≠ 0 ∧ v.val.parent = u.val.birth))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem parent_data_of_birth_eq (T : Tree) {v w : Vertex T}
    (hv : v.val.birth ≠ 0) (hp : v.val.parent = w.val.birth) :
    w.val.height + 1 = v.val.height ∧ w.val.birth < v.val.birth := by
  obtain ⟨q, hq, hd, hb⟩ := exists_parent T v (fun he => hv ((eq_root_iff T v).mp he))
  have he : q = w := vertex_birth_injective T (hq.trans hp)
  simpa only [he] using And.intro hd hb

theorem height_le_of_adj (T : Tree) {u v : Vertex T} (h : (graph T).Adj u v) :
    v.val.height ≤ u.val.height + 1 := by
  rcases h.2 with h | h
  · have hh := (parent_data_of_birth_eq T h.1 h.2).1
    omega
  · exact (parent_data_of_birth_eq T h.1 h.2).1.ge

theorem height_le_add_length (T : Tree) {u v : Vertex T} (p : (graph T).Walk u v) :
    v.val.height ≤ u.val.height + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have hh := height_le_of_adj T h
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem exists_root_walk (T : Tree) (v : Vertex T) :
    ∃ p : (graph T).Walk (root T) v, p.length = v.val.height := by
  generalize hd : v.val.height = d
  induction d using Nat.strong_induction_on generalizing v with
  | h d ih =>
    by_cases hv : v = root T
    · subst v
      exact ⟨.nil, by simpa only [SimpleGraph.Walk.length_nil, root_height] using hd⟩
    · obtain ⟨w, hp, hh, hb⟩ := exists_parent T v hv
      obtain ⟨p, hlen⟩ := ih w.val.height (by omega) w rfl
      have hwv : w ≠ v := by intro he; have := congrArg (fun q : Vertex T => q.val.birth) he; omega
      have hadj : (graph T).Adj w v :=
        ⟨hwv, Or.inr ⟨fun he => hv ((eq_root_iff T v).mpr he), hp.symm⟩⟩
      exact ⟨p.concat hadj, by simp only [SimpleGraph.Walk.length_concat, hlen]; omega⟩

theorem graph_connected (T : Tree) : (graph T).Connected := by
  apply ((graph T).connected_iff_exists_forall_reachable).mpr
  refine ⟨root T, ?_⟩
  intro v
  obtain ⟨p, _⟩ := exists_root_walk T v
  exact ⟨p⟩

theorem height_eq_dist (T : Tree) (v : Vertex T) :
    v.val.height = (graph T).dist (root T) v := by
  obtain ⟨p, hp⟩ := exists_root_walk T v
  apply le_antisymm
  · obtain ⟨q, hq⟩ := (show (graph T).Reachable (root T) v from ⟨p⟩).exists_walk_length_eq_dist
    simpa only [root_height, zero_add, hq] using height_le_add_length T q
  · simpa only [hp] using (graph T).dist_le p

theorem lower_neighbor_parent (T : Tree) {u v : Vertex T}
    (h : (graph T).Adj v u) (hbirth : u.val.birth ≤ v.val.birth) :
    v.val.parent = u.val.birth := by
  rcases h.2 with h | h
  · exact h.2
  · have hh := (parent_data_of_birth_eq T h.1 h.2).2
    omega

theorem graph_isAcyclic (T : Tree) : (graph T).IsAcyclic := by
  intro u p hp
  obtain ⟨v, hv, hmax⟩ := p.support.toFinset.exists_max_image
    (fun w : Vertex T => w.val.birth) ⟨u, by simp⟩
  have hv' : v ∈ p.support := List.mem_toFinset.mp hv
  let q := p.rotate v hv'
  have hq : q.IsCycle := hp.rotate hv'
  have hupper : ∀ w ∈ q.support, w.val.birth ≤ v.val.birth := by
    intro w hw
    exact hmax w (List.mem_toFinset.mpr ((p.mem_support_rotate_iff v hv').mp hw))
  have hleft := lower_neighbor_parent T (q.adj_snd hq.not_nil)
    (hupper q.snd (q.getVert_mem_support 1))
  have hright := lower_neighbor_parent T (q.adj_penultimate hq.not_nil).symm
    (hupper q.penultimate (q.getVert_mem_support (q.length - 1)))
  exact hq.snd_ne_penultimate (vertex_birth_injective T (hleft.symm.trans hright))

theorem graph_isTree (T : Tree) : (graph T).IsTree :=
  ⟨graph_connected T, graph_isAcyclic T⟩

theorem finite_height_le (T : Tree) (h : ℕ) :
    {v : Vertex T | v.val.height ≤ h}.Finite := by
  have he : {v : Vertex T | v.val.height ≤ h} =
      Subtype.val ⁻¹' (T.val h : Set VertexRecord) := by
    ext v
    exact (vertex_mem_ball_iff T v h).symm
  rw [he]
  exact (T.val h).finite_toSet.preimage (Set.injOn_of_injective Subtype.val_injective)

theorem finite_neighborSet (T : Tree) (v : Vertex T) :
    ((graph T).neighborSet v).Finite :=
  (finite_height_le T (v.val.height + 1)).subset (fun _ h => height_le_of_adj T h)

noncomputable instance graph_locallyFinite (T : Tree) : (graph T).LocallyFinite :=
  fun v => (finite_neighborSet T v).fintype

/-- Every stored ball is exactly the genuine distance ball, with all records
and frozen labels retained, including at the boundary. -/
theorem ball_eq_image_dist (T : Tree) (h : ℕ) :
    (T.val h : Set VertexRecord) =
      Subtype.val '' {v : Vertex T | (graph T).dist (root T) v ≤ h} := by
  ext r
  constructor
  · intro hr
    refine ⟨⟨r, h, hr⟩, ?_, rfl⟩
    change (graph T).dist (root T) ⟨r, h, hr⟩ ≤ h
    rw [← height_eq_dist]
    exact (T.property h).1.bounded r hr
  · rintro ⟨v, hv, rfl⟩
    exact (vertex_mem_ball_iff T v h).mpr (by rwa [height_eq_dist])

theorem graph_adj_iff_union_ballGraph (T : Tree) (u v : Vertex T) :
    (graph T).Adj u v ↔ ∃ h, (ballGraph (T.val h)).Adj u.val.birth v.val.birth := by
  constructor
  · intro huv
    refine ⟨max u.val.height v.val.height, ?_⟩
    exact ⟨fun he => huv.1 (vertex_birth_injective T he), u.val,
      (vertex_mem_ball_iff T u _).mpr (le_max_left _ _), v.val,
      (vertex_mem_ball_iff T v _).mpr (le_max_right _ _), rfl, rfl, huv.2⟩
  · rintro ⟨h, hne, r, hr, s, hs, hu, hv, hadj⟩
    have her : r = u.val := T.records_unique ⟨h, hr⟩ u.property hu
    have hes : s = v.val := T.records_unique ⟨h, hs⟩ v.property hv
    subst r
    subst s
    exact ⟨fun he => hne (congrArg (fun w : Vertex T => w.val.birth) he), hadj⟩

end Freezing1.LocalTree
