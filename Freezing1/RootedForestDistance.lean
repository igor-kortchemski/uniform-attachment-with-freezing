module

public import Freezing1.RootedForestCoalescence

/-!
# Distances under the actual forest operations

Adding a bridge preserves the distance between vertices already connected.
For vertices in the two components joined by that bridge, a signed-depth
potential proves the exact distance without assuming a lowest common ancestor.
-/

@[expose] public section

namespace Freezing1.RootedForest

open scoped Classical

variable {V : Type*}

/-- An acyclic graph extension preserves distances within an old component. -/
theorem dist_eq_of_le_isAcyclic {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : H.IsAcyclic) {u v : V} (huv : G.Reachable u v) : H.dist u v = G.dist u v := by
  obtain ⟨p, hp, hplen⟩ := huv.exists_path_of_dist
  obtain ⟨q, hq, hqlen⟩ := (huv.mono hGH).exists_path_of_dist
  have he : p.mapLe hGH = q := Subtype.mk.inj
    ((hH.subsingleton_path u v).elim ⟨p.mapLe hGH, hp.mapLe hGH⟩ ⟨q, hq⟩)
  have hh := congrArg SimpleGraph.Walk.length he
  simpa only [SimpleGraph.Walk.length_mapLe, hplen, hqlen] using hh.symm

variable [DecidableEq V]

/-- A path through the common root bounds distance by the two depths. -/
theorem dist_le_depth_add_depth (F : RootedForest V) {u v : V}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (hroot : F.root u = F.root v) :
    F.graph.dist u v ≤ F.depth u + F.depth v := by
  obtain ⟨p, hp⟩ := F.exists_root_walk hu
  have hv' : ∃ q : F.graph.Walk (F.root u) v, q.length = F.depth v := by
    rw [hroot]
    exact F.exists_root_walk hv
  obtain ⟨q, hq⟩ := hv'
  have hh := F.graph.dist_le (p.reverse.append q)
  simpa only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hp, hq] using hh

/-- The graph of a merge contains every old edge. -/
theorem graph_le_join (F : RootedForest V) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    F.graph ≤ (F.join a b ha hb hab).graph := by
  rw [F.join_graph ha hb hab]
  exact le_sup_left

/-- A bridge cannot change a distance inside an old component. -/
theorem join_preserves_dist (F : RootedForest V) (hF : F.graph.IsAcyclic)
    {a b u v : V} (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b)
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (hroot : F.root u = F.root v) :
    (F.join a b ha hb hab).graph.dist u v = F.graph.dist u v :=
  dist_eq_of_le_isAcyclic (F.graph_le_join ha hb hab) (F.join_isAcyclic hF ha hb hab)
    ((F.root_eq_iff_reachable hu hv).mp hroot)

/-- Adding an isolated vertex leaves the ambient graph and all its distances unchanged. -/
theorem adjoin_preserves_dist (F : RootedForest V) {w : V} (hw : w ∉ F.vertices) (u v : V) :
    (F.adjoin w hw).graph.dist u v = F.graph.dist u v := by rw [F.adjoin_graph hw]

omit [DecidableEq V] in
/-- A one-Lipschitz integer potential changes by at most the length of a walk. -/
theorem potential_le_add_length {G : SimpleGraph V} (f : V → ℤ)
    (hf : ∀ {u v}, G.Adj u v → f v ≤ f u + 1) {u v : V} (p : G.Walk u v) :
    f v ≤ f u + (p.length : ℤ) := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have hh := hf h
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    omega

/-- Negative depth on the child component measures distance across the new bridge. -/
def joinPotential (F : RootedForest V) (b v : V) : ℤ :=
  if F.root v = b then -(F.depth v : ℤ) - 1 else (F.depth v : ℤ)

theorem joinPotential_le_of_old_adj (F : RootedForest V) (b : V) {u v : V}
    (h : F.graph.Adj u v) : F.joinPotential b v ≤ F.joinPotential b u + 1 := by
  have hr := F.root_eq_of_adj h
  have hdu : (F.depth v : ℤ) ≤ (F.depth u : ℤ) + 1 := by exact_mod_cast F.depth_le_of_adj h
  have hdv : (F.depth u : ℤ) ≤ (F.depth v : ℤ) + 1 := by exact_mod_cast F.depth_le_of_adj h.symm
  by_cases hu : F.root u = b
  · have hv : F.root v = b := hr.symm.trans hu
    simp only [joinPotential, hu, hv, ite_true]
    omega
  · have hv : F.root v ≠ b := by intro h'; exact hu (hr.trans h')
    simp only [joinPotential, hu, hv, ite_false]
    exact hdu

/-- The potential is one-Lipschitz on the actual merged graph, including its new edge. -/
theorem joinPotential_le_of_join_adj (F : RootedForest V) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) {u v : V}
    (h : (F.join a b ha hb hab).graph.Adj u v) :
    F.joinPotential b v ≤ F.joinPotential b u + 1 := by
  rw [F.join_graph ha hb hab] at h
  rcases h with h | h
  · exact F.joinPotential_le_of_old_adj b h
  · have hra := (mem_roots.mp ha).2
    have hrb := (mem_roots.mp hb).2
    have hda : F.depth a = 0 := (F.depth_eq_zero_iff (mem_roots.mp ha).1).mpr hra
    have hdb : F.depth b = 0 := (F.depth_eq_zero_iff (mem_roots.mp hb).1).mpr hrb
    rcases (SimpleGraph.edge_adj a b u v).mp h with ⟨h | h, _⟩
    · rcases h with ⟨rfl, rfl⟩
      simp [joinPotential, hra, hrb, hda, hdb, hab]
    · rcases h with ⟨rfl, rfl⟩
      simp [joinPotential, hra, hrb, hda, hdb, hab]

/-- At the merge of the two tracked components, distance is exactly the sum
of their new depths. This supplies the first-coalescence geometric identity. -/
theorem join_dist_eq_depth_add_depth (F : RootedForest V) {a b u v : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b)
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    (hua : F.root u = a) (hvb : F.root v = b) :
    (F.join a b ha hb hab).graph.dist u v =
      (F.join a b ha hb hab).depth u + (F.join a b ha hb hab).depth v := by
  let J := F.join a b ha hb hab
  have hju : u ∈ J.vertices := hu
  have hjv : v ∈ J.vertices := hv
  have hroot : J.root u = J.root v := by simp [J, join, hua, hvb, hab]
  apply le_antisymm (J.dist_le_depth_add_depth hju hjv hroot)
  obtain ⟨q, hq⟩ := ((J.root_eq_iff_reachable hju hjv).mp hroot).exists_walk_length_eq_dist
  have hpot := potential_le_add_length (G := J.graph) (F.joinPotential b)
    (fun {_ _} h => F.joinPotential_le_of_join_adj ha hb hab h) q.reverse
  simp only [SimpleGraph.Walk.length_reverse, hq, joinPotential, hua, hvb, hab,
    ite_false, ite_true] at hpot
  have hlow : F.depth u + F.depth v + 1 ≤ J.graph.dist u v := by
    exact_mod_cast (show (F.depth u : ℤ) + (F.depth v : ℤ) + 1 ≤ (J.graph.dist u v : ℤ) by omega)
  simpa only [J, join_depth, hua, hvb, hab, ite_false, ite_true, Nat.add_zero, Nat.add_assoc] using hlow

/-- Every ordered merge choice, including its identity fallback, preserves old edges. -/
theorem graph_le_joinChoice (F : RootedForest V) (p : V × V) :
    F.graph ≤ (F.joinChoice p).graph := by
  by_cases hp : p ∈ F.roots.offDiag
  · simp only [joinChoice, dite_eq_left hp]
    exact F.graph_le_join _ _ _
  · simp only [joinChoice, dite_eq_right hp, le_refl]

theorem joinChoice_isAcyclic (F : RootedForest V) (hF : F.graph.IsAcyclic) (p : V × V) :
    (F.joinChoice p).graph.IsAcyclic := by
  by_cases hp : p ∈ F.roots.offDiag
  · simp only [joinChoice, dite_eq_left hp]
    exact F.join_isAcyclic hF _ _ _
  · simpa only [joinChoice, dite_eq_right hp] using hF

/-- Actual ordered choices preserve distance inside each old component. -/
theorem joinChoice_preserves_dist (F : RootedForest V) (hF : F.graph.IsAcyclic)
    (p : V × V) {u v : V} (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    (hroot : F.root u = F.root v) :
    (F.joinChoice p).graph.dist u v = F.graph.dist u v :=
  dist_eq_of_le_isAcyclic (F.graph_le_joinChoice p) (F.joinChoice_isAcyclic hF p)
    ((F.root_eq_iff_reachable hu hv).mp hroot)

/-- If this ordered choice first coalesces the tracked components, their new
common root lies on the path joining them, as certified by the distance identity. -/
theorem joinChoice_new_coalescence_dist (F : RootedForest V) {p : V × V}
    (hp : p ∈ F.roots.offDiag) {u v : V}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v)
    (heq : (F.joinChoice p).root u = (F.joinChoice p).root v) :
    (F.joinChoice p).graph.dist u v = (F.joinChoice p).depth u + (F.joinChoice p).depth v := by
  rcases (F.joinChoice_root_eq_iff huv hp).mp heq with rfl | rfl
  · simp only [joinChoice, dite_eq_left hp]
    exact F.join_dist_eq_depth_add_depth _ _ _ hu hv rfl rfl
  · simp only [joinChoice, dite_eq_left hp]
    rw [SimpleGraph.dist_comm, Nat.add_comm]
    exact F.join_dist_eq_depth_add_depth _ _ _ hv hu rfl rfl

end Freezing1.RootedForest
