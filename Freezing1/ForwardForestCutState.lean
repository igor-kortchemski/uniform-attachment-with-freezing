module

public import Freezing1.ForwardCutUpdates
public import Freezing1.ForwardHistorySupport

/-!
# The complete actual forward forest after a cut

The retained old vertices are the roots active at the cut. Their parent
edges and old heights are erased, while their later freezing times remain.
The active set is the genuine active set, so a marked root that later freezes
is retained as a forest vertex without being counted as genuinely active.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

set_option backward.isDefEq.respectTransparency false

def forestInitial (roots : Finset ℕ) : State where
  vertices := roots
  active := roots
  graph := ⊥
  parent := id
  height := fun _ => 0
  frozenAt := fun _ => none

noncomputable def forestCut (s : State) (a : ℕ) : State where
  vertices := cutVertices s a
  active := s.active
  graph := cutGraph s a
  parent v := if v ∈ cutVertices s a then if v ≤ a then v else s.parent v else v
  height v := if v ∈ cutVertices s a then cutHeight s a v else 0
  frozenAt v := if v ∈ cutVertices s a then s.frozenAt v else none

theorem active_subset_cutVertices {n : ℕ} {s : State} (hs : ValidAt n s) (a : ℕ) :
    s.active ⊆ cutVertices s a := by
  intro v hv
  have hvV := hs.active_subset hv
  have hn := (hs.active_iff v hvV).mp hv
  simp [cutVertices, hvV, hn]

theorem cutVertices_attach {n : ℕ} {s : State} (_hs : ValidAt n s) (a p : ℕ) :
    cutVertices (attach s (n + 1) p) a = insert (n + 1) (cutVertices s a) := by
  ext v
  by_cases hv : v = n + 1
  · subst v
    simp [cutVertices, attach]
  · simp [cutVertices, attach, hv]

theorem cutVertices_freeze {n : ℕ} {s : State} (hs : ValidAt n s)
    {a p : ℕ} (ha : a ≤ n) (hp : p ∈ s.active) :
    cutVertices (freeze s (n + 1) p) a = cutVertices s a := by
  have hpV := hs.active_subset hp
  have hnone := (hs.active_iff p hpV).mp hp
  ext v
  by_cases hv : v = p
  · subst v
    simp [cutVertices, freeze, hpV, hnone, show a < n + 1 by omega]
  · simp [cutVertices, freeze, hv]

theorem forestCut_attach {n : ℕ} {s : State} (hs : ValidAt n s)
    {a p : ℕ} (ha : a ≤ n) (hp : p ∈ s.active) :
    forestCut (attach s (n + 1) p) a = attach (forestCut s a) (n + 1) p := by
  have hnew : n + 1 ∉ s.vertices := by intro hh; have := hs.vertices_le _ hh; omega
  have hnewC : n + 1 ∉ cutVertices s a := fun hh => hnew (Finset.mem_filter.mp hh).1
  have hpC := active_subset_cutVertices hs a hp
  have hpN : p ≤ n := hs.vertices_le _ (hs.active_subset hp)
  have hpnew : n + 1 ≠ p := by omega
  have hnewa : ¬n + 1 ≤ a := by omega
  have hcut := cutVertices_attach hs a p
  apply State.ext_data
  · exact hcut
  · rfl
  · ext u v
    change (u ∈ cutVertices (attach s (n + 1) p) a ∧
        v ∈ cutVertices (attach s (n + 1) p) a ∧
        (s.graph ⊔ SimpleGraph.edge p (n + 1)).Adj u v ∧ a < max u v) ↔
      ((cutGraph s a) ⊔ SimpleGraph.edge p (n + 1)).Adj u v
    rw [hcut]
    have hleft (w : ℕ) : ¬s.graph.Adj (n + 1) w := fun hh => hnew (hs.adj_mem hh).1
    have hright (w : ℕ) : ¬s.graph.Adj w (n + 1) := fun hh => hnew (hs.adj_mem hh).2
    by_cases hu : u = n + 1
    · subst u
      by_cases hv : v = p
      · subst v
        simp [SimpleGraph.sup_adj, SimpleGraph.edge_adj, cutGraph, hleft, hpC,
          hnewC, show max (n + 1) p = n + 1 from max_eq_left (by omega), show a < n + 1 by omega]
      · simp [SimpleGraph.sup_adj, SimpleGraph.edge_adj, cutGraph, hleft, hnewC, hv, hpnew]
    · by_cases hv : v = n + 1
      · subst v
        by_cases hup : u = p
        · subst u
          simp [SimpleGraph.sup_adj, SimpleGraph.edge_adj, cutGraph, hright, hpC,
            hnewC, show max p (n + 1) = n + 1 from max_eq_right (by omega), show a < n + 1 by omega]
        · simp [SimpleGraph.sup_adj, SimpleGraph.edge_adj, cutGraph, hright, hnewC, hup, hpnew, hu]
      · simp [SimpleGraph.sup_adj, SimpleGraph.edge_adj, cutGraph, hu, hv]
  · funext v
    change (if v ∈ cutVertices (attach s (n + 1) p) a then
      if v ≤ a then v else (attach s (n + 1) p).parent v else v) =
      Function.update (fun w => if w ∈ cutVertices s a then if w ≤ a then w else s.parent w else w)
        (n + 1) p v
    rw [hcut]
    by_cases hv : v = n + 1
    · subst v
      simp [attach, hnewa]
    · simp [attach, hv]
  · funext v
    change (if v ∈ cutVertices (attach s (n + 1) p) a then cutHeight (attach s (n + 1) p) a v else 0) =
      Function.update (fun w => if w ∈ cutVertices s a then cutHeight s a w else 0)
        (n + 1) ((if p ∈ cutVertices s a then cutHeight s a p else 0) + 1) v
    rw [hcut]
    by_cases hv : v = n + 1
    · subst v
      simp only [Finset.mem_insert_self, ite_true, Function.update_self]
      rw [cutHeight_attach_new hs ha hp, ite_eq_left hpC]
    · by_cases hvC : v ∈ cutVertices s a
      · have hvV := (Finset.mem_filter.mp hvC).1
        simp only [Finset.mem_insert, hv, false_or, hvC, ite_true,
          Function.update_of_ne hv]
        exact cutHeight_attach_old hs a p hvV
      · simp [hv, hvC]
  · funext v
    change (if v ∈ cutVertices (attach s (n + 1) p) a then (attach s (n + 1) p).frozenAt v else none) =
      Function.update (fun w => if w ∈ cutVertices s a then s.frozenAt w else none) (n + 1) none v
    rw [hcut]
    by_cases hv : v = n + 1
    · subst v
      simp [attach]
    · simp [attach, hv]

theorem forestCut_freeze {n : ℕ} {s : State} (hs : ValidAt n s)
    {a p : ℕ} (ha : a ≤ n) (hp : p ∈ s.active) :
    forestCut (freeze s (n + 1) p) a = freeze (forestCut s a) (n + 1) p := by
  have hc := cutVertices_freeze hs ha hp
  have hpC := active_subset_cutVertices hs a hp
  apply State.ext_data
  · exact hc
  · rfl
  · ext u v
    change (u ∈ cutVertices (freeze s (n + 1) p) a ∧
      v ∈ cutVertices (freeze s (n + 1) p) a ∧ s.graph.Adj u v ∧ a < max u v) ↔ _
    rw [hc]
    rfl
  · funext v
    change (if v ∈ cutVertices (freeze s (n + 1) p) a then
      if v ≤ a then v else s.parent v else v) = _
    rw [hc]
    rfl
  · funext v
    change (if v ∈ cutVertices (freeze s (n + 1) p) a then cutHeight (freeze s (n + 1) p) a v else 0) = _
    rw [hc, cutHeight_freeze]
    rfl
  · funext v
    change (if v ∈ cutVertices (freeze s (n + 1) p) a then (freeze s (n + 1) p).frozenAt v else none) =
      Function.update (fun w => if w ∈ cutVertices s a then s.frozenAt w else none) p (some (n + 1)) v
    rw [hc]
    by_cases hv : v = p
    · subst v
      simp [freeze, hpC]
    · simp [freeze, hv]

theorem forestCut_step {n : ℕ} {s : State} (hs : ValidAt n s)
    {a p : ℕ} (ha : a ≤ n) (hp : p ∈ s.active) (sign : Bool) :
    forestCut (step s (n + 1) sign p) a = step (forestCut s a) (n + 1) sign p := by
  simp only [step, hp, forestCut, ite_true]
  cases sign
  · exact forestCut_freeze hs ha hp
  · exact forestCut_attach hs ha hp

theorem cutVertices_at_cut {n : ℕ} {s : State} (hs : ValidAt n s) (hl : LabelsValidAt n s) :
    cutVertices s n = s.active := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨hvV, htime⟩ := Finset.mem_filter.mp hv
    apply (hs.active_iff v hvV).mpr
    cases hf : s.frozenAt v with
    | none => rfl
    | some t =>
      have hb := (hl.bounded v hvV t hf).2
      have ht := htime t hf
      omega
  · exact active_subset_cutVertices hs n

theorem forestCut_at_cut {n : ℕ} {s : State} (hs : ValidAt n s) (hl : LabelsValidAt n s) :
    forestCut s n = forestInitial s.active := by
  have hc := cutVertices_at_cut hs hl
  apply State.ext_data
  · exact hc
  · rfl
  · ext u v
    change (u ∈ cutVertices s n ∧ v ∈ cutVertices s n ∧ s.graph.Adj u v ∧ n < max u v) ↔ False
    constructor
    · rintro ⟨hu, hv, _, hmax⟩
      have hun := hs.vertices_le u (Finset.mem_filter.mp hu).1
      have hvn := hs.vertices_le v (Finset.mem_filter.mp hv).1
      omega
    · simp
  · funext v
    by_cases hv : v ∈ cutVertices s n
    · have hvn := hs.vertices_le v (Finset.mem_filter.mp hv).1
      simp [forestCut, forestInitial, hv, hvn]
    · simp [forestCut, forestInitial, hv]
  · funext v
    by_cases hv : v ∈ cutVertices s n
    · have hvn := hs.vertices_le v (Finset.mem_filter.mp hv).1
      simp [forestCut, forestInitial, hv, cutHeightAux_eq_zero_of_le s n _ v hvn, cutHeight]
    · simp [forestCut, forestInitial, hv]
  · funext v
    by_cases hv : v ∈ cutVertices s n
    · have hvA : v ∈ s.active := hc ▸ hv
      simp [forestCut, forestInitial, hv, (hs.active_iff v (hs.active_subset hvA)).mp hvA]
    · simp [forestCut, forestInitial, hv]

end Freezing1.Forward
