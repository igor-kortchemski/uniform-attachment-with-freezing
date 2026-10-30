module

public import Freezing1.ForwardLocalLimit
public import Freezing1.ForwardPrefixGeometry
public import Freezing1.ForwardDegreeMonotonicity

/-!
# Degrees and persistent data of every forward vertex

The degree counts actual graph neighbours, including the parent of a nonroot
vertex. The results below hold for every valid legal-or-held trajectory,
including absorption. No eventual-freezing hypothesis is used for degree
monotonicity or for stabilization of the displayed record of an old vertex.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology Classical

set_option backward.isDefEq.respectTransparency false

namespace Forward

noncomputable def vertexNeighbors (s : State) (r : ℕ) : Finset ℕ :=
  s.vertices.filter fun v => s.graph.Adj r v

noncomputable def vertexDegree (s : State) (r : ℕ) : ℕ :=
  (vertexNeighbors s r).card

theorem vertexDegree_root (s : State) : vertexDegree s 0 = rootDegree s := rfl

theorem vertexNeighbors_attach_old {n : ℕ} {s : State} (hs : ValidAt n s)
    {r : ℕ} (hr : r ≤ n) (p : ℕ) :
    vertexNeighbors (attach s (n + 1) p) r =
      if p = r then insert (n + 1) (vertexNeighbors s r) else vertexNeighbors s r := by
  have hfresh : n + 1 ∉ s.vertices := by intro h; have := hs.vertices_le _ h; omega
  have hrnew : r ≠ n + 1 := by omega
  have hnotadj : ¬s.graph.Adj r (n + 1) := fun h => hfresh (hs.adj_mem h).2
  ext v
  by_cases hp : p = r <;> by_cases hv : v = n + 1
  · subst p v
    simp [vertexNeighbors, attach, SimpleGraph.edge_adj, hnotadj, hrnew]
  · subst p
    simp [vertexNeighbors, attach, SimpleGraph.edge_adj, hv, hrnew]
  · subst v
    simp [vertexNeighbors, attach, SimpleGraph.edge_adj, hp, Ne.symm hp, hnotadj,
      hfresh, hrnew]
  · simp [vertexNeighbors, attach, SimpleGraph.edge_adj, hp, hv, hrnew]

theorem vertexDegree_attach_old {n : ℕ} {s : State} (hs : ValidAt n s)
    {r : ℕ} (hr : r ≤ n) (p : ℕ) :
    vertexDegree (attach s (n + 1) p) r = vertexDegree s r + if p = r then 1 else 0 := by
  have hfresh : n + 1 ∉ vertexNeighbors s r := by
    intro h
    have := hs.vertices_le _ (Finset.mem_filter.mp h).1
    omega
  rw [vertexDegree, vertexNeighbors_attach_old hs hr p]
  by_cases hp : p = r <;> simp [hp, vertexDegree, Finset.card_insert_of_notMem hfresh]

theorem vertexDegree_freeze (s : State) (t p r : ℕ) :
    vertexDegree (freeze s t p) r = vertexDegree s r := rfl

theorem vertexDegree_step_old {n : ℕ} {s : State} (hs : ValidAt n s)
    {r : ℕ} (hr : r ≤ n) {p : ℕ} (hp : p ∈ s.active) (sign : Bool) :
    vertexDegree (step s (n + 1) sign p) r =
      vertexDegree s r + if sign = true ∧ p = r then 1 else 0 := by
  rw [step, ite_eq_left hp]
  cases sign <;> simp [vertexDegree_freeze, vertexDegree_attach_old hs hr p]

end Forward

namespace ForwardInfiniteHistory

open Forward

theorem LegalOrHeld.graph_le {x : SignSequence} {n : ℕ} {s q : State}
    (hl : LegalOrHeld x n s q) : s.graph ≤ q.graph := by
  rcases hl with ⟨_, rfl⟩ | ⟨p, hp, rfl⟩
  · exact le_rfl
  · exact graph_le_step _ _ _ _

theorem LegalOrHeld.vertexNeighbors_subset {x : SignSequence} {n : ℕ} {s q : State}
    (hl : LegalOrHeld x n s q) (r : ℕ) : vertexNeighbors s r ⊆ vertexNeighbors q r := by
  intro v hv
  obtain ⟨hv, hadj⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hl.vertices_mono hv, hl.graph_le hadj⟩

theorem vertexNeighbors_monotone {x : SignSequence} {H : History}
    (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1))) (r : ℕ) :
    Monotone (fun n => vertexNeighbors (H n) r) :=
  monotone_nat_of_le_succ fun n => (hl n).vertexNeighbors_subset r

theorem vertexDegree_monotone {x : SignSequence} {H : History}
    (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1))) (r : ℕ) :
    Monotone (fun n => vertexDegree (H n) r) :=
  fun _ _ hab => Finset.card_le_card (vertexNeighbors_monotone hl r hab)

theorem vertices_mono {x : SignSequence} {H : History}
    (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1))) :
    Monotone (fun n => (H n).vertices) :=
  monotone_nat_of_le_succ fun n => (hl n).vertices_mono

theorem old_height_eq {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    {a r : ℕ} (hr : r ∈ (H a).vertices) :
    ∀ n ≥ a, (H n).height r = (H a).height r := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    exact ((legalOrHeld_old_geometry (hv n) (hl n)).2.1 r
      (vertices_mono hl hn hr)).trans ih

theorem LegalOrHeld.parent_old {x : SignSequence} {n : ℕ} {s q : State}
    (hl : LegalOrHeld x n s q) (hs : ValidAt n s) {r : ℕ} (hr : r ∈ s.vertices) :
    q.parent r = s.parent r := by
  have hnew : r ≠ n + 1 := by have := hs.vertices_le r hr; omega
  rcases hl with ⟨_, rfl⟩ | ⟨p, hp, rfl⟩
  · rfl
  · rw [step, ite_eq_left hp]
    cases hx : x (n + 1) <;> simp [attach, freeze, hnew]

theorem old_parent_eq {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    {a r : ℕ} (hr : r ∈ (H a).vertices) :
    ∀ n ≥ a, (H n).parent r = (H a).parent r := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    exact ((hl n).parent_old (hv n) (vertices_mono hl hn hr)).trans ih

/-- A label changes at most once. This assertion does not require that its
vertex ever freezes. -/
theorem old_record_eventually_constant {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    {a r : ℕ} (hr : r ∈ (H a).vertices) :
    ∃ b ≥ a, ∀ n ≥ b, localRecord (H n) r = localRecord (H b) r := by
  have hf : ∃ b ≥ a, ∀ n ≥ b, (H n).frozenAt r = (H b).frozenAt r := by
    by_cases he : ∃ b ≥ a, ∃ j, (H b).frozenAt r = some j
    · obtain ⟨b, hab, j, hj⟩ := he
      exact ⟨b, hab, fun n hn => (frozenAt_persists hv hl
        (vertices_mono hl hab hr) hj n hn).trans hj.symm⟩
    · refine ⟨a, le_rfl, fun n hn => ?_⟩
      have hz : ∀ k ≥ a, (H k).frozenAt r = none := by
        intro k hk
        cases heq : (H k).frozenAt r with
        | none => rfl
        | some j => exact (he ⟨k, hk, j, heq⟩).elim
      rw [hz n hn, hz a le_rfl]
  obtain ⟨b, hab, hb⟩ := hf
  refine ⟨b, hab, fun n hn => ?_⟩
  have hp := old_parent_eq hv hl hr n (hab.trans hn)
  have hpb := old_parent_eq hv hl hr b hab
  have hh := old_height_eq hv hl hr n (hab.trans hn)
  have hhb := old_height_eq hv hl hr b hab
  simp only [localRecord, hp, hpb, hh, hhb, hb n hn]

theorem degree_constant_after_freezing {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    {a r j : ℕ} (hr : r ∈ (H a).vertices) (hf : (H a).frozenAt r = some j) :
    ∀ n ≥ a, vertexDegree (H n) r = vertexDegree (H a) r := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hmem := vertices_mono hl hn hr
    have hfrozen := frozenAt_persists hv hl hr hf n hn
    have hnot : r ∉ (H n).active := by
      intro ha
      have he := ((hv n).active_iff r hmem).mp ha
      rw [hfrozen] at he
      contradiction
    rcases hl n with ⟨_, he⟩ | ⟨p, hp, he⟩
    · simpa only [he] using ih
    · rw [he, vertexDegree_step_old (hv n) ((hv n).vertices_le r hmem) hp]
      have hpr : p ≠ r := fun he => hnot (he ▸ hp)
      simpa [hpr] using ih

/-- A monotone sequence of actual neighbour sets stabilizes as soon as its
finite cardinalities are bounded. -/
theorem neighbors_stabilize_of_degree_bounded {x : SignSequence} {H : History}
    (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1))) (r : ℕ)
    (hb : ∃ d, ∀ n, vertexDegree (H n) r ≤ d) :
    ∃ a, ∀ n ≥ a, vertexNeighbors (H n) r = vertexNeighbors (H a) r := by
  obtain ⟨d, hd⟩ := hb
  let f := fun n => vertexDegree (H n) r
  have hfin : (Set.range f).Finite :=
    (Set.finite_Iic d).subset (by rintro _ ⟨n, rfl⟩; exact hd n)
  obtain ⟨a, ha⟩ := (Set.range_nonempty f).csSup_mem hfin
  refine ⟨a, fun n hn => ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le (vertexNeighbors_monotone hl r hn)
  change f n ≤ f a
  rw [ha]
  exact le_csSup hfin.bddAbove (Set.mem_range_self n)

theorem fullLaw_all_vertexDegree_monotone (x : SignSequence) :
    ∀ᵐ H ∂fullLaw x, ∀ r, Monotone (fun n => vertexDegree (H n) r) :=
  (fullLaw_legalOrHeld x).mono fun _ hl r => vertexDegree_monotone hl r

end ForwardInfiniteHistory
end Freezing1
