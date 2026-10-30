module

public import Freezing1.ForwardVertexDegree

/-!
# Local convergence is exactly finiteness of all limiting degrees

This is a deterministic statement about valid growing forward histories.
It includes held steps after absorption and does not assume that vertices
freeze. A record which never freezes already has a constant displayed label.
-/

@[expose] public section

namespace Freezing1.ForwardInfiniteHistory

open Forward Filter MeasureTheory
open scoped Topology Classical

set_option backward.isDefEq.respectTransparency false

theorem heightVertices_monotone {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    (h : ℕ) : Monotone (fun n => heightVertices (H n) h) := by
  intro a b hab v hm
  obtain ⟨hm, hh⟩ := Finset.mem_filter.mp hm
  exact Finset.mem_filter.mpr ⟨vertices_mono hl hab hm,
    by rw [old_height_eq hv hl hm b hab]; exact hh⟩

theorem heightVertices_zero {n : ℕ} {s : State} (hs : ValidAt n s) :
    heightVertices s 0 = {0} := by
  ext r
  simp only [heightVertices, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hh⟩
    have hz : s.graph.dist 0 r = 0 := by rw [← hs.height_eq_dist r hr]; omega
    exact ((hs.reachable r hr).dist_eq_zero_iff.mp hz).symm
  · rintro rfl
    exact ⟨hs.root_mem, by rw [hs.height_root]⟩

theorem all_heightVertices_stabilize_of_degree_bounded {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    (hd : ∀ r, ∃ d, ∀ n, vertexDegree (H n) r ≤ d) :
    ∀ h, ∃ a, ∀ n ≥ a, heightVertices (H n) h = heightVertices (H a) h := by
  intro h
  induction h with
  | zero => exact ⟨0, fun n _ => (heightVertices_zero (hv n)).trans
      (heightVertices_zero (hv 0)).symm⟩
  | succ h ih =>
    obtain ⟨a, ha⟩ := ih
    have hs : ∀ r ∈ heightVertices (H a) h,
        ∃ b, ∀ n ≥ b, vertexNeighbors (H n) r = vertexNeighbors (H b) r :=
      fun r _ => neighbors_stabilize_of_degree_bounded hl r (hd r)
    choose b hb using hs
    let M := max a ((heightVertices (H a) h).attach.sup fun r => b r.val r.property)
    have haM : a ≤ M := le_max_left _ _
    have hMb : ∀ r (hr : r ∈ heightVertices (H a) h), b r hr ≤ M := by
      intro r hr
      exact (Finset.le_sup (f := fun q => b q.val q.property)
        (Finset.mem_attach _ ⟨r, hr⟩)).trans (le_max_right _ _)
    refine ⟨M, fun n hn => ?_⟩
    apply Finset.Subset.antisymm
    · intro v hvm
      obtain ⟨hvn, hvh⟩ := Finset.mem_filter.mp hvm
      by_cases hv0 : v = 0
      · subst v
        exact Finset.mem_filter.mpr ⟨(hv M).root_mem, by rw [(hv M).height_root]; omega⟩
      · have hpv := (hv n).parent_mem v hvn
        have hph := (hv n).height_parent v hvn hv0
        have hpn : (H n).parent v ∈ heightVertices (H n) h :=
          Finset.mem_filter.mpr ⟨hpv, by omega⟩
        have hpa : (H n).parent v ∈ heightVertices (H a) h := by
          rw [← ha n (haM.trans hn)]
          exact hpn
        have hNb := hb ((H n).parent v) hpa n ((hMb _ hpa).trans hn)
        have hNM := hb ((H n).parent v) hpa M (hMb _ hpa)
        have hneigh : v ∈ vertexNeighbors (H M) ((H n).parent v) := by
          rw [hNM, ← hNb]
          exact Finset.mem_filter.mpr ⟨hvn, (hv n).parent_adj v hvn hv0⟩
        have hMv := (Finset.mem_filter.mp hneigh).1
        exact Finset.mem_filter.mpr ⟨hMv, by
          rwa [old_height_eq hv hl hMv n hn] at hvh⟩
    · exact heightVertices_monotone hv hl (h + 1) hn

theorem all_localBalls_stabilize_of_degree_bounded {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    (hd : ∀ r, ∃ d, ∀ n, vertexDegree (H n) r ≤ d) :
    ∀ h, ∃ a, ∀ n ≥ a, localBall (H n) h = localBall (H a) h := by
  intro h
  obtain ⟨a, ha⟩ := all_heightVertices_stabilize_of_degree_bounded hv hl hd h
  have hs : ∀ r ∈ heightVertices (H a) h,
      ∃ b ≥ a, ∀ n ≥ b, localRecord (H n) r = localRecord (H b) r := by
    intro r hr
    exact old_record_eventually_constant hv hl (Finset.mem_filter.mp hr).1
  choose b hba hb using hs
  let M := max a ((heightVertices (H a) h).attach.sup fun r => b r.val r.property)
  have haM : a ≤ M := le_max_left _ _
  have hMb : ∀ r (hr : r ∈ heightVertices (H a) h), b r hr ≤ M := by
    intro r hr
    exact (Finset.le_sup (f := fun q => b q.val q.property)
      (Finset.mem_attach _ ⟨r, hr⟩)).trans (le_max_right _ _)
  refine ⟨M, fun n hn => ?_⟩
  rw [localBall_eq_image, localBall_eq_image]
  change (heightVertices (H n) h).image _ = (heightVertices (H M) h).image _
  rw [ha n (haM.trans hn), ha M haM]
  apply Finset.image_congr
  intro r hr
  exact (hb r hr n ((hMb r hr).trans hn)).trans (hb r hr M (hMb r hr)).symm

theorem exists_local_limit_of_degree_bounded {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    (hd : ∀ r, ∃ d, ∀ n, vertexDegree (H n) r ≤ d) :
    ∃ t : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t) := by
  apply LocalTree.exists_limit_of_balls_stabilize
  intro h
  obtain ⟨a, ha⟩ := all_localBalls_stabilize_of_degree_bounded hv hl hd h
  exact ⟨a, fun n hn => by
    simpa only [(hv n).localTreeOfState_balls, (hv a).localTreeOfState_balls] using ha n hn⟩

theorem degree_bounded_of_exists_local_limit {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    (hc : ∃ t : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)) :
    ∀ r, ∃ d, ∀ n, vertexDegree (H n) r ≤ d := by
  intro r
  by_cases he : ∃ b, r ∈ (H b).vertices
  · obtain ⟨b, hrb⟩ := he
    obtain ⟨t, ht⟩ := hc
    let h := (H b).height r + 1
    obtain ⟨a, ha⟩ := eventually_atTop.mp ((LocalTree.tendsto_iff_balls _ _).mp ht h)
    let M := max a b
    have hball : ∀ n ≥ M, localBall (H n) h = localBall (H M) h := by
      intro n hn
      have han := ha n ((le_max_left a b).trans hn)
      have haM := ha M (le_max_left _ _)
      simpa only [(hv n).localTreeOfState_balls, (hv M).localTreeOfState_balls]
        using han.trans haM.symm
    refine ⟨(localBall (H M) h).card, fun n => ?_⟩
    have hbound : ∀ k ≥ M, vertexDegree (H k) r ≤ (localBall (H M) h).card := by
      intro k hk
      have hrk := vertices_mono hl ((le_max_right a b).trans hk) hrb
      have hheight := old_height_eq hv hl hrb k ((le_max_right a b).trans hk)
      have hsub : vertexNeighbors (H k) r ⊆ (localBall (H M) h).image
          LocalTree.VertexRecord.birth := by
        intro v hvm
        obtain ⟨hvk, hadj⟩ := Finset.mem_filter.mp hvm
        have hvh : (H k).height v ≤ h := by
          have hh := (hv k).adj_height hadj
          dsimp only [h]
          omega
        apply Finset.mem_image.mpr
        refine ⟨localRecord (H k) v, ?_, rfl⟩
        rw [← hball k hk]
        exact (localRecord_mem_ball_iff _ _ _).mpr ⟨hvk, hvh⟩
      exact (Finset.card_le_card hsub).trans (Finset.card_image_le)
    exact (vertexDegree_monotone hl r (Nat.le_max_left n M)).trans
      (hbound (max n M) (Nat.le_max_right n M))
  · refine ⟨0, fun n => ?_⟩
    have heq : vertexNeighbors (H n) r = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hm
      exact he ⟨n, ((hv n).adj_mem (Finset.mem_filter.mp hm).2).1⟩
    simp only [vertexDegree, heq, Finset.card_empty, le_refl]

theorem exists_local_limit_iff_degree_bounded {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1))) :
    (∃ t : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)) ↔
      ∀ r, ∃ d, ∀ n, vertexDegree (H n) r ≤ d :=
  ⟨degree_bounded_of_exists_local_limit hv hl, exists_local_limit_of_degree_bounded hv hl⟩

theorem degree_bounded_iff_all_occurring_degrees_stabilize {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1))) :
    (∀ r, ∃ d, ∀ n, vertexDegree (H n) r ≤ d) ↔
      ∀ r b, r ∈ (H b).vertices →
        ∃ a, ∀ n ≥ a, vertexDegree (H n) r = vertexDegree (H a) r := by
  constructor
  · intro hd r b _
    obtain ⟨a, ha⟩ := neighbors_stabilize_of_degree_bounded hl r (hd r)
    exact ⟨a, fun n hn => congrArg Finset.card (ha n hn)⟩
  · intro hd r
    by_cases he : ∃ b, r ∈ (H b).vertices
    · obtain ⟨b, hr⟩ := he
      obtain ⟨a, ha⟩ := hd r b hr
      refine ⟨vertexDegree (H a) r, fun n => ?_⟩
      calc
        _ ≤ vertexDegree (H (max n a)) r := vertexDegree_monotone hl r (le_max_left _ _)
        _ = _ := ha _ (le_max_right _ _)
    · refine ⟨0, fun n => ?_⟩
      have heq : vertexNeighbors (H n) r = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hm
        exact he ⟨n, ((hv n).adj_mem (Finset.mem_filter.mp hm).2).1⟩
      simp only [vertexDegree, heq, Finset.card_empty, le_refl]

/-- The paper's first degree/local-equivalence assertion, with all occurring
vertices and the root, for every valid legal trajectory, not merely a.s. -/
theorem exists_local_limit_iff_all_degrees_stabilize {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1))) :
    (∃ t : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)) ↔
      ∀ r b, r ∈ (H b).vertices →
        ∃ a, ∀ n ≥ a, vertexDegree (H n) r = vertexDegree (H a) r :=
  (exists_local_limit_iff_degree_bounded hv hl).trans
    (degree_bounded_iff_all_occurring_degrees_stabilize hv hl)

theorem fullLaw_local_limit_iff_all_degrees_stabilize (x : SignSequence) :
    ∀ᵐ H ∂fullLaw x,
      (∃ t : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)) ↔
        ∀ r b, r ∈ (H b).vertices →
          ∃ a, ∀ n ≥ a, vertexDegree (H n) r = vertexDegree (H a) r := by
  filter_upwards [fullLaw_valid x, fullLaw_legalOrHeld x] with H hv hl
  exact exists_local_limit_iff_all_degrees_stabilize hv hl

end Freezing1.ForwardInfiniteHistory
