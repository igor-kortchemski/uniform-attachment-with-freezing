module

public import Freezing1.ForwardLocalTree
public import Freezing1.ForwardSupportCharacterization
public import Freezing1.CanonicalTreeObservable

/-!
# The graph and labels encoded by a local ball

On the actual history support, the graph recovered from the finite records
is exactly the induced radius ball. Vertex labels are retained verbatim;
the birth ID of each child is its incoming edge's actual timestamp.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped Classical

namespace LocalTree

def ballGraph (B : Ball) : SimpleGraph ℕ where
  Adj u v := u ≠ v ∧ ∃ r ∈ B, ∃ q ∈ B, r.birth = u ∧ q.birth = v ∧
    ((r.birth ≠ 0 ∧ r.parent = q.birth) ∨ (q.birth ≠ 0 ∧ q.parent = r.birth))
  symm := by
    constructor
    intro u v huv
    obtain ⟨hne, r, hr, q, hq, hu, hv, hp⟩ := huv
    exact ⟨hne.symm, q, hq, r, hr, hv, hu, hp.symm⟩
  loopless := by
    constructor
    intro u hu
    exact hu.1 rfl

end LocalTree

namespace Forward

theorem HistoryShape.localBall_graph {x : SignSequence} {n : ℕ} {s : State}
    (hs : HistoryShape x n s) (h u v : ℕ) :
    (LocalTree.ballGraph (localBall s h)).Adj u v ↔
      s.graph.Adj u v ∧ s.height u ≤ h ∧ s.height v ≤ h := by
  constructor
  · rintro ⟨hne, r, hr, q, hq, hu, hv, hp⟩
    obtain ⟨i, hi, rfl, hih⟩ := (mem_localBall_iff s h r).mp hr
    obtain ⟨j, hj, rfl, hjh⟩ := (mem_localBall_iff s h q).mp hq
    change i = u at hu
    change j = v at hv
    subst i
    subst j
    refine ⟨(hs.graph_iff u v).mpr ⟨hi, hj, ?_⟩, hih, hjh⟩
    rcases hp with hp | hp
    · have hu0 : u ≠ 0 := hp.1
      exact Or.inl ⟨hu0, by simpa [localRecord, hu0] using hp.2⟩
    · have hv0 : v ≠ 0 := hp.1
      exact Or.inr ⟨hv0, by simpa [localRecord, hv0] using hp.2⟩
  · rintro ⟨hadj, huh, hvh⟩
    obtain ⟨hu, hv, hp⟩ := (hs.graph_iff u v).mp hadj
    refine ⟨hadj.ne, localRecord s u, (localRecord_mem_ball_iff s h u).mpr ⟨hu, huh⟩,
      localRecord s v, (localRecord_mem_ball_iff s h v).mpr ⟨hv, hvh⟩, rfl, rfl, ?_⟩
    rcases hp with hp | hp
    · exact Or.inl ⟨hp.1, by simpa [localRecord, hp.1] using hp.2⟩
    · exact Or.inr ⟨hp.1, by simpa [localRecord, hp.1] using hp.2⟩

theorem HistoryShape.localBall_graph_distance {x : SignSequence} {n : ℕ} {s : State}
    (hs : HistoryShape x n s) (h u v : ℕ) :
    (LocalTree.ballGraph (localBall s h)).Adj u v ↔
      s.graph.Adj u v ∧ s.graph.dist 0 u ≤ h ∧ s.graph.dist 0 v ≤ h := by
  rw [hs.localBall_graph]
  constructor <;> rintro ⟨hadj, hu, hv⟩
  · exact ⟨hadj, by rwa [← hs.hasHistory.current.valid.height_eq_dist u
      ((hs.graph_iff u v).mp hadj).1], by rwa [← hs.hasHistory.current.valid.height_eq_dist v
      ((hs.graph_iff u v).mp hadj).2.1]⟩
  · exact ⟨hadj, by rwa [hs.hasHistory.current.valid.height_eq_dist u
      ((hs.graph_iff u v).mp hadj).1], by rwa [hs.hasHistory.current.valid.height_eq_dist v
      ((hs.graph_iff u v).mp hadj).2.1]⟩

theorem localRecord_frozen_label (s : State) (v : ℕ) :
    (localRecord s v).frozenAt = s.frozenAt v := rfl

theorem ValidAt.localRecord_edge_timestamp {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) (hv0 : v ≠ 0) :
    CanonicalTree.edgeTime (localRecord s v).parent (localRecord s v).birth = v := by
  simpa only [localRecord, ite_eq_right hv0] using CanonicalTree.forward_edge_time hs hv hv0

theorem treeLaw_localBall_graph_distance (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂treeLaw x n, ∀ h u v,
      (LocalTree.ballGraph (localBall s h)).Adj u v ↔
        s.graph.Adj u v ∧ s.graph.dist 0 u ≤ h ∧ s.graph.dist 0 v ≤ h :=
  (treeLaw_historyShape x n hn).mono fun _ hs => hs.localBall_graph_distance

end Forward
end Freezing1
