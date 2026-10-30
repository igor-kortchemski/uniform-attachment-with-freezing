module

public import Freezing1.ForwardInfiniteHistory
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Old heights and pair distances persist along the actual forward history

Appending leaves to a tree preserves every path between old vertices.
This supplies the geometry required when uniform terminal samples are
restricted to a large earlier vertex set.
-/

@[expose] public section

namespace Freezing1

open scoped Classical

theorem acyclic_supergraph_dist_eq {V : Type*} {G K : SimpleGraph V}
    (hK : K.IsAcyclic) (hle : G ≤ K) {u v : V} (hr : G.Reachable u v) :
    G.dist u v = K.dist u v := by
  obtain ⟨p, hp, hpl⟩ := hr.exists_path_of_dist
  obtain ⟨q, hq, hql⟩ := (hr.mono hle).exists_path_of_dist
  have he : p.mapLe hle = q := Subtype.mk.inj
    (hK.subsingleton_path u v |>.elim ⟨p.mapLe hle, hp.mapLe hle⟩ ⟨q, hq⟩)
  have hh := congrArg SimpleGraph.Walk.length he
  simpa only [SimpleGraph.Walk.length_mapLe, hpl, hql] using hh

namespace Forward

theorem vertices_subset_step (s : State) (n : ℕ) (sign : Bool) (p : ℕ) :
    s.vertices ⊆ (step s n sign p).vertices := by
  unfold step
  split_ifs <;> simp [attach, freeze]

theorem graph_le_step (s : State) (n : ℕ) (sign : Bool) (p : ℕ) :
    s.graph ≤ (step s n sign p).graph := by
  unfold step
  split_ifs <;> simp [attach, freeze]

theorem ValidAt.height_step_old {n : ℕ} {s : State} (hs : ValidAt n s)
    (sign : Bool) (p : ℕ) {v : ℕ} (hv : v ∈ s.vertices) :
    (Forward.step s (n + 1) sign p).height v = s.height v := by
  have hne : v ≠ n + 1 := by have hh := hs.vertices_le v hv; omega
  unfold Forward.step
  split_ifs <;> simp [Forward.attach, Forward.freeze, hne]

theorem ValidAt.dist_step_old {n : ℕ} {s : State} (hs : ValidAt n s)
    (sign : Bool) (p : ℕ) {u v : ℕ} (hu : u ∈ s.vertices) (hv : v ∈ s.vertices) :
    (Forward.step s (n + 1) sign p).graph.dist u v = s.graph.dist u v := by
  symm
  exact acyclic_supergraph_dist_eq (hs.step sign p).acyclic (graph_le_step _ _ _ _)
    ((hs.reachable u hu).symm.trans (hs.reachable v hv))

end Forward

namespace ForwardInfiniteHistory

open Forward
open MeasureTheory

theorem legalOrHeld_old_geometry {x : SignSequence} {n : ℕ} {s t : State}
    (hs : ValidAt n s) (hl : LegalOrHeld x n s t) :
    s.vertices ⊆ t.vertices ∧
      (∀ v ∈ s.vertices, t.height v = s.height v) ∧
      (∀ u ∈ s.vertices, ∀ v ∈ s.vertices, t.graph.dist u v = s.graph.dist u v) := by
  rcases hl with ⟨_, rfl⟩ | ⟨p, hp, rfl⟩
  · exact ⟨Finset.Subset.refl _, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  · exact ⟨vertices_subset_step _ _ _ _,
      fun _ hv => hs.height_step_old _ p hv, fun _ hu _ hv => hs.dist_step_old _ p hu hv⟩

theorem history_old_geometry {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    (a k : ℕ) (hak : a ≤ k) :
    (H a).vertices ⊆ (H k).vertices ∧
      (∀ v ∈ (H a).vertices, (H k).height v = (H a).height v) ∧
      (∀ u ∈ (H a).vertices, ∀ v ∈ (H a).vertices,
        (H k).graph.dist u v = (H a).graph.dist u v) := by
  induction k, hak using Nat.le_induction with
  | base => exact ⟨Finset.Subset.refl _, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | succ k hak ih =>
    have hs := legalOrHeld_old_geometry (hv k) (hl k)
    refine ⟨ih.1.trans hs.1, ?_, ?_⟩
    · intro v hv
      exact (hs.2.1 v (ih.1 hv)).trans (ih.2.1 v hv)
    · intro u hu v hv
      exact (hs.2.2 u (ih.1 hu) v (ih.1 hv)).trans (ih.2.2 u hu v hv)

theorem fullLaw_old_geometry (x : SignSequence) (a k : ℕ) (hak : a ≤ k) :
    ∀ᵐ H ∂fullLaw x,
      (H a).vertices ⊆ (H k).vertices ∧
        (∀ v ∈ (H a).vertices, (H k).height v = (H a).height v) ∧
        (∀ u ∈ (H a).vertices, ∀ v ∈ (H a).vertices,
          (H k).graph.dist u v = (H a).graph.dist u v) := by
  filter_upwards [fullLaw_valid x, fullLaw_legalOrHeld x] with H hv hl
  exact history_old_geometry hv hl a k hak

end ForwardInfiniteHistory
end Freezing1
