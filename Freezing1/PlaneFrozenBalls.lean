module

public import Freezing1.PlaneStateUpdates
public import Freezing1.PlaneTreeLocalTopology

/-!
# Frozen finite balls persist under actual plane-tree updates
-/

@[expose] public section

namespace Freezing1.PlaneForward

open PlaneTree
open scoped Classical

def heightVertices (s : State) (h : ℕ) : Finset Address :=
  s.vertices.filter (fun u => u.length ≤ h)

def FrozenBall (s : State) (h : ℕ) : Prop :=
  ∀ u ∈ s.vertices, u.length ≤ h → u ∉ s.active

theorem Valid.ball_shape {s : State} (hs : Valid s) (h : ℕ) :
    PlaneTree.ball (shape s) h = heightVertices s h := by
  ext u
  rw [heightVertices, PlaneTree.mem_ball, Finset.mem_filter, ← hs.mem_vertices_iff_present]

theorem FrozenBall.active_length {s : State} {h : ℕ} (hf : FrozenBall s h)
    (hs : Valid s) {u : Address} (hu : u ∈ s.active) : h < u.length := by
  by_contra hn
  exact hf u (hs.active_subset hu) (by omega) hu

theorem heightVertices_attach_of_frozen {s : State} {h : ℕ} (hs : Valid s)
    (hf : FrozenBall s h) {u : Address} (hu : u ∈ s.active) {q : ℕ} (hq : q ≤ h + 1) :
    heightVertices (attach s u) q = heightVertices s q := by
  have hlen : q < (newChild s u).length := by
    have hp := hf.active_length hs hu
    simp only [newChild, List.length_append, List.length_singleton]
    omega
  change (insert (newChild s u) s.vertices).filter (fun v => v.length ≤ q) = _
  rw [Finset.filter_insert, ite_eq_right (by omega)]
  rfl

theorem heightVertices_freeze (s : State) (u : Address) (h : ℕ) :
    heightVertices (freeze s u) h = heightVertices s h := rfl

theorem FrozenBall.attach {s : State} {h : ℕ} (hf : FrozenBall s h) (hs : Valid s)
    {u : Address} (hu : u ∈ s.active) : FrozenBall (PlaneForward.attach s u) h := by
  have hparent := hf.active_length hs hu
  intro v hv hlen ha
  have hnewlen : h < (newChild s u).length := by
    simp only [newChild, List.length_append, List.length_singleton]
    omega
  have hvne : v ≠ newChild s u := by intro he; subst v; omega
  have hvold : v ∈ s.vertices := (Finset.mem_insert.mp hv).resolve_left hvne
  have haold : v ∈ s.active := (Finset.mem_insert.mp ha).resolve_left hvne
  exact hf v hvold hlen haold

theorem FrozenBall.freeze {s : State} {h : ℕ} (hf : FrozenBall s h) (u : Address) :
    FrozenBall (PlaneForward.freeze s u) h := by
  intro v hv hlen ha
  exact hf v hv hlen (Finset.mem_of_mem_erase ha)

theorem FrozenBall.step {s : State} {h : ℕ} (hf : FrozenBall s h) (hs : Valid s)
    (sign : Bool) (u : Address) : FrozenBall (PlaneForward.step s sign u) h := by
  by_cases hu : u ∈ s.active
  · rw [PlaneForward.step, ite_eq_left hu]
    cases sign
    · exact hf.freeze u
    · exact hf.attach hs hu
  · rw [PlaneForward.step, ite_eq_right hu]
    exact hf

theorem ball_shape_step_of_frozen {s : State} {h : ℕ} (hs : Valid s)
    (hf : FrozenBall s h) (sign : Bool) (u : Address) :
    PlaneTree.ball (shape (step s sign u)) h = PlaneTree.ball (shape s) h := by
  rw [(hs.step sign u).ball_shape, hs.ball_shape]
  by_cases hu : u ∈ s.active
  · rw [step, ite_eq_left hu]
    cases sign
    · exact heightVertices_freeze s u h
    · exact heightVertices_attach_of_frozen hs hf hu (Nat.le_succ h)
  · rw [step, ite_eq_right hu]

end Freezing1.PlaneForward
