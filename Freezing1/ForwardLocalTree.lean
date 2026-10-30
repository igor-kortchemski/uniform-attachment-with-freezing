module

public import Freezing1.LocalTreeTopology
public import Freezing1.ForwardLaw
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Actual forward trees in the local space

The finite records preserve every incoming edge timestamp and displayed
vertex label. Their radius is the maintained height, proved equal to graph
distance on the genuine support. A default value outside valid states makes
the map total and has no effect under any forward law.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped Classical

namespace LocalTree

instance : MeasurableSpace Tree := borel Tree
instance : BorelSpace Tree := ⟨rfl⟩

end LocalTree

namespace Forward

def localRecord (s : State) (v : ℕ) : LocalTree.VertexRecord where
  birth := v
  parent := if v = 0 then 0 else s.parent v
  height := s.height v
  frozenAt := s.frozenAt v

theorem localRecord_injective (s : State) : Function.Injective (localRecord s) := by
  intro v w he
  exact congrArg LocalTree.VertexRecord.birth he

def localBall (s : State) (h : ℕ) : LocalTree.Ball :=
  LocalTree.restrict h (s.vertices.image (localRecord s))

theorem mem_localBall_iff (s : State) (h : ℕ) (r : LocalTree.VertexRecord) :
    r ∈ localBall s h ↔ ∃ v ∈ s.vertices, localRecord s v = r ∧ s.height v ≤ h := by
  simp only [localBall, LocalTree.restrict, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hh⟩
    exact ⟨v, hv, rfl, hh⟩
  · rintro ⟨v, hv, rfl, hh⟩
    exact ⟨⟨v, hv, rfl⟩, hh⟩

theorem localRecord_mem_ball_iff (s : State) (h v : ℕ) :
    localRecord s v ∈ localBall s h ↔ v ∈ s.vertices ∧ s.height v ≤ h := by
  rw [mem_localBall_iff]
  constructor
  · rintro ⟨w, hw, he, hh⟩
    have he' := localRecord_injective s he
    subst w
    exact ⟨hw, hh⟩
  · rintro ⟨hv, hh⟩
    exact ⟨v, hv, rfl, hh⟩

/-- Membership is the exact graph-distance ball, restricted to actual vertices. -/
theorem ValidAt.localBall_graph_distance {n : ℕ} {s : State} (hs : ValidAt n s)
    (h v : ℕ) :
    localRecord s v ∈ localBall s h ↔ v ∈ s.vertices ∧ s.graph.dist 0 v ≤ h := by
  rw [localRecord_mem_ball_iff]
  constructor
  · rintro ⟨hv, hh⟩
    exact ⟨hv, by rwa [← hs.height_eq_dist v hv]⟩
  · rintro ⟨hv, hh⟩
    exact ⟨hv, by rwa [hs.height_eq_dist v hv]⟩

theorem ValidAt.localBall_valid {n : ℕ} {s : State} (hs : ValidAt n s) (h : ℕ) :
    LocalTree.ValidBall h (localBall s h) := by
  constructor
  · refine ⟨localRecord s 0, ?_, rfl⟩
    exact (localRecord_mem_ball_iff s h 0).mpr ⟨hs.root_mem, by rw [hs.height_root]; omega⟩
  · intro r hr
    obtain ⟨v, hv, rfl, hh⟩ := (mem_localBall_iff s h r).mp hr
    exact hh
  · intro r hr q hq he
    obtain ⟨v, hv, rfl, hh⟩ := (mem_localBall_iff s h r).mp hr
    obtain ⟨w, hw, rfl, hh'⟩ := (mem_localBall_iff s h q).mp hq
    change v = w at he
    exact congrArg (localRecord s) he
  · intro r hr he
    obtain ⟨v, hv, rfl, hh⟩ := (mem_localBall_iff s h r).mp hr
    change v = 0 at he
    subst v
    simp [localRecord, hs.height_root]
  · intro r hr he
    obtain ⟨v, hv, rfl, hh⟩ := (mem_localBall_iff s h r).mp hr
    change v ≠ 0 at he
    have hp := hs.height_parent v hv he
    refine ⟨localRecord s (s.parent v), ?_, ?_, ?_, hs.parent_lt v hv he⟩
    · exact (localRecord_mem_ball_iff s h (s.parent v)).mpr ⟨hs.parent_mem v hv, by omega⟩
    · simp [localRecord, he]
    · exact hp.symm

theorem restrict_localBall (s : State) {h H : ℕ} (hh : h ≤ H) :
    LocalTree.restrict h (localBall s H) = localBall s h :=
  LocalTree.restrict_restrict _ hh

theorem ValidAt.localBalls_valid {n : ℕ} {s : State} (hs : ValidAt n s) :
    LocalTree.ValidSequence (localBall s) := by
  intro h
  exact ⟨hs.localBall_valid h, restrict_localBall s (Nat.le_succ h)⟩

noncomputable def localTreeOfState (s : State) : LocalTree.Tree :=
  if hs : ∃ n, ValidAt n s then ⟨localBall s, hs.choose_spec.localBalls_valid⟩
  else ⟨localBall initial, initial_valid.localBalls_valid⟩

theorem ValidAt.localTreeOfState_balls {n : ℕ} {s : State} (hs : ValidAt n s) :
    (localTreeOfState s).val = localBall s := by
  simp only [localTreeOfState, dite_eq_left (show ∃ n, ValidAt n s from ⟨n, hs⟩)]

noncomputable def localTreeLaw (x : SignSequence) (n : ℕ) : Measure LocalTree.Tree :=
  (treeLaw x n).map localTreeOfState

instance localTreeLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (localTreeLaw x n) := by
  unfold localTreeLaw
  infer_instance

theorem treeLaw_localTreeOfState_balls (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, (localTreeOfState s).val = localBall s :=
  (treeLaw_valid x n).mono fun _ hs => hs.localTreeOfState_balls

end Forward
end Freezing1
