module

public import Freezing1.ForwardHistoryExistence

/-!
# Forward forests cut at a prescribed time

These objects are defined from the forward terminal state alone. Vertices
frozen at or before the cut are removed; only edges born after the cut remain.
The roots are precisely the vertices active at the cut. A bounded parent
recursion counts the edges above the cut; its agreement with the graph height
is proved separately through the actual stamped-history coupling.
-/

@[expose] public section

namespace Freezing1.Forward

open scoped Classical

def cutVertices (s : State) (i : ℕ) : Finset ℕ :=
  s.vertices.filter fun v => ∀ t, s.frozenAt v = some t → i < t

noncomputable def cutRoots (s : State) (i : ℕ) : Finset ℕ := (truncateAt s i).active

def cutGraph (s : State) (i : ℕ) : SimpleGraph ℕ where
  Adj u v := u ∈ cutVertices s i ∧ v ∈ cutVertices s i ∧ s.graph.Adj u v ∧ i < max u v
  symm := ⟨by
    intro u v h
    exact ⟨h.2.1, h.1, h.2.2.1.symm, by simpa only [max_comm] using h.2.2.2⟩⟩
  loopless := ⟨fun _ h => s.graph.irrefl h.2.2.1⟩

def cutHeightAux (s : State) (i : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, v => if v ≤ i then 0 else cutHeightAux s i m (s.parent v) + 1

def cutHeight (s : State) (i v : ℕ) : ℕ := cutHeightAux s i (s.height v) v

def blockHeight (s : State) (a b v : ℕ) : ℕ := cutHeight s a v - cutHeight s b v

noncomputable def blockTallCount (s : State) (a b : ℕ) (threshold : ℝ) : ℕ :=
  ((cutRoots s b).filter fun v => threshold < (blockHeight s a b v : ℝ)).card

theorem mem_cutRoots (s : State) (i v : ℕ) :
    v ∈ cutRoots s i ↔ v ∈ cutVertices s i ∧ v ≤ i := by
  simp only [cutRoots, truncateAt, cutVertices, Finset.mem_filter]
  tauto

theorem cutRoots_subset (s : State) (i : ℕ) : cutRoots s i ⊆ cutVertices s i :=
  fun v hv => ((mem_cutRoots s i v).mp hv).1

theorem cutHeightAux_eq_zero_of_le (s : State) (i m v : ℕ) (hv : v ≤ i) :
    cutHeightAux s i m v = 0 := by cases m <;> simp [cutHeightAux, hv]

theorem cutHeight_root_zero (s : State) (i : ℕ) {v : ℕ} (hv : v ∈ cutRoots s i) :
    cutHeight s i v = 0 :=
  cutHeightAux_eq_zero_of_le s i _ v ((mem_cutRoots s i v).mp hv).2

theorem blockHeight_of_cutRoot (s : State) (a b : ℕ) {v : ℕ} (hv : v ∈ cutRoots s b) :
    blockHeight s a b v = cutHeight s a v := by
  simp only [blockHeight, cutHeight_root_zero s b hv, Nat.sub_zero]

end Freezing1.Forward
