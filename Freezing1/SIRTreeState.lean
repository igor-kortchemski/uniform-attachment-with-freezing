module

public import Freezing1.SIRCounts
public import Freezing1.PlaneStateUpdates

/-!
# The infection-tree state of the finite SIR process

Vertices are ordered by infection time at each parent. Infectious vertices
are exactly the active vertices of the plane attachment/freezing state.
The susceptible count accounts for the finite population.
-/

@[expose] public section

namespace Freezing1.SIR

open PlaneTree
open scoped Classical

structure TreeState where
  susceptible : ℕ
  tree : PlaneForward.State
  deriving DecidableEq, Countable

instance : MeasurableSpace TreeState := ⊤
instance : DiscreteMeasurableSpace TreeState := ⟨fun _ => trivial⟩

def initialTreeState (n : ℕ) : TreeState := ⟨n, PlaneForward.initial⟩

def TreeState.counts (z : TreeState) : Counts := ⟨z.susceptible, z.tree.active.card⟩

def TreeState.Valid (n : ℕ) (z : TreeState) : Prop :=
  PlaneForward.Valid z.tree ∧ z.susceptible + z.tree.vertices.card = n + 1

noncomputable def infectTreeState (z : TreeState) (u : Address) : TreeState :=
  ⟨z.susceptible - 1, PlaneForward.attach z.tree u⟩

def recoverTreeState (z : TreeState) (u : Address) : TreeState :=
  ⟨z.susceptible, PlaneForward.freeze z.tree u⟩

noncomputable def treeStep (z : TreeState) (sign : Bool) (u : Address) : TreeState :=
  if u ∈ z.tree.active then
    if sign then if z.susceptible = 0 then z else infectTreeState z u
    else recoverTreeState z u
  else z

theorem initialTreeState_valid (n : ℕ) : (initialTreeState n).Valid n := by
  exact ⟨PlaneForward.initial_valid, by simp [initialTreeState, PlaneForward.initial]⟩

@[simp] theorem counts_initialTreeState (n : ℕ) :
    (initialTreeState n).counts = initialCounts n := by
  simp [TreeState.counts, initialTreeState, initialCounts, PlaneForward.initial]

theorem PlaneForward_valid_attach_card {s : PlaneForward.State} (hs : PlaneForward.Valid s)
    {u : Address} (hu : u ∈ s.active) :
    (PlaneForward.attach s u).active.card = s.active.card + 1 ∧
      (PlaneForward.attach s u).vertices.card = s.vertices.card + 1 := by
  have hnew := hs.newChild_not_mem (hs.active_subset hu)
  constructor
  · apply Finset.card_insert_of_notMem
    intro ha
    exact hnew (hs.active_subset ha)
  · exact Finset.card_insert_of_notMem hnew

theorem TreeState.Valid.infect {n : ℕ} {z : TreeState} (hz : z.Valid n)
    {u : Address} (hu : u ∈ z.tree.active) (hs : 0 < z.susceptible) :
    (infectTreeState z u).Valid n := by
  refine ⟨hz.1.attach hu, ?_⟩
  change z.susceptible - 1 + (PlaneForward.attach z.tree u).vertices.card = n + 1
  rw [(PlaneForward_valid_attach_card hz.1 hu).2]
  have hpop := hz.2
  omega

theorem TreeState.Valid.recover {n : ℕ} {z : TreeState} (hz : z.Valid n) (u : Address) :
    (recoverTreeState z u).Valid n :=
  ⟨hz.1.freeze u, hz.2⟩

theorem TreeState.Valid.step {n : ℕ} {z : TreeState} (hz : z.Valid n)
    (sign : Bool) (u : Address) : (treeStep z sign u).Valid n := by
  unfold treeStep
  split_ifs with hu hsign hs
  · exact hz
  · exact hz.infect hu (by omega)
  · exact hz.recover u
  · exact hz

theorem TreeState.Valid.counts {n : ℕ} {z : TreeState} (hz : z.Valid n) :
    z.counts.Valid n := by
  change z.susceptible + z.tree.active.card ≤ n + 1
  have hcard := Finset.card_le_card hz.1.active_subset
  have hpop := hz.2
  omega

theorem treeStep_of_active_empty {z : TreeState} (hz : z.tree.active = ∅)
    (sign : Bool) (u : Address) : treeStep z sign u = z := by
  simp [treeStep, hz]

theorem treeStep_counts {z : TreeState} (hz : PlaneForward.Valid z.tree)
    {u : Address} (hu : u ∈ z.tree.active) (sign : Bool) :
    (treeStep z sign u).counts = countsStep z.counts sign := by
  have hpos : 0 < z.tree.active.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hne : z.counts.infectious ≠ 0 := hpos.ne'
  rw [treeStep, ite_eq_left hu, countsStep, ite_eq_right hne]
  cases sign
  · simp [recoverTreeState, PlaneForward.freeze, TreeState.counts, recoverCounts,
      Finset.card_erase_of_mem hu]
  · by_cases hs : z.susceptible = 0
    · simp [hs, TreeState.counts]
    · simp only [ite_true, hs, ite_false]
      have hcard := (PlaneForward_valid_attach_card hz hu).1
      simp [TreeState.counts, infectTreeState, infectCounts, hcard, hs]

theorem treeStep_vertices_mono (z : TreeState) (sign : Bool) (u : Address) :
    z.tree.vertices ⊆ (treeStep z sign u).tree.vertices := by
  unfold treeStep
  split_ifs <;> simp [infectTreeState, recoverTreeState, PlaneForward.attach,
    PlaneForward.freeze, Finset.subset_insert]

end Freezing1.SIR
