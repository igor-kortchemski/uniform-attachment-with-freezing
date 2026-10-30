module

public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Tactic
public import Mathlib.Tactic.DeriveCountable

/-!
# Coherent finite balls for the local topology of time-labelled trees

A nonroot vertex is identified by its incoming edge's birth time. The root
has ID zero. Records retain parents, heights and frozen labels, including
labels on the boundary of each ball. Every ball is finite; consequently this
encoding does not admit a root with infinitely many children.

The space is a closed subset of a countable product of discrete countable
spaces. The connection to forward states and graph-distance balls is proved
separately; this module supplies the topological construction itself.
-/

@[expose] public section

namespace Freezing1.LocalTree

open Filter Set TopologicalSpace
open scoped Topology Classical

structure VertexRecord where
  birth : ℕ
  parent : ℕ
  height : ℕ
  frozenAt : Option ℕ
  deriving DecidableEq, Countable

abbrev Ball := Finset VertexRecord

instance : TopologicalSpace Ball := ⊥
instance : DiscreteTopology Ball := ⟨rfl⟩
instance : PolishSpace Ball := inferInstance

def restrict (h : ℕ) (B : Ball) : Ball := B.filter (fun v => v.height ≤ h)

structure ValidBall (h : ℕ) (B : Ball) : Prop where
  root : ∃ v ∈ B, v.birth = 0
  bounded : ∀ v ∈ B, v.height ≤ h
  unique : ∀ v ∈ B, ∀ w ∈ B, v.birth = w.birth → v = w
  root_data : ∀ v ∈ B, v.birth = 0 → v.parent = 0 ∧ v.height = 0
  parent_data : ∀ v ∈ B, v.birth ≠ 0 →
    ∃ w ∈ B, w.birth = v.parent ∧ w.height + 1 = v.height ∧ w.birth < v.birth

theorem restrict_restrict (B : Ball) {h H : ℕ} (hh : h ≤ H) :
    restrict h (restrict H B) = restrict h B := by
  ext v
  simp only [restrict, Finset.mem_filter]
  exact ⟨fun hv => ⟨hv.1.1, hv.2⟩, fun hv => ⟨⟨hv.1, hv.2.trans hh⟩, hv.2⟩⟩

theorem ValidBall.restrict {B : Ball} {h H : ℕ} (hB : ValidBall H B) :
    ValidBall h (restrict h B) := by
  constructor
  · obtain ⟨v, hv, hv0⟩ := hB.root
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, by rw [(hB.root_data v hv hv0).2]; omega⟩, hv0⟩
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v hv w hw he
    exact hB.unique v (Finset.mem_filter.mp hv).1 w (Finset.mem_filter.mp hw).1 he
  · intro v hv he
    exact hB.root_data v (Finset.mem_filter.mp hv).1 he
  · intro v hv hv0
    obtain ⟨hvB, hvh⟩ := Finset.mem_filter.mp hv
    obtain ⟨w, hw, he, hhgt, hbirth⟩ := hB.parent_data v hvB hv0
    exact ⟨w, Finset.mem_filter.mpr ⟨hw, by omega⟩, he, hhgt, hbirth⟩

theorem ValidBall.restrict_self {B : Ball} {h : ℕ} (hB : ValidBall h B) :
    LocalTree.restrict h B = B := by
  apply Finset.filter_eq_self.mpr
  exact hB.bounded

def ValidSequence (B : ℕ → Ball) : Prop :=
  ∀ h, ValidBall h (B h) ∧ restrict h (B (h + 1)) = B h

theorem isClosed_validSequence : IsClosed {B : ℕ → Ball | ValidSequence B} := by
  have hset : {B : ℕ → Ball | ValidSequence B} =
      ⋂ h, ({B | ValidBall h (B h)} ∩ {B | restrict h (B (h + 1)) = B h}) := by
    ext B
    simp only [ValidSequence, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [hset]
  apply isClosed_iInter
  intro h
  apply IsClosed.inter
  · exact (isClosed_discrete (s := {B : Ball | ValidBall h B})).preimage (continuous_apply h)
  · exact isClosed_eq ((continuous_of_discreteTopology : Continuous (restrict h)).comp
      (continuous_apply (h + 1))) (continuous_apply h)

abbrev Tree := {B : ℕ → Ball // ValidSequence B}

instance : PolishSpace Tree := isClosed_validSequence.polishSpace

/-- Local convergence is exactly eventual equality of every complete finite
ball, including the root and the labels on its boundary. -/
theorem tendsto_iff_balls {ι : Type*} {l : Filter ι} (T : ι → Tree) (t : Tree) :
    Tendsto T l (𝓝 t) ↔ ∀ h, ∀ᶠ i in l, (T i).val h = t.val h := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  simp only [nhds_discrete, tendsto_pure]

theorem Tree.restrict_ball (T : Tree) {h H : ℕ} (hh : h ≤ H) :
    restrict h (T.val H) = T.val h := by
  induction H, hh using Nat.le_induction with
  | base => exact (T.property h).1.restrict_self
  | succ H hH ih =>
    rw [← restrict_restrict (T.val (H + 1)) hH, (T.property H).2, ih]

end Freezing1.LocalTree
