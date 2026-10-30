module

public import Freezing1.PlaneLabelledIsoDistance
public import Mathlib.Topology.Compactness.Compact

/-!
# Finite actual-ball isomorphisms and their compact compatibility space

All maps are actual bijections preserving root, radius, parents and full
labels. Nonemptiness is an explicit input to the compactness helper; it is
discharged from the finite unordered quotient in the final application.
-/

@[expose] public section

namespace Freezing1.PlaneLabelled

open Set
open scoped Topology Classical

variable {V E : Type*} {S T : Tree V E} {h H K : ℕ}

abbrev BallVertex (T : Tree V E) (h : ℕ) :=
  {u : PlaneTree.Address // u ∈ PlaneTree.ball (shape T) h}

noncomputable instance ballVertex_fintype (T : Tree V E) (h : ℕ) : Fintype (BallVertex T h) :=
  inferInstance

def BallVertex.vertex {T : Tree V E} {h : ℕ} (u : BallVertex T h) : Vertex (shape T) :=
  ⟨u.val, ((PlaneTree.mem_ball _ _ _).mp u.property).1⟩

theorem BallVertex.length_le {T : Tree V E} {h : ℕ} (u : BallVertex T h) : u.val.length ≤ h :=
  ((PlaneTree.mem_ball _ _ _).mp u.property).2

def rootBall (T : Tree V E) (h : ℕ) : BallVertex T h :=
  ⟨[], (PlaneTree.mem_ball _ _ _).mpr ⟨PlaneTree.present_nil _, by simp⟩⟩

def BallVertex.weaken {T : Tree V E} (hh : h ≤ H) (u : BallVertex T h) : BallVertex T H :=
  ⟨u.val, (PlaneTree.mem_ball _ _ _).mpr ⟨u.vertex.property, u.length_le.trans hh⟩⟩

def BallVertex.lower {T : Tree V E} (u : BallVertex T H) (hu : u.val.length ≤ h) : BallVertex T h :=
  ⟨u.val, (PlaneTree.mem_ball _ _ _).mpr ⟨u.vertex.property, hu⟩⟩

def smallerBallEquiv (T : Tree V E) (hh : h ≤ H) :
    BallVertex T h ≃ {u : BallVertex T H // u.val.length ≤ h} where
  toFun u := ⟨u.weaken hh, u.length_le⟩
  invFun u := u.val.lower u.property
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

structure BallIso (S T : Tree V E) (h : ℕ) where
  toEquiv : BallVertex S h ≃ BallVertex T h
  root_eq : toEquiv (rootBall S h) = rootBall T h
  length_eq : ∀ u, (toEquiv u).val.length = u.val.length
  parent_iff : ∀ u v, Parent u.vertex v.vertex ↔ Parent (toEquiv u).vertex (toEquiv v).vertex
  vertex_labels : ∀ u, vertexSlot S u.val = vertexSlot T (toEquiv u).val
  edge_labels : ∀ u, edgeSlot S u.val = edgeSlot T (toEquiv u).val

theorem BallIso.ext {e f : BallIso S T h} (he : e.toEquiv = f.toEquiv) : e = f := by
  cases e
  cases f
  cases he
  rfl

instance ballIso_finite (S T : Tree V E) (h : ℕ) : Finite (BallIso S T h) :=
  Finite.of_injective (fun e : BallIso S T h => e.toEquiv) (fun _ _ he => BallIso.ext he)

noncomputable instance ballIso_fintype (S T : Tree V E) (h : ℕ) : Fintype (BallIso S T h) :=
  Fintype.ofFinite _

instance (S T : Tree V E) (h : ℕ) : TopologicalSpace (BallIso S T h) := ⊥
instance (S T : Tree V E) (h : ℕ) : DiscreteTopology (BallIso S T h) := ⟨rfl⟩

noncomputable def BallIso.restrict (e : BallIso S T H) (hh : h ≤ H) : BallIso S T h where
  toEquiv := (smallerBallEquiv S hh).trans
    ((Equiv.subtypeEquiv e.toEquiv (fun u => by rw [e.length_eq u])).trans
      (smallerBallEquiv T hh).symm)
  root_eq := by
    apply Subtype.ext
    exact congrArg (fun u : BallVertex T H => u.val) e.root_eq
  length_eq u := e.length_eq (u.weaken hh)
  parent_iff u v := e.parent_iff (u.weaken hh) (v.weaken hh)
  vertex_labels u := e.vertex_labels (u.weaken hh)
  edge_labels u := e.edge_labels (u.weaken hh)

theorem BallIso.restrict_apply_val (e : BallIso S T H) (hh : h ≤ H) (u : BallVertex S h) :
    ((e.restrict hh).toEquiv u).val = (e.toEquiv (u.weaken hh)).val := rfl

theorem BallIso.restrict_self (e : BallIso S T h) : e.restrict le_rfl = e := by
  apply BallIso.ext
  apply Equiv.ext
  intro u
  apply Subtype.ext
  rfl

theorem BallIso.restrict_restrict (e : BallIso S T K) (hh : h ≤ H) (hH : H ≤ K) :
    (e.restrict hH).restrict hh = e.restrict (hh.trans hH) := by
  apply BallIso.ext
  apply Equiv.ext
  intro u
  apply Subtype.ext
  rfl

theorem exists_coherent_ball_isos (S T : Tree V E) (hn : ∀ h, Nonempty (BallIso S T h)) :
    ∃ e : ∀ h, BallIso S T h, ∀ h, (e (h + 1)).restrict (by omega : h ≤ h + 1) = e h := by
  let Space := ∀ h, BallIso S T h
  let C : ℕ → Set Space := fun h => {e | (e (h + 1)).restrict (by omega : h ≤ h + 1) = e h}
  have hclosed (h : ℕ) : IsClosed (C h) :=
    isClosed_eq ((continuous_of_discreteTopology :
      Continuous (fun e : BallIso S T (h + 1) => e.restrict (by omega : h ≤ h + 1))).comp
        (continuous_apply (h + 1))) (continuous_apply h)
  have hfinite (F : Finset ℕ) : (⋂ h ∈ F, C h).Nonempty := by
    let N := F.sup (fun h => h + 1)
    let eN : BallIso S T N := Classical.choice (hn N)
    let candidate : Space := fun h => if hh : h ≤ N then eN.restrict hh else Classical.choice (hn h)
    refine ⟨candidate, Set.mem_iInter.mpr (fun h => Set.mem_iInter.mpr (fun hf => ?_))⟩
    have hsucc : h + 1 ≤ N := Finset.le_sup (f := fun h => h + 1) hf
    have hle : h ≤ N := by omega
    change (candidate (h + 1)).restrict (by omega : h ≤ h + 1) = candidate h
    simp only [candidate, dite_eq_left hsucc, dite_eq_left hle]
    exact BallIso.restrict_restrict eN (by omega : h ≤ h + 1) hsucc
  have : CompactSpace Space := inferInstance
  obtain ⟨e, he⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  exact ⟨e, fun h => Set.mem_iInter.mp he h⟩

end Freezing1.PlaneLabelled
