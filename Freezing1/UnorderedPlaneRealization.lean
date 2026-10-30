module

public import Freezing1.UnorderedCoherentBalls
public import Freezing1.RootedPlaneLabelledCoding

/-!
# Realizing coherent unordered balls by an actual infinite plane-labelled tree

Compatible finite representatives are constructed by compactness in the
preceding module. Their stable coordinates define a genuine locally finite
Ulam--Harris tree, with exactly the required finite labelled balls.
Forgetting the auxiliary plane order still requires its separate quotient
or graph-isomorphism bridge before the broad source space is identified.
-/

@[expose] public section

namespace Freezing1.UnorderedLocal

open BinaryBijection Filter
open scoped Topology Classical

def realizedOffspring (r : ℕ → Rooted) (u : PlaneTree.Address) : ℕ :=
  (r (u.length + 1)).offspring u

def realizedVertexCode (r : ℕ → Rooted) (u : PlaneTree.Address) : PlaneLabelled.LabelSlot (Option ℕ) :=
  (r u.length).vertexCode u

def realizedEdgeCode (r : ℕ → Rooted) (u : PlaneTree.Address) : PlaneLabelled.LabelSlot ℕ :=
  (r u.length).edgeCode u

theorem offspring_stabilizes (r : ℕ → Rooted)
    (hr : ∀ h, (r (h + 1)).truncate h = r h) (u : PlaneTree.Address) (H : ℕ)
    (hH : u.length + 1 ≤ H) : (r H).offspring u = realizedOffspring r u := by
  calc
    (r H).offspring u = ((r H).truncate (u.length + 1)).offspring u :=
      (Rooted.offspring_truncate _ _ _ (by omega)).symm
    _ = realizedOffspring r u := congrArg (fun t : Rooted => t.offspring u)
      (raw_truncate_ball r hr hH)

theorem vertexCode_stabilizes (r : ℕ → Rooted)
    (hr : ∀ h, (r (h + 1)).truncate h = r h) (u : PlaneTree.Address) (H : ℕ)
    (hH : u.length ≤ H) : (r H).vertexCode u = realizedVertexCode r u := by
  calc
    (r H).vertexCode u = ((r H).truncate u.length).vertexCode u :=
      (Rooted.vertexCode_truncate _ _ _ le_rfl).symm
    _ = realizedVertexCode r u := congrArg (fun t : Rooted => t.vertexCode u)
      (raw_truncate_ball r hr hH)

theorem edgeCode_stabilizes (r : ℕ → Rooted)
    (hr : ∀ h, (r (h + 1)).truncate h = r h) (u : PlaneTree.Address) (H : ℕ)
    (hH : u.length ≤ H) : (r H).edgeCode u = realizedEdgeCode r u := by
  calc
    (r H).edgeCode u = ((r H).truncate u.length).edgeCode u :=
      (Rooted.edgeCode_truncate _ _ _ le_rfl).symm
    _ = realizedEdgeCode r u := congrArg (fun t : Rooted => t.edgeCode u)
      (raw_truncate_ball r hr hH)

theorem offspring_tendsto (r : ℕ → Rooted)
    (hr : ∀ h, (r (h + 1)).truncate h = r h) :
    Tendsto (fun H => (r H).offspring) atTop (𝓝 (realizedOffspring r)) := by
  rw [tendsto_pi_nhds]
  intro u
  rw [nhds_discrete, tendsto_pure]
  filter_upwards [eventually_ge_atTop (u.length + 1)] with H hH
  exact offspring_stabilizes r hr u H hH

theorem vertexCode_tendsto (r : ℕ → Rooted)
    (hr : ∀ h, (r (h + 1)).truncate h = r h) :
    Tendsto (fun H => (r H).vertexCode) atTop (𝓝 (realizedVertexCode r)) := by
  rw [tendsto_pi_nhds]
  intro u
  rw [nhds_discrete, tendsto_pure]
  filter_upwards [eventually_ge_atTop u.length] with H hH
  exact vertexCode_stabilizes r hr u H hH

theorem edgeCode_tendsto (r : ℕ → Rooted)
    (hr : ∀ h, (r (h + 1)).truncate h = r h) :
    Tendsto (fun H => (r H).edgeCode) atTop (𝓝 (realizedEdgeCode r)) := by
  rw [tendsto_pi_nhds]
  intro u
  rw [nhds_discrete, tendsto_pure]
  filter_upwards [eventually_ge_atTop u.length] with H hH
  exact edgeCode_stabilizes r hr u H hH

theorem exists_realization_of_compatible (r : ℕ → Rooted)
    (hr : ∀ h, (r (h + 1)).truncate h = r h) :
    ∃ T : PlaneLabelled.Tree (Option ℕ) ℕ,
      Tendsto (fun H => (r H).toPlaneLabelled) atTop (𝓝 T) ∧
      ∀ h, PlaneLabelled.ball T h = PlaneLabelled.ball (r h).toPlaneLabelled h := by
  have hf := offspring_tendsto r hr
  have hcan : PlaneTree.Canonical (realizedOffspring r) :=
    PlaneTree.isClosed_canonical.mem_of_tendsto hf
      (Eventually.of_forall (fun H => (r H).canonical_offspring))
  let shape : PlaneTree.Tree := ⟨realizedOffspring r, hcan⟩
  have hs : Tendsto (fun H => (r H).toPlaneTree) atTop (𝓝 shape) := by
    rw [tendsto_subtype_rng]
    exact hf
  let p : PlaneLabelled.RawTree (Option ℕ) ℕ :=
    (shape, realizedVertexCode r, realizedEdgeCode r)
  have hp : Tendsto (fun H => ((r H).toPlaneTree, (r H).vertexCode, (r H).edgeCode)) atTop (𝓝 p) := by
    simpa only [p, nhds_prod_eq] using
      hs.prodMk ((vertexCode_tendsto r hr).prodMk (edgeCode_tendsto r hr))
  have hvalid : PlaneLabelled.Valid p :=
    (PlaneLabelled.isClosed_valid (Option ℕ) ℕ).mem_of_tendsto hp
      (Eventually.of_forall (fun H => (r H).toPlaneLabelled.property))
  let T : PlaneLabelled.Tree (Option ℕ) ℕ := ⟨p, hvalid⟩
  have ht : Tendsto (fun H => (r H).toPlaneLabelled) atTop (𝓝 T) := by
    rw [tendsto_subtype_rng]
    exact hp
  refine ⟨T, ht, ?_⟩
  intro h
  have hb := (PlaneLabelled.tendsto_iff_balls _ _).mp ht h
  obtain ⟨H, hball, hH⟩ := (hb.and (eventually_ge_atTop h)).exists
  have hrh := raw_truncate_ball r hr hH
  have hh := Rooted.labelledBall_truncate (r H) h h le_rfl
  rw [hrh] at hh
  exact hball.symm.trans hh.symm

/-- Every quotient tower has an actual infinite locally finite plane tree
realization with genuine finite representatives of each unordered ball. -/
theorem exists_plane_realization (B : BallTower) :
    ∃ T : PlaneLabelled.Tree (Option ℕ) ℕ, ∃ r : ℕ → Rooted,
      (∀ h, ofRooted (r h) = B.val h) ∧
      (∀ h, (r (h + 1)).truncate h = r h) ∧
      ∀ h, PlaneLabelled.ball T h = PlaneLabelled.ball (r h).toPlaneLabelled h := by
  obtain ⟨r, hrep, hr⟩ := exists_coherent_representatives B
  obtain ⟨T, _, hball⟩ := exists_realization_of_compatible r hr
  exact ⟨T, r, hrep, hr, hball⟩

end Freezing1.UnorderedLocal
