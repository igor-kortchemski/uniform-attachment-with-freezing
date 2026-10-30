module

public import Freezing1.UnorderedTreeTopology
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Continuous forgetting-order projection and exact finite-ball classification. -/

@[expose] public section

namespace Freezing1.PlaneLabelled

open BinaryBijection

noncomputable def BallIso.finiteRootedIso {S T : Tree (Option ℕ) ℕ} {h : ℕ} (e : BallIso S T h) :
    UnorderedIso (finiteRooted S h).toPlaneLabelled (finiteRooted T h).toPlaneLabelled :=
  (((BallIso.of_ball_eq (finiteRooted S h).toPlaneLabelled S h (finiteRooted_ball S h)).trans e).trans
    (BallIso.of_ball_eq T (finiteRooted T h).toPlaneLabelled h (finiteRooted_ball T h).symm)).toUnorderedIso
      (finiteRooted_vertex_bound S h) (finiteRooted_vertex_bound T h)

theorem finiteRooted_class_eq_iff_ballIso (S T : Tree (Option ℕ) ℕ) (h : ℕ) :
    UnorderedLocal.ofRooted (finiteRooted S h) = UnorderedLocal.ofRooted (finiteRooted T h) ↔
      Nonempty (BallIso S T h) := by
  constructor
  · exact nonempty_ballIso_of_finiteRooted_eq S T h
  · rintro ⟨e⟩
    exact (UnorderedLocal.finiteClasses_eq_iff_actualIso UnorderedLocal.finiteIsoReflection _ _).mpr
      ⟨e.finiteRootedIso⟩

end Freezing1.PlaneLabelled

namespace Freezing1.UnorderedLocal

open Filter MeasureTheory
open scoped Topology

noncomputable instance : MeasurableSpace Tree := borel Tree
instance : BorelSpace Tree := ⟨rfl⟩

theorem finiteBall_ofPlane_eq_iff_ballIso (S T : PlaneSource) (h : ℕ) :
    finiteBall (ofPlane S) h = finiteBall (ofPlane T) h ↔ Nonempty (PlaneLabelled.BallIso S T h) :=
  PlaneLabelled.finiteRooted_class_eq_iff_ballIso S T h

theorem finiteBall_ofPlane_eq_of_ball_eq (S T : PlaneSource) (h : ℕ)
    (hh : PlaneLabelled.ball S h = PlaneLabelled.ball T h) :
    finiteBall (ofPlane S) h = finiteBall (ofPlane T) h :=
  (finiteBall_ofPlane_eq_iff_ballIso S T h).mpr ⟨PlaneLabelled.BallIso.of_ball_eq S T h hh⟩

theorem continuous_finiteBall (h : ℕ) : Continuous (fun T : Tree => finiteBall T h) := by
  have hc : Continuous (towerMap finiteIsoReflection) := continuous_induced_dom
  exact (continuous_apply h).comp (continuous_subtype_val.comp hc)

theorem continuous_ofPlane : Continuous ofPlane := by
  apply continuous_iff_continuousAt.mpr
  intro T
  apply (tree_tendsto_iff_balls ofPlane (ofPlane T)).mpr
  intro h
  have hb := (PlaneLabelled.tendsto_iff_balls (l := 𝓝 T) (fun S : PlaneSource => S) T).mp tendsto_id h
  filter_upwards [hb] with S hS
  exact finiteBall_ofPlane_eq_of_ball_eq S T h hS

end Freezing1.UnorderedLocal
