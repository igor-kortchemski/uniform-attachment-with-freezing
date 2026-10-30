module

public import Freezing1.PlaneBallIsoExtensions
public import Freezing1.PlaneFiniteRootedCorrectness
public import Freezing1.RootedPlaneHeightBound
public import Freezing1.UnorderedPlaneRealization

/-!
# Actual finite-isomorphism bridges for the infinite unordered quotient

These theorems use actual graph witnesses. The finite quotient converse is
applied in the final topology assembly, rather than assumed here.
-/

@[expose] public section

namespace Freezing1.PlaneLabelled

open BinaryBijection

theorem finiteRooted_vertex_bound (T : Tree (Option ℕ) ℕ) (h : ℕ)
    (u : Vertex (shape (finiteRooted T h).toPlaneLabelled)) : u.val.length ≤ h :=
  Rooted.present_length_of_fits _ h (finiteRooted_truncate T h h le_rfl) u.val u.property

noncomputable def UnorderedIso.finiteRootedIso {S T : Tree (Option ℕ) ℕ}
    (e : UnorderedIso S T) (h : ℕ) :
    UnorderedIso (finiteRooted S h).toPlaneLabelled (finiteRooted T h).toPlaneLabelled :=
  (((BallIso.of_ball_eq (finiteRooted S h).toPlaneLabelled S h (finiteRooted_ball S h)).trans
    (e.toBallIso h)).trans
      (BallIso.of_ball_eq T (finiteRooted T h).toPlaneLabelled h (finiteRooted_ball T h).symm)).toUnorderedIso
        (finiteRooted_vertex_bound S h) (finiteRooted_vertex_bound T h)

end Freezing1.PlaneLabelled

namespace Freezing1.UnorderedLocal

open BinaryBijection

theorem exists_finiteIso_realization (B : BallTower) :
    ∃ T : PlaneLabelled.Tree (Option ℕ) ℕ, ∃ r : ℕ → Rooted,
      (∀ h, ofRooted (r h) = B.val h) ∧
      ∀ h, Nonempty (PlaneLabelled.UnorderedIso
        (PlaneLabelled.finiteRooted T h).toPlaneLabelled (r h).toPlaneLabelled) := by
  obtain ⟨T, r, hrep, hr, hball⟩ := exists_plane_realization B
  refine ⟨T, r, hrep, ?_⟩
  intro h
  apply PlaneLabelled.nonempty_unorderedIso_of_ball_eq_of_bounded
    (PlaneLabelled.finiteRooted T h).toPlaneLabelled (r h).toPlaneLabelled h
    (PlaneLabelled.finiteRooted_vertex_bound T h)
    (fun u => Rooted.present_length_of_fits _ h (raw_truncate_self r hr h) u.val u.property)
  exact (PlaneLabelled.finiteRooted_ball T h).trans (hball h)

end Freezing1.UnorderedLocal
