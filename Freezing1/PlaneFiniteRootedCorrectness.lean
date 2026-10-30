module

public import Freezing1.PlaneFiniteRootedEdges

/-! The finite rooted reader is exactly the complete labelled radius truncation. -/

@[expose] public section

namespace Freezing1.PlaneLabelled

open BinaryBijection Filter
open scoped Topology Classical

theorem present_finiteRooted (T : Tree (Option ℕ) ℕ) (h : ℕ) (w : PlaneTree.Address)
    (hw : w.length ≤ h) :
    PlaneTree.Present (finiteRooted T h).toPlaneTree w ↔ PlaneTree.Present (shape T) w := by
  have hh := subtree_finiteRootedAt_isSome T ⟨[], PlaneTree.present_nil _⟩ h w hw
  simp only [List.nil_append] at hh
  change ((finiteRooted T h).subtree w).isSome = decide (PlaneTree.Present (shape T) w) at hh
  rw [Rooted.present_iff_subtree, hh]
  simp

theorem finiteRooted_ball (T : Tree (Option ℕ) ℕ) (h : ℕ) :
    ball (finiteRooted T h).toPlaneLabelled h = ball T h := by
  ext ⟨w, v, e⟩
  simp only [mem_ball, Rooted.shape_toPlaneLabelled, Rooted.vertexSlot_toPlaneLabelled,
    Rooted.edgeSlot_toPlaneLabelled]
  by_cases hw : w.length ≤ h
  · rw [present_finiteRooted T h w hw, vertexCode_finiteRooted T h w hw,
      edgeCode_finiteRooted T h w hw]
  · simp only [hw, false_and, and_false]

theorem finiteRooted_tendsto (T : Tree (Option ℕ) ℕ) :
    Tendsto (fun h => (finiteRooted T h).toPlaneLabelled) atTop (𝓝 T) := by
  apply (tendsto_iff_balls _ _).mpr
  intro h
  filter_upwards [eventually_ge_atTop h] with H hH
  have hh := Rooted.labelledBall_truncate (finiteRooted T H) h h le_rfl
  rw [finiteRooted_truncate T H h hH] at hh
  exact hh.symm.trans (finiteRooted_ball T h)

end Freezing1.PlaneLabelled
