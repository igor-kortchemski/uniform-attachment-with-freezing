module

import Freezing1.FinitePlaneShuffleMain

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical

namespace Freezing1

set_option backward.isDefEq.respectTransparency false

example (m : ℕ) : Finite {T : PlaneTree.Tree //
    {u : PlaneTree.Address | PlaneTree.Present T u}.Finite ∧
      {u : PlaneTree.Address | PlaneTree.Present T u}.ncard = m} :=
  inferInstanceAs (Finite (PlaneTree.FinitePlaneClass m))

example (p : unitInterval) (hp : (p : ℝ) < 1) (T : PlaneTree.Tree)
    (hT : {u : PlaneTree.Address | PlaneTree.Present T u}.Finite) :
    (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree) {T} =
      ENNReal.ofReal ((1 - (p : ℝ)) ^ {u : PlaneTree.Address | PlaneTree.Present T u}.ncard *
        (p : ℝ) ^ ({u : PlaneTree.Address | PlaneTree.Present T u}.ncard - 1)) :=
  ForwardAnnealed.planeLimitLaw_atom p hp _ T hT rfl

example (p : unitInterval) (hp : (p : ℝ) < 1) (m : ℕ) (hm : 1 ≤ m) :
    ∀ᵐ H ∂PlaneForward.fullLaw p PlaneForward.initial,
      ((H (2 * m - 1)).active.card = 0 ∧
        ∀ k < 2 * m - 1, (H k).active.card ≠ 0) ↔
      ({u : PlaneTree.Address | PlaneTree.Present (PlaneForward.chainLimit H) u}.Finite ∧
        {u : PlaneTree.Address | PlaneTree.Present (PlaneForward.chainLimit H) u}.ncard = m) :=
  PlaneForward.ae_extinctionTimeIs_iff_finiteVertexCount p hp m hm

-- Read the genuine tree at extinction itself, then apply the actual independent
-- uniform sibling-permutation kernel; expand the target into all finite shapes.
example (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (m : ℕ) (hm : 1 ≤ m) :
    (((PlaneForward.fullLaw p PlaneForward.initial)[|
      {H | (H (2 * m - 1)).active.card = 0 ∧
        ∀ k < 2 * m - 1, (H k).active.card ≠ 0}]).map
      (fun H => PlaneForward.shape (H (2 * m - 1)))).bind PlaneTree.shuffleLaw =
      (Fintype.card (PlaneTree.FinitePlaneClass m) : ℝ≥0∞)⁻¹ •
        ∑ T : PlaneTree.FinitePlaneClass m, Measure.dirac T.val := by
  change (((PlaneForward.fullLaw p PlaneForward.initial)[|
    {H | PlaneForward.ExtinctionTimeIs (2 * m - 1) H}]).map
      (fun H => PlaneForward.shape (H (2 * m - 1)))).bind PlaneTree.shuffleLaw =
        PlaneTree.finitePlaneUniform m
  rw [ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane_at_time p hp0 hp1 m hm]
  exact PlaneTree.finitePlaneUniform_bind_shuffleLaw m

example (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (m : ℕ) (hm : 1 ≤ m) :
    0 < PlaneForward.fullLaw p PlaneForward.initial
      {H | (H (2 * m - 1)).active.card = 0 ∧
        ∀ k < 2 * m - 1, (H k).active.card ≠ 0} :=
  ForwardAnnealed.measure_extinctionTimeIs_pos p hp0 hp1 m hm

example (p : unitInterval) (n : ℕ) (hn : n % 2 = 0) :
    PlaneForward.fullLaw p PlaneForward.initial
      {H | (H n).active.card = 0 ∧ ∀ k < n, (H k).active.card ≠ 0} = 0 :=
  ForwardAnnealed.measure_extinctionTimeIs_even p hn

#print axioms PlaneTree.finitePlaneClass_fintype
#print axioms ForwardAnnealed.planeLimitLaw_atom
#print axioms PlaneForward.ae_extinctionTimeIs_iff_finiteVertexCount
#print axioms ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane_at_time
#print axioms ForwardAnnealed.measure_extinctionTimeIs_pos
#print axioms ForwardAnnealed.measure_extinctionTimeIs_even
#print axioms PlaneTree.shufflePMF
#print axioms PlaneTree.finitePlaneUniform_bind_shuffleLaw
#print axioms ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane_shuffled

end Freezing1
