module

import Freezing1.FinitePlaneConditionedUniform

open MeasureTheory ProbabilityTheory
open Freezing1
open scoped Classical ENNReal

/-! Authored exact-type reconstruction for the A03 finite extinction-conditioned example
(source lines 271-274, second bullet), chronological plane order. -/

-- The source's symmetric success probability, as an element of the unit interval.
noncomputable def halfP : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

private theorem halfP_pos : 0 < (halfP : ℝ) := by simp [halfP]
private theorem halfP_lt : (halfP : ℝ) < 1 := by simp [halfP]; norm_num

-- Odd extinction time 2m-1: positive probability, equal to |class| * (1/2)^m (1/2)^(m-1).
example (m : ℕ) (hm : 1 ≤ m) :
    PlaneForward.fullLaw halfP PlaneForward.initial
        {H | PlaneForward.ExtinctionTimeIs (2 * m - 1) H} =
      (Fintype.card (PlaneTree.FinitePlaneClass m) : ℝ≥0∞) *
        ENNReal.ofReal ((1 - (halfP : ℝ)) ^ m * (halfP : ℝ) ^ (m - 1)) :=
  ForwardAnnealed.measure_extinctionTimeIs halfP halfP_lt m hm

example (m : ℕ) (hm : 1 ≤ m) :
    0 < PlaneForward.fullLaw halfP PlaneForward.initial
        {H | PlaneForward.ExtinctionTimeIs (2 * m - 1) H} :=
  ForwardAnnealed.measure_extinctionTimeIs_pos halfP halfP_pos halfP_lt m hm

-- Each finite plane tree with exactly m vertices has conditional mass 1 / |class|, and nothing
-- else has mass: the conditioned terminal tree is uniform on the class.
example (m : ℕ) (hm : 1 ≤ m) (T : PlaneTree.Tree) (hT : PlaneTree.FiniteVertices T)
    (hc : PlaneTree.finiteVertexCount T = m) :
    (((PlaneForward.fullLaw halfP PlaneForward.initial)[|
        {H | PlaneForward.ExtinctionTimeIs (2 * m - 1) H}]).map PlaneForward.chainLimit) {T} =
      (Fintype.card (PlaneTree.FinitePlaneClass m) : ℝ≥0∞)⁻¹ := by
  rw [(ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane halfP halfP_pos halfP_lt
    m hm).2, PlaneTree.finitePlaneUniform_apply m (measurableSet_singleton T)]
  convert mul_one ((Fintype.card (PlaneTree.FinitePlaneClass m) : ℝ≥0∞)⁻¹) using 2
  rw [Nat.cast_eq_one, Finset.card_eq_one]
  refine ⟨⟨T, hT, hc⟩, ?_⟩
  ext U
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_singleton_iff,
    Finset.mem_singleton]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩

example (m : ℕ) (hm : 1 ≤ m) :
    (((PlaneForward.fullLaw halfP PlaneForward.initial)[|
        {H | PlaneForward.ExtinctionTimeIs (2 * m - 1) H}]).map PlaneForward.chainLimit)
      (PlaneTree.finitePlaneSet m)ᶜ = 0 := by
  rw [(ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane halfP halfP_pos halfP_lt
    m hm).2, PlaneTree.finitePlaneUniform_apply m
      (PlaneTree.measurableSet_finitePlaneSet m).compl]
  convert mul_zero ((Fintype.card (PlaneTree.FinitePlaneClass m) : ℝ≥0∞)⁻¹) using 2
  rw [Nat.cast_eq_zero, Finset.card_eq_zero]
  ext U
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
    Set.mem_compl_iff, not_not]
  exact U.property

-- Read at the extinction time itself: the stopped tree T_n, n = 2m-1.
example (m : ℕ) (hm : 1 ≤ m) :
    ((PlaneForward.fullLaw halfP PlaneForward.initial)[|
        {H | PlaneForward.ExtinctionTimeIs (2 * m - 1) H}]).map
          (fun H => PlaneForward.shape (H (2 * m - 1))) = PlaneTree.finitePlaneUniform m :=
  ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane_at_time halfP halfP_pos
    halfP_lt m hm

-- Parity: even times are impossible first extinction times.
example (n : ℕ) (hn : n % 2 = 0) :
    PlaneForward.fullLaw halfP PlaneForward.initial
        {H | PlaneForward.ExtinctionTimeIs n H} = 0 :=
  ForwardAnnealed.measure_extinctionTimeIs_even halfP hn

-- The exact atom mass of the actual limit law on a finite plane tree with m vertices.
example (m : ℕ) (T : PlaneTree.Tree) (hT : PlaneTree.FiniteVertices T)
    (hc : PlaneTree.finiteVertexCount T = m) :
    (ForwardAnnealed.planeLimitLaw halfP : Measure PlaneTree.Tree) {T} =
      ENNReal.ofReal ((1 - (halfP : ℝ)) ^ m * (halfP : ℝ) ^ (m - 1)) :=
  ForwardAnnealed.planeLimitLaw_atom halfP halfP_lt m T hT hc

-- The class is exactly the finite plane trees with m vertices, and it is nonempty.
example (m : ℕ) (hm : 1 ≤ m) : Nonempty (PlaneTree.FinitePlaneClass m) :=
  PlaneTree.finitePlaneClass_nonempty hm

-- Actual first-extinction identity: the vertex count of the stopped tree.
example (p : unitInterval) (hp : (p : ℝ) < 1) (m : ℕ) (hm : 1 ≤ m) :
    ∀ᵐ H ∂PlaneForward.fullLaw p PlaneForward.initial,
      PlaneForward.ExtinctionTimeIs (2 * m - 1) H ↔
        (PlaneTree.FiniteVertices (PlaneForward.chainLimit H) ∧
          PlaneTree.finiteVertexCount (PlaneForward.chainLimit H) = m) :=
  PlaneForward.ae_extinctionTimeIs_iff_finiteVertexCount p hp m hm

#print axioms Freezing1.ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane
#print axioms Freezing1.ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane_at_time
#print axioms Freezing1.ForwardAnnealed.measure_extinctionTimeIs
#print axioms Freezing1.ForwardAnnealed.measure_extinctionTimeIs_pos
#print axioms Freezing1.ForwardAnnealed.measure_extinctionTimeIs_even
#print axioms Freezing1.ForwardAnnealed.planeLimitLaw_atom
#print axioms Freezing1.PlaneForward.ae_extinctionTimeIs_iff_finiteVertexCount
#print axioms Freezing1.PlaneForward.ae_vertex_active_time_count
#print axioms Freezing1.PlaneTree.finitePlaneUniform_apply
#print axioms Freezing1.PlaneTree.finitePlaneClass_nonempty
