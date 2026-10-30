module

import Freezing1.ForwardFreezingDegrees
import Freezing1.AttachmentDensity

/-! Independently reconstructed from source lines 893–906 by the integrating
reviewer. The actual degree is expanded to its graph-neighbour cardinality. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal BigOperators Classical
open Freezing1 Freezing1.Forward Freezing1.ForwardInfiniteHistory

example (x : SignSequence) (H : History)
    (valid : ∀ n, ValidAt n (H n))
    (legal : ∀ n, LegalOrHeld x n (H n) (H (n + 1))) :
    (∃ T : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 T)) ↔
      ∀ v, ∃ d : ℕ, ∀ n,
        ((H n).vertices.filter fun w => (H n).graph.Adj v w).card ≤ d :=
  exists_local_limit_iff_degree_bounded valid legal

example (x : SignSequence) (neverExtinct : extinctionTime x = ⊤)
    (v : ℕ) (positive : (fullLaw x) {H | ∀ k, v ∈ (H (v + k)).active} ≠ 0) :
    iIndepSet (fun i => if v < i ∧ x i = true then
      {H : History | (H i).parent i = v} else ∅)
      ((fullLaw x)[|{H | ∀ k, v ∈ (H (v + k)).active}]) :=
  conditional_postBirthAttachment_iIndepSet x neverExtinct v positive

example (x : SignSequence) (neverExtinct : extinctionTime x = ⊤) (v : ℕ) :
    ∀ᵐ H ∂(fullLaw x).restrict {H | ∀ k, v ∈ (H (v + k)).active},
      Tendsto (fun n => ((H n).vertices.filter fun w => (H n).graph.Adj v w).card)
        atTop atTop :=
  restrict_survival_vertexDegree_tendsto_atTop x neverExtinct v

example (x : SignSequence) :
    ∀ᵐ H ∂fullLaw x,
      (∃ T : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 T)) ↔
        ∀ v b, v ∈ (H b).vertices →
          ∃ a j, ∀ n ≥ a, (H n).frozenAt v = some j :=
  fullLaw_local_limit_iff_all_eventually_frozen_all_schedules x

example (x : SignSequence) (neverExtinct : extinctionTime x = ⊤) :
    (∀ n : ℕ, 1 ≤ n → (1 : ℝ) / 2 ≤ (plusCount x n : ℝ) / n) ∧
      Tendsto (fun n => ∑ i ∈ Finset.range n,
        if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0) atTop atTop :=
  ⟨fun n hn => attachment_density_ge_half x neverExtinct n hn,
    printed_attachment_reciprocal_sum_tendsto x neverExtinct⟩

#print axioms exists_local_limit_iff_degree_bounded
#print axioms conditional_postBirthAttachment_iIndepSet
#print axioms restrict_survival_vertexDegree_tendsto_atTop
#print axioms fullLaw_local_limit_iff_all_eventually_frozen_all_schedules
#print axioms attachment_density_ge_half
#print axioms printed_attachment_reciprocal_sum_tendsto
