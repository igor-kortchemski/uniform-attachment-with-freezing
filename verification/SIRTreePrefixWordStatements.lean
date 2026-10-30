module

import Freezing1.SIRTreePrefixWordObservations
import Freezing1.MainSIRUniformSamplesStrong

/-!
Independent reconstruction of the joint adaptive-prefix law. Earlier
count gates and the final tree statistic occur inside one integral.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

namespace Verification.SIRTreePrefixWords

open Freezing1 Freezing1.SIR

set_option backward.isDefEq.respectTransparency false

theorem full_prefix (rate : ℝ≥0) (n k : ℕ) :
    (treeFullLaw rate n).map (fun H => fun i : Finset.Iic k => H i.val) =
      (signWordLaw rate n k).bind (conditionalTreePrefixWordLaw n) :=
  treeFullLaw_prefix_word_mixture rate n k

theorem all_count_coordinates (n k : ℕ) (w : Fin k → Bool) :
    ∀ᵐ P ∂conditionalTreePrefixWordLaw n w,
      ∀ i : Finset.Iic k, (P i).counts = countsPrefixWord n w i := by
  filter_upwards [conditionalTreePrefixWordLaw_phase n w] with P hP
  exact hP.2

theorem earlier_gate_height (rate : ℝ≥0) (n k a : ℕ) (ha : a ≤ k) (A : Set ℕ) :
    (∫⁻ H, if 0 < (H a).counts.infectious then
        PlaneForward.vertexHeightKernel (H k).tree A else 0 ∂treeFullLaw rate n) =
      ∫⁻ w, if 0 < (countsPrefixWord n w ⟨a, Finset.mem_Iic.mpr ha⟩).infectious then
        ((planeWordLaw w).bind PlaneForward.vertexHeightKernel) A else 0
        ∂signWordLaw rate n k := by
  have hh := lintegral_treeFullLaw_countsPrefix_tree rate n k
    (fun z => if 0 < (z.1 ⟨a, Finset.mem_Iic.mpr ha⟩).infectious then
      PlaneForward.vertexHeightKernel z.2 A else 0)
  calc
    _ = ∫⁻ w, ∫⁻ s, if 0 < (countsPrefixWord n w ⟨a, Finset.mem_Iic.mpr ha⟩).infectious then
          PlaneForward.vertexHeightKernel s A else 0 ∂planeWordLaw w ∂signWordLaw rate n k := hh
    _ = _ := by
      apply lintegral_congr
      intro w
      split_ifs with h
      · exact (Measure.bind_apply (Set.to_countable A).measurableSet
          PlaneForward.vertexHeightKernel.aemeasurable).symm
      · simp only [lintegral_zero]

theorem earlier_gate_pair (rate : ℝ≥0) (n k a : ℕ) (ha : a ≤ k)
    (A : Set (ℕ × ℕ × ℕ)) :
    (∫⁻ H, if 0 < (H a).counts.infectious then
        PlaneForward.pairDataKernel (H k).tree A else 0 ∂treeFullLaw rate n) =
      ∫⁻ w, if 0 < (countsPrefixWord n w ⟨a, Finset.mem_Iic.mpr ha⟩).infectious then
        ((planeWordLaw w).bind PlaneForward.pairDataKernel) A else 0
        ∂signWordLaw rate n k := by
  have hh := lintegral_treeFullLaw_countsPrefix_tree rate n k
    (fun z => if 0 < (z.1 ⟨a, Finset.mem_Iic.mpr ha⟩).infectious then
      PlaneForward.pairDataKernel z.2 A else 0)
  calc
    _ = ∫⁻ w, ∫⁻ s, if 0 < (countsPrefixWord n w ⟨a, Finset.mem_Iic.mpr ha⟩).infectious then
          PlaneForward.pairDataKernel s A else 0 ∂planeWordLaw w ∂signWordLaw rate n k := hh
    _ = _ := by
      apply lintegral_congr
      intro w
      split_ifs with h
      · exact (Measure.bind_apply (Set.to_countable A).measurableSet
          PlaneForward.pairDataKernel.aemeasurable).symm
      · simp only [lintegral_zero]

#print axioms full_prefix
#print axioms all_count_coordinates
#print axioms earlier_gate_height
#print axioms earlier_gate_pair

end Verification.SIRTreePrefixWords
