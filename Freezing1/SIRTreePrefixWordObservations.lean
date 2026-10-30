module

public import Freezing1.SIRTreePrefixWordMixture

/-!
# Joint count gates and infection-tree observations
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory CountableMarkovChain
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem conditionalTreePrefixWordLaw_map_counts (n : ℕ) {k : ℕ} (w : Fin k → Bool) :
    (conditionalTreePrefixWordLaw n w).map (fun P => fun i => (P i).counts) =
      Measure.dirac (countsPrefixWord n w) := by
  calc
    _ = (conditionalTreePrefixWordLaw n w).map (fun _ => countsPrefixWord n w) := by
      apply Measure.map_congr
      filter_upwards [conditionalTreePrefixWordLaw_phase n w] with P hP
      exact funext hP.2
    _ = _ := by simp

theorem treeFullLaw_countsPrefix_original_tree_word_mixture (rate : ℝ≥0) (n k : ℕ) :
    (treeFullLaw rate n).map (fun H =>
      ((fun i : Finset.Iic k => (H i.val).counts), (H k).tree)) =
      (signWordLaw rate n k).bind (fun w =>
        (Forward.treeLaw (ForwardAnnealed.wordSchedule w) k).map
          (fun s => (countsPrefixWord n w, s.toPlaneState))) := by
  rw [treeFullLaw_countsPrefix_tree_word_mixture]
  congr 1
  funext w
  rw [← map_fixedWord_treeLaw_to_planeWordLaw,
    Measure.map_map (measurable_of_countable
      (fun s : PlaneForward.State => (countsPrefixWord n w, s)))
      Forward.measurable_toPlaneState]
  rfl

/-- Every function of the complete earlier count prefix and the last
plane state can be integrated jointly against the actual adaptive word law. -/
theorem lintegral_treeFullLaw_countsPrefix_tree (rate : ℝ≥0) (n k : ℕ)
    (F : Prefix (E := Counts) k × PlaneForward.State → ℝ≥0∞) :
    (∫⁻ H, F ((fun i : Finset.Iic k => (H i.val).counts), (H k).tree)
      ∂treeFullLaw rate n) =
      ∫⁻ w, ∫⁻ s, F (countsPrefixWord n w, s) ∂planeWordLaw w
        ∂signWordLaw rate n k := by
  have hF : Measurable F := measurable_of_countable _
  have hobs : Measurable (fun H : ℕ → TreeState =>
      ((fun i : Finset.Iic k => (H i.val).counts), (H k).tree)) := by
    exact (measurable_of_countable (fun P : Prefix (E := TreeState) k =>
      ((fun i => (P i).counts), (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩).tree))).comp
        (Preorder.measurable_frestrictLe k)
  calc
    _ = ∫⁻ z, F z ∂(treeFullLaw rate n).map (fun H =>
        ((fun i : Finset.Iic k => (H i.val).counts), (H k).tree)) :=
      (lintegral_map hF hobs).symm
    _ = _ := by
      rw [treeFullLaw_countsPrefix_tree_word_mixture,
        Measure.lintegral_bind (measurable_of_countable _).aemeasurable hF.aemeasurable]
      apply lintegral_congr
      intro w
      exact lintegral_map hF (measurable_of_countable _)

end Freezing1.SIR
