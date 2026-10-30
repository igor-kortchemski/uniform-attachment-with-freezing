module

public import Freezing1.SIRForwardPrefixBridge
public import Freezing1.SIRPhysicalLaws

/-! Whole physical infection-tree histories as actual forward-word mixtures. -/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory CountableMarkovChain
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
  {n : ℕ} {rate : ℝ≥0} {X : (c : ClockSlot n) → Ω → ClockDatum c}

theorem PoissonSIRData.original_treePrefix_word_mixture
    (h : PoissonSIRData mu n rate X) (hr : 0 < rate) (k : ℕ) :
    (physicalTreePathLaw mu n X : Measure (ℕ → TreeState)).map
      (fun H => fun i : Finset.Iic k => (H i.val).tree) =
      (signWordLaw rate n k).bind (fun w =>
        ((ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
          (Preorder.frestrictLe k)).map (ForwardAnnealed.planePrefix k)) := by
  rw [h.treePathLaw_eq hr]
  exact treeFullLaw_original_treePrefix_word_mixture rate n k

/-- The entire physical tree prefix and its extinction-determining counts
belong to the same joint forward-word mixture. -/
theorem PoissonSIRData.countsPrefix_original_treePrefix_word_mixture
    (h : PoissonSIRData mu n rate X) (hr : 0 < rate) (k : ℕ) :
    (physicalTreePathLaw mu n X : Measure (ℕ → TreeState)).map (fun H =>
      ((fun i : Finset.Iic k => (H i.val).counts),
        (fun i : Finset.Iic k => (H i.val).tree))) =
      (signWordLaw rate n k).bind (fun w =>
        ((ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
          (Preorder.frestrictLe k)).map
            (fun P => (countsPrefixWord n w, ForwardAnnealed.planePrefix k P))) := by
  rw [h.treePathLaw_eq hr]
  exact treeFullLaw_countsPrefix_original_treePrefix_word_mixture rate n k

end Freezing1.SIR
