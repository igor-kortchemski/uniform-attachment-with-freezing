module

public import Freezing1.SIRPhysicalZeroRate
public import Freezing1.SIRForwardPrefixBridge

/-! Complete joint forward-history identification for the zero-rate branch. -/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory CountableMarkovChain

theorem zeroRate_physical_original_treePrefix_word_mixture
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n k : ℕ) (recovery : Individual n → Ω → ℝ)
    (contacts : Individual n → Individual n → Ω → PoissonContact.OptionalPath)
    (hC : ∀ v w, Measurable (contacts v w))
    (hcounts : ∀ v w, PoissonContact.HasOptionalPoissonCounts (mu.map (contacts v w)) 0) :
    (mu.map (fun omega => optionalContactTreePath n (fun v => recovery v omega)
      (fun v w => contacts v w omega))).map (fun H =>
        ((fun i : Finset.Iic k => (H i.val).counts),
          (fun i : Finset.Iic k => (H i.val).tree))) =
      (signWordLaw 0 n k).bind (fun w =>
        ((ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
          (Preorder.frestrictLe k)).map
            (fun P => (countsPrefixWord n w, ForwardAnnealed.planePrefix k P))) := by
  rw [zeroRate_physical_tree_fullLaw mu n recovery contacts hC hcounts]
  exact treeFullLaw_countsPrefix_original_treePrefix_word_mixture 0 n k

end Freezing1.SIR
