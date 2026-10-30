module

public import Freezing1.SIRClockWordKernel

/-! Expanded statements for the static original-array history milestone. -/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

example {r : ℝ} (hr : 0 < r) (n : ℕ) (w : List (Option (ClockSlot n))) :
    ((preassignedClockLaw r n).restrict
      {omega | preassignedWord n omega w.length = w}).map (clockPrefixResidual n w) =
      clockWordWeight r n w •
        Measure.pi (fun c : RelevantCoordinate (replayPopulation n w) =>
          expMeasure (clockSlotRate r c.val)) :=
  preassigned_clock_prefix_residual_law hr n w

example {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (preassignedClockLaw r n).map
      (fun omega : ClockArray n => fun k : ℕ => preassignedWord n omega k) =
      CountableMarkovChain.fullLaw (clockWordKernel r hr n) [] :=
  preassigned_clock_word_fullLaw hr n

example {r : ℝ} (hr : 0 < r) (n k : ℕ) :
    (preassignedClockLaw r n).map (fun omega => preassignedWord n omega k) =
      (CountableMarkovChain.fullLaw (clockWordKernel r hr n) []).map (fun H => H k) :=
  preassigned_word_marginal_eq hr n k

#print axioms clockChoiceLaw_singleton
#print axioms clockWordFullLaw_marginal
#print axioms preassigned_word_marginal_eq
#print axioms coherent_word_drop
#print axioms preassigned_clock_word_fullLaw

end Freezing1.SIR
