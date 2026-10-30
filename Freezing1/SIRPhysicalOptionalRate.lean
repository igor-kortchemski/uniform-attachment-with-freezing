module

public import Freezing1.SIRPhysicalZeroRate
public import Freezing1.SIROptionalContactCompatibility
public import Freezing1.SIRPhysicalLaws

/-!
# Positive and zero intensity on the same optional contact protocol

At positive intensity the source's arrival paths inject as nonempty contact
paths. At zero intensity their counting marginals force the empty paths.
Both branches use the same next-event protocol, and their entire tree laws
are the corresponding embedded SIR laws.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem optionalContactTreePath_arrivals (n : ℕ) (recovery : Individual n → ℝ)
    (contacts : Individual n → Individual n → PoissonContact.ArrivalPath) :
    optionalContactTreePath n recovery (fun v w => Sum.inr (contacts v w)) =
      poissonFullContactTreePath n (recoveryContactData recovery contacts) := by
  funext k
  change (optionalContactRun n recovery (fun v w => Sum.inr (contacts v w)) k).population.project = _
  rw [optionalContactRun_arrivals]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]

theorem positiveRate_optional_physical_tree_fullLaw (n : ℕ) (rate : ℝ≥0) (hr : 0 < rate)
    (recovery : Individual n → Ω → ℝ)
    (contacts : Individual n → Individual n → Ω → PoissonContact.ArrivalPath)
    (hsource : PoissonSIRData mu n rate
      (fun c omega => recoveryContactData (fun v => recovery v omega) (fun v w => contacts v w omega) c)) :
    mu.map (fun omega => optionalContactTreePath n (fun v => recovery v omega)
      (fun v w => Sum.inr (contacts v w omega))) = treeFullLaw rate n := by
  calc
    _ = (physicalTreePathLaw mu n (fun c omega => recoveryContactData
        (fun v => recovery v omega) (fun v w => contacts v w omega) c) : Measure (ℕ → TreeState)) := by
      change mu.map _ = mu.map _
      apply congrArg (fun f => mu.map f)
      funext omega
      exact optionalContactTreePath_arrivals n _ _
    _ = _ := hsource.treePathLaw_eq hr

end Freezing1.SIR
