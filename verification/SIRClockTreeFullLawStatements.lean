module

public import Freezing1.SIRClockTreeFullLaw

/-! Expanded source-model statements for the A65 complete-history milestone. -/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

example {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (preassignedClockLaw r n).map
      (fun omega k => (preassignedRun n omega k).population.project) =
      treeFullLaw (⟨r, hr.le⟩ : ℝ≥0) n :=
  preassigned_clock_tree_fullLaw hr n

example {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∀ᵐ omega ∂preassignedClockLaw r n,
      (preassignedRun n omega (2 * n + 1)).population.active = ∅ ∧
        ∀ k ≥ 2 * n + 1,
          preassignedRun n omega k = preassignedRun n omega (2 * n + 1) :=
  preassigned_clock_absorbed_by hr n

example {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    mu.map (fun omega k =>
      (preassignedRun n (firstArrivalArray (fun c => X c omega)) k).population.project) =
      CountableMarkovChain.fullLaw (treeKernel r) (initialTreeState n) :=
  independent_poisson_tree_fullLaw mu n r hr X hX hindep hrecovery hcontact

example {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    mu.map (fun omega => PlaneForward.shape
      (preassignedRun n (firstArrivalArray (fun c => X c omega))
        (2 * n + 1)).population.tree) =
      (embeddedTerminalTreeLaw r n : Measure PlaneTree.Tree) :=
  independent_poisson_terminal_tree_law mu n r hr X hX hindep hrecovery hcontact

#print axioms clockWordKernel_project
#print axioms clockWordFullLaw_project
#print axioms preassigned_clock_tree_fullLaw
#print axioms preassigned_clock_absorbed_by
#print axioms independent_poisson_tree_fullLaw
#print axioms independent_poisson_absorbed_by
#print axioms independent_poisson_terminal_tree_law

end Freezing1.SIR
