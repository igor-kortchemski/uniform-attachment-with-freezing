module

public import Freezing1.SIRPoissonFullContactLaw

/-! Expanded statements for the actual entire-arrival-path SIR protocol. -/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

example {n : ℕ} (F : ClockFrame n) (data : PoissonClockData n) (v w : Individual n) :
    nextContactDelayArray F data (v, some w) =
      (data (v, some w)).1
        (PoissonContact.count (data (v, some w)) (F.time - F.birthTime v)) := rfl

example {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    mu.map (fun omega k =>
      (poissonFullContactRun n (fun c => X c omega) k).population.project) =
      CountableMarkovChain.fullLaw (treeKernel r) (initialTreeState n) :=
  independent_poisson_fullContact_tree_fullLaw mu n r hr X hX hindep hrecovery hcontact

example {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    mu.map (fun omega k =>
      let z := (poissonFullContactRun n (fun c => X c omega) k).population
      (⟨z.susceptible.card, z.active.card⟩ : Counts)) =
      CountableMarkovChain.fullLaw (countsKernel r) (initialCounts n) :=
  independent_poisson_fullContact_counts_fullLaw mu n r hr X hX hindep hrecovery hcontact

example {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : ClockSlot n) → Ω → ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : Individual n,
      PoissonContact.HasPoissonCounts (mu.map (X (v, some w))) r) :
    mu.map (fun omega => PlaneForward.shape
      (poissonFullContactRun n (fun c => X c omega) (2 * n + 1)).population.tree) =
      (embeddedTerminalTreeLaw r n : Measure PlaneTree.Tree) :=
  independent_poisson_fullContact_terminal_tree_law mu n r hr X hX hindep hrecovery hcontact

#print axioms independent_poisson_fullContactRun_eq_preassigned
#print axioms aemeasurable_poissonFullContactTreePath
#print axioms independent_poisson_fullContact_tree_fullLaw
#print axioms independent_poisson_fullContact_counts_fullLaw
#print axioms independent_poisson_fullContact_absorbed_by
#print axioms independent_poisson_fullContact_terminal_tree_law

end Freezing1.SIR
