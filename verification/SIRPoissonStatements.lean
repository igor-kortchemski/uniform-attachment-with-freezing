module

import Freezing1.SIRPoissonClockArray
import Freezing1.SIRClockPrefixLaw
import Freezing1.SIRPoissonFullContactLaw

/-!
Independent exact-type reconstruction of the positive-rate first-contact
component of source A65, lines 2026--2037. The input is the source's given
independent whole contact processes and recovery lifetimes. Exponential
contact delays are conclusions. No process-existence theorem is asserted.
-/

open Freezing1 MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical

example (a : SIR.PoissonContact.ArrivalPath) :
    {t : ℝ | 0 < SIR.PoissonContact.count a t} =
      Ici (a.1 0) := SIR.PoissonContact.positive_count_times a

example (nu : Measure SIR.PoissonContact.ArrivalPath) [IsProbabilityMeasure nu]
    (r : ℝ≥0) (hr : 0 < r)
    (hcounts : ∀ t : ℝ≥0,
      nu.map (fun a => SIR.PoissonContact.count a (t : ℝ)) = poissonMeasure (r * t)) :
    nu.map (fun a => a.1 0) = expMeasure (r : ℝ) :=
  SIR.PoissonContact.first_law nu r hr hcounts

example {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : SIR.ClockSlot n) → Ω → SIR.ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : SIR.Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : SIR.Individual n, ∀ t : ℝ≥0,
      (mu.map (X (v, some w))).map
        (fun a => SIR.PoissonContact.count a (t : ℝ)) = poissonMeasure (r * t)) :
    mu.map (fun omega => SIR.firstArrivalArray (fun c => X c omega)) =
      Measure.pi (fun c => expMeasure (SIR.clockSlotRate (r : ℝ) c)) :=
  SIR.independent_firstArrivalArray_law mu n r hr X hX hindep hrecovery hcontact

-- The original independent array supplies the actual event-word mass.
-- Residual independence after a history is proved, rather than a premise.
example {r : ℝ} (hr : 0 < r) (n : ℕ) (w : SIR.ClockWord n) :
    SIR.preassignedClockLaw r n (SIR.clockPrefixEvent n w) = SIR.clockWordWeight r n w :=
  SIR.preassigned_clock_word_probability hr n w

#print axioms Freezing1.SIR.PoissonContact.count_eq_zero_iff
#print axioms Freezing1.SIR.PoissonContact.positive_count_times
#print axioms Freezing1.SIR.PoissonContact.arrival_le_iff_lt_count
#print axioms Freezing1.SIR.PoissonContact.first_law
#print axioms Freezing1.SIR.independent_firstArrivalArray_law
#print axioms Freezing1.SIR.preassigned_clock_prefix_residual_law
#print axioms Freezing1.SIR.preassigned_clock_word_probability

section WholeContactProtocol

variable {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (X : (c : SIR.ClockSlot n) → Ω → SIR.ClockDatum c)
    (hX : ∀ c, Measurable (X c)) (hindep : iIndepFun X mu)
    (hrecovery : ∀ v : SIR.Individual n, mu.map (X (v, none)) = expMeasure 1)
    (hcontact : ∀ v w : SIR.Individual n, ∀ t : ℝ≥0,
      (mu.map (X (v, some w))).map
        (fun a => SIR.PoissonContact.count a (t : ℝ)) = poissonMeasure (r * t))

-- The actual protocol consults the next point of every live contact path.
-- Its entire genealogy has the true tree-kernel path law.
example : mu.map (fun omega k =>
      (SIR.poissonFullContactRun n (fun c => X c omega) k).population.project) =
    CountableMarkovChain.fullLaw (SIR.treeKernel r) (SIR.initialTreeState n) :=
  SIR.independent_poisson_fullContact_tree_fullLaw mu n r hr X hX hindep hrecovery hcontact

-- These are literal individual counts, not renamed observations.
example : mu.map (fun omega k =>
      let z := (SIR.poissonFullContactRun n (fun c => X c omega) k).population
      (⟨z.susceptible.card, z.active.card⟩ : SIR.Counts)) =
    CountableMarkovChain.fullLaw (SIR.countsKernel r) (SIR.initialCounts n) :=
  SIR.independent_poisson_fullContact_counts_fullLaw mu n r hr X hX hindep hrecovery hcontact

example : mu.map (fun omega => PlaneForward.shape
      (SIR.poissonFullContactRun n (fun c => X c omega) (2*n+1)).population.tree) =
    (SIR.embeddedTerminalTreeLaw r n : Measure PlaneTree.Tree) :=
  SIR.independent_poisson_fullContact_terminal_tree_law mu n r hr X hX hindep hrecovery hcontact

end WholeContactProtocol

#print axioms Freezing1.SIR.poissonFullContactRun_eq_preassigned
#print axioms Freezing1.SIR.independent_poisson_fullContact_tree_fullLaw
#print axioms Freezing1.SIR.independent_poisson_fullContact_counts_fullLaw
#print axioms Freezing1.SIR.independent_poisson_fullContact_absorbed_by
#print axioms Freezing1.SIR.independent_poisson_fullContact_terminal_tree_law
