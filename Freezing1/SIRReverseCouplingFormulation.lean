module

public import Freezing1.SIRCountsExtinctionIndex
public import Freezing1.IidHalfSlope

/-!
# The exact unresolved reverse iid coupling obligation

The auxiliary iid marginal is unconditional and may be correlated with
the epidemic and the late event. No conditional iid law or reverse hazard
bound is built into this formulation. Existence is not assumed or asserted.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Classical

def sourceLatePressureEvent (rate : ℝ≥0) (n : ℕ) (ε : unitInterval) : Set (ℕ → Counts) :=
  {H | ∀ k : ℕ, (3 : ℝ) * n / 2 ≤ k → k ≤ 2 * n →
    (infectionProbability rate (H k).susceptible : ℝ) ≤ ε}

noncomputable def sourceReverseWindow (n : ℕ) (H : ℕ → Counts) : ℕ :=
  min (n / 2) (boundedExtinctionIndex n H - n)

def sourceReverseBirth (n : ℕ) (H : ℕ → Counts) (j : ℕ) : Prop :=
  (H (boundedExtinctionIndex n H - j)).infectious <
    (H (boundedExtinctionIndex n H - j + 1)).infectious

def sourceReverseBadEvent (rate : ℝ≥0) (n : ℕ) (ε : unitInterval) (j : ℕ) :
    Set (ℕ → Counts) :=
  {H | H ∈ sourceLatePressureEvent rate n ε ∧ 1 ≤ j ∧ j ≤ sourceReverseWindow n H ∧
    sourceReverseBirth n H j}

theorem measurableSet_sourceLatePressureEvent (rate : ℝ≥0) (n : ℕ) (ε : unitInterval) :
    MeasurableSet (sourceLatePressureEvent rate n ε) := by
  apply Measurable.setOf
  apply Measurable.forall
  intro k
  apply measurable_const.imp
  apply measurable_const.imp
  apply measurableSet_setOfPred.mp
  exact measurableSet_le ((measurable_of_countable
    (fun c : Counts => (infectionProbability rate c.susceptible : ℝ))).comp
      (measurable_pi_apply k)) measurable_const

theorem measurable_sourceReverseWindow (n : ℕ) : Measurable (sourceReverseWindow n) :=
  (measurable_of_countable (fun τ : ℕ => min (n / 2) (τ - n))).comp
    (measurable_boundedExtinctionIndex n)

theorem measurable_countAt_measurable_index (k : (ℕ → Counts) → ℕ) (hk : Measurable k) :
    Measurable (fun H : ℕ → Counts => H (k H)) := by
  have heval : Measurable (fun q : (ℕ → Counts) × ℕ => q.1 q.2) :=
    measurable_from_prod_countable_left (fun j => measurable_pi_apply j)
  exact heval.comp (measurable_id.prodMk hk)

theorem measurableSet_sourceReverseBirth (n j : ℕ) :
    MeasurableSet {H : ℕ → Counts | sourceReverseBirth n H j} := by
  have hm := measurable_boundedExtinctionIndex n
  have hleft : Measurable (fun H : ℕ → Counts =>
      (H (boundedExtinctionIndex n H - j)).infectious) :=
    (measurable_of_countable Counts.infectious).comp
      (measurable_countAt_measurable_index _ ((measurable_of_countable (fun τ : ℕ => τ - j)).comp hm))
  have hright : Measurable (fun H : ℕ → Counts =>
      (H (boundedExtinctionIndex n H - j + 1)).infectious) :=
    (measurable_of_countable Counts.infectious).comp
      (measurable_countAt_measurable_index _
        ((measurable_of_countable (fun τ : ℕ => τ - j + 1)).comp hm))
  exact measurableSet_lt hleft hright

theorem measurableSet_sourceReverseBadEvent (rate : ℝ≥0) (n : ℕ) (ε : unitInterval) (j : ℕ) :
    MeasurableSet (sourceReverseBadEvent rate n ε j) := by
  have hc : MeasurableSet {H : ℕ → Counts | 1 ≤ j} :=
    (measurable_const : Measurable (fun _ : ℕ → Counts => 1 ≤ j)).setOf
  have hw : MeasurableSet {H : ℕ → Counts | j ≤ sourceReverseWindow n H} :=
    measurableSet_le measurable_const (measurable_sourceReverseWindow n)
  exact (measurableSet_sourceLatePressureEvent rate n ε).inter
    (hc.inter (hw.inter (measurableSet_sourceReverseBirth n j)))

/-- The source's required coupling, with the actual complete epidemic
law and the genuine iid sign-law marginal. Existence remains open. -/
def SourceReverseIidCoupling (rate : ℝ≥0) (n : ℕ) (ε : unitInterval) : Prop :=
  ∃ γ : ProbabilityMeasure ((ℕ → Counts) × SignSequence),
    (γ : Measure ((ℕ → Counts) × SignSequence)).map Prod.fst = countsFullLaw rate n ∧
    (γ : Measure ((ℕ → Counts) × SignSequence)).map Prod.snd =
      ForwardAnnealed.iidSignLaw (unitInterval.symm ε) ∧
    ∀ᵐ p ∂(γ : Measure ((ℕ → Counts) × SignSequence)),
      ∀ j : ℕ, p.1 ∈ sourceReverseBadEvent rate n ε j → p.2 j = false

end Freezing1.SIR
