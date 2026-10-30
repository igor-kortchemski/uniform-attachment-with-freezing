module

public import Freezing1.ForwardComponentUrnPathPositive
public import Freezing1.SignedUrnPositiveExtensionMaximal

/-!
# Infinite maximal inequality for the actual extended tree component

The path-law input is supplied by the projection of the original forward
history kernels. Thus the source's component process, rather than a second
urn with matching endpoints, satisfies the infinite-horizon estimate.
-/

@[expose] public section

namespace Freezing1.ForwardInfiniteHistory

open Forward MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

theorem positiveExtension_actual_component_infinite_maximal (x : SignSequence) {a b : ℕ}
    (hab : a < b) (hb : PositiveThrough x b)
    (past : (i : Finset.Iic a) → State)
    (hs : HasHistory (positiveExtension x b) a (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩))
    {r : ℕ} (hr : r ∈ (past ⟨a, Finset.mem_Iic.mpr le_rfl⟩).active)
    {t : ℝ} (ht : 0 ≤ t) :
    (continuationHistoryLaw (positiveExtension x b) a past).real {H |
      ∃ i : ℕ, 1 ≤ i ∧ t / (activeCount x a : ℝ) <
        |(componentPopulation (H (a + i)) a r : ℝ) /
          SignedUrn.positiveExtensionPopulation x a b i - (activeCount x a : ℝ)⁻¹|} ≤
      2 * Real.exp (-((t ^ 2 / 4) * (activeCount x a : ℝ)⁻¹) /
        (SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b) + t *
          max (SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b))
            (SignedUrn.sourceEpsilon x a b hab))) := by
  have hsum : Summable (fun i : ℕ =>
      ((SignedUrn.positiveExtensionPopulation x a b i : ℝ)⁻¹) ^ 2) :=
    (summable_nat_add_iff 1).mp (SignedUrn.positiveExtension_square_summable x hab.le hb)
  have h := SignedUrn.infinite_maximal_summable
    (μ := continuationHistoryLaw (positiveExtension x b) a past)
    (fun i (H : History) => componentPopulation (H (a + i)) a r)
    (SignedUrn.positiveExtensionPopulation x a b)
    (positiveExtension_actual_component_hasPathLaws x hab.le hb past hs hr)
    (SignedUrn.positiveExtensionPopulation_positive x hb)
    (SignedUrn.positiveExtensionPopulation_signed x hab.le) hsum ht
  rwa [SignedUrn.positiveExtensionPopulation_zero x hab.le,
    SignedUrn.positiveExtension_maximum_eq_sourceEpsilon x hab hb] at h

end Freezing1.ForwardInfiniteHistory
