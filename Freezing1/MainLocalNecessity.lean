module

public import Freezing1.ForwardDegreeLimits
public import Freezing1.ForwardDegreeMonotonicity
public import Freezing1.LocalDegreeTightness
public import Freezing1.ForwardLocalLimit

/-!
# Necessity of the freezing-series criterion for local convergence

A summable freezing series leaves a positive mass of roots with arbitrarily
large degree. Agreement of every fixed schedule prefix transfers this
obstruction to the diagonal tree laws. Degree monotonicity includes held
states, so no survival assumption is imposed on the diagonal schedules.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology ENNReal Classical

namespace Forward

theorem diagonal_rootDegree_not_tight_of_summable_freezing
    (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤) (hs : Summable (printedFreezingReciprocal y)) :
    ∃ δ > 0, ∀ d : ℕ, ∀ᶠ n in atTop,
      δ ≤ (treeLaw (x n) n).real {s | d < rootDegree s} := by
  obtain ⟨δ, hδ, hd⟩ := rootDegree_not_tight_of_summable_freezing y hτ hs
  refine ⟨δ, hδ, fun d => ?_⟩
  obtain ⟨m, hm⟩ := (hd d).exists
  filter_upwards [eventually_ge_atTop m, eventually_treeLaw_eq hxy m] with n hmn hn
  calc
    δ ≤ (treeLaw y m).real {s | d < rootDegree s} := hm
    _ = (treeLaw (x n) m).real {s | d < rootDegree s} := by rw [hn]
    _ ≤ (treeLaw (x n) n).real {s | d < rootDegree s} :=
      treeLaw_rootDegree_tail_real_mono (x n) d hmn

end Forward

namespace ForwardInfiniteHistory

open Forward

theorem localProbabilityLaw_rootDegree_tail_real (x : SignSequence) (n d : ℕ) :
    (localProbabilityLaw x n : Measure LocalTree.Tree).real
        {T | d < LocalTree.rootDegree T} =
      (treeLaw x n).real {s | d < rootDegree s} := by
  change (localTreeLaw x n).real _ = _
  unfold Measure.real
  congr 1
  have hh := congrArg (fun μ : Measure ℕ => μ {k | d < k})
    (localTreeLaw_map_rootDegree x n)
  rw [Measure.map_apply LocalTree.continuous_rootDegree.measurable (by trivial),
    Measure.map_apply measurable_from_top (by trivial)] at hh
  exact hh

/-- Any diagonal local weak limit forces the source freezing series to
 diverge, with no diagonal extinction restriction. -/
theorem not_summable_freezing_of_diagonal_local_tendsto
    (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤) {ν : ProbabilityMeasure LocalTree.Tree}
    (hconv : Tendsto (fun n => localProbabilityLaw (x n) n) atTop (𝓝 ν)) :
    ¬Summable (printedFreezingReciprocal y) := by
  intro hs
  obtain ⟨δ, hδ, htail⟩ := diagonal_rootDegree_not_tight_of_summable_freezing x y hxy hτ hs
  obtain ⟨d, hd⟩ := LocalTree.eventually_rootDegree_tail_lt_of_tendsto hconv hδ
  obtain ⟨n, hn, hn'⟩ := ((htail d).and hd).exists
  rw [localProbabilityLaw_rootDegree_tail_real] at hn'
  exact (not_lt_of_ge hn) hn'

theorem not_summable_freezing_of_local_tendsto (x : SignSequence)
    (hτ : extinctionTime x = ⊤) {ν : ProbabilityMeasure LocalTree.Tree}
    (hconv : Tendsto (localProbabilityLaw x) atTop (𝓝 ν)) :
    ¬Summable (printedFreezingReciprocal x) :=
  not_summable_freezing_of_diagonal_local_tendsto (fun _ => x) x
    (fun _ _ => Filter.Eventually.of_forall fun _ => rfl) hτ hconv

end ForwardInfiniteHistory
end Freezing1
