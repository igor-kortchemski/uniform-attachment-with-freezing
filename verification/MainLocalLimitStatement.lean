module

import Freezing1.MainLocalLimit
import Freezing1.ForwardLifetimeLimit

/-!
Independent source-type probe for T01, Introduction lines 257–267.
The statements expose the actual pushforward laws, the pointwise schedule
quantifiers, finite labeled-ball convergence, and the printed post-step
reciprocal sum. The second example requires one measurable pathwise tree
whose law is both weak limits. This file is verification evidence only.
-/

open Freezing1 Freezing1.Forward Freezing1.ForwardInfiniteHistory
open Filter MeasureTheory
open scoped Topology BigOperators Classical

private theorem actual_ball_convergence_iff (y : SignSequence) :
    AlmostSureLocalConvergence y ↔
      (∀ᵐ H ∂fullLaw y, ∃ T : LocalTree.Tree,
        ∀ r : ℕ, ∀ᶠ n in atTop, localBall (H n) r = T.val r) := by
  constructor
  · intro hc
    filter_upwards [hc, fullLaw_valid y] with H hH hv
    obtain ⟨T, hT⟩ := hH
    refine ⟨T, fun r => ?_⟩
    have he := (LocalTree.tendsto_iff_balls _ _).mp hT r
    filter_upwards [he] with n hn
    simpa only [(hv n).localTreeOfState_balls] using hn
  · intro hc
    filter_upwards [hc, fullLaw_valid y] with H hH hv
    obtain ⟨T, hT⟩ := hH
    refine ⟨T, (LocalTree.tendsto_iff_balls _ _).mpr (fun r => ?_)⟩
    filter_upwards [hT r] with n hn
    simpa only [(hv n).localTreeOfState_balls] using hn

example (x : ℕ → ℕ → Bool) (y : ℕ → Bool)
    (hxy : ∀ i : ℕ, 1 ≤ i → ∃ N : ℕ, ∀ n ≥ N, x n i = y i)
    (hτ : extinctionTime y = ⊤) :
    ((∃ ν : ProbabilityMeasure LocalTree.Tree,
        Tendsto (β := ProbabilityMeasure LocalTree.Tree) (fun n => (⟨(treeLaw (x n) n).map localTreeOfState,
          inferInstance⟩ : ProbabilityMeasure LocalTree.Tree)) atTop (𝓝 ν)) ↔
      (∀ᵐ H ∂fullLaw y, ∃ T : LocalTree.Tree,
        ∀ r : ℕ, ∀ᶠ n in atTop, localBall (H n) r = T.val r)) ∧
    ((∀ᵐ H ∂fullLaw y, ∃ T : LocalTree.Tree,
        ∀ r : ℕ, ∀ᶠ n in atTop, localBall (H n) r = T.val r) ↔
      Tendsto (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n,
        if y i then (0 : ℝ) else 1 / (activeCount y i : ℝ)) atTop atTop) := by
  have hp : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i :=
    fun i hi => eventually_atTop.mpr (hxy i hi)
  have hmain := local_convergence_equivalences x y hp hτ
  change (DiagonalLocalConvergence x ↔ _) ∧ (_ ↔ _)
  exact ⟨hmain.1.trans (actual_ball_convergence_iff y),
    (actual_ball_convergence_iff y).symm.trans hmain.2⟩

example (x : ℕ → ℕ → Bool) (y : ℕ → Bool)
    (hxy : ∀ i : ℕ, 1 ≤ i → ∃ N : ℕ, ∀ n ≥ N, x n i = y i)
    (hτ : extinctionTime y = ⊤)
    (hdiv : Tendsto (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n,
      if y i then (0 : ℝ) else 1 / (activeCount y i : ℝ)) atTop atTop) :
    ∃ L : History → LocalTree.Tree,
      AEMeasurable L (fullLaw y) ∧
      (∀ᵐ H ∂fullLaw y, ∀ r : ℕ, ∀ᶠ n in atTop, localBall (H n) r = (L H).val r) ∧
      Tendsto (β := ProbabilityMeasure LocalTree.Tree) (fun n => (⟨(treeLaw y n).map localTreeOfState,
          inferInstance⟩ : ProbabilityMeasure LocalTree.Tree)) atTop
        (𝓝 (ProbabilityMeasure.map
          (⟨fullLaw y, inferInstance⟩ : ProbabilityMeasure History) L)) ∧
      Tendsto (β := ProbabilityMeasure LocalTree.Tree) (fun n => (⟨(treeLaw (x n) n).map localTreeOfState,
          inferInstance⟩ : ProbabilityMeasure LocalTree.Tree)) atTop
        (𝓝 (ProbabilityMeasure.map
          (⟨fullLaw y, inferInstance⟩ : ProbabilityMeasure History) L)) := by
  have hp : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i :=
    fun i hi => eventually_atTop.mpr (hxy i hi)
  obtain ⟨hm, ha, hf, hd⟩ := local_convergence_common_limit x y hp hτ hdiv
  refine ⟨localLimit, hm, ?_, hf, hd⟩
  filter_upwards [ha, fullLaw_valid y] with H hH hv r
  have he := (LocalTree.tendsto_iff_balls _ _).mp hH r
  filter_upwards [he] with n hn
  simpa only [(hv n).localTreeOfState_balls] using hn

#print axioms Freezing1.local_convergence_equivalences
#print axioms Freezing1.local_convergence_common_limit
#print axioms Freezing1.ForwardInfiniteHistory.tendsto_diagonal_localProbabilityLaw
#print axioms Freezing1.ForwardInfiniteHistory.fullLaw_tendsto_localLimit
#print axioms Freezing1.ForwardInfiniteHistory.not_summable_freezing_of_diagonal_local_tendsto
#print axioms Freezing1.ForwardInfiniteHistory.all_vertices_eventually_frozen_iff
