module

import Freezing1.ForwardLifetimeCriterion

open Freezing1 Filter MeasureTheory
open scoped Topology BigOperators Classical

example (x : SignSequence) (a k : ℕ) (s : Forward.State)
    (hs : Forward.PhaseData x a s) (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x)
    (r : ℕ) (hr : r ≤ a) :
    (Forward.continuationLaw x a k s).real {q | r ∈ q.active} =
      (if r ∈ s.active then (1 : ℝ) else 0) *
        ∏ i ∈ Finset.Ioc a (a + k),
          (if x i then 1 else 1 - 1 / (activeCount x (i - 1) : ℝ)) :=
  Forward.continuationLaw_vertex_survival hs hτ hr

example (x : SignSequence) (hτ : extinctionTime x = ⊤) :
    Tendsto (fun n => (Forward.treeLaw x n).real {s | 0 ∈ s.active}) atTop (𝓝 0) ↔
      Tendsto (fun n => ∑ i ∈ Finset.range n,
        if x (i + 1) then (0 : ℝ) else 1 / (activeCount x (i + 1) : ℝ)) atTop atTop :=
  Forward.treeLaw_root_survival_tendsto_zero_iff_sum_atTop x hτ

example (p : ℕ → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1) (a : ℕ) :
    Tendsto (fun n => ∏ i ∈ Finset.Ico a (a + n), (1 - p i)) atTop (𝓝 0) ↔
      ¬Summable p :=
  tendsto_survivalProduct_tail_zero_iff_not_summable hp0 hp1 a

#print axioms Freezing1.Forward.vertexSurvivalFactor
#print axioms Freezing1.Forward.vertexSurvivalFactor_nonneg
#print axioms Freezing1.Forward.step_active_old
#print axioms Freezing1.Forward.transitionLaw_old_active_probability
#print axioms Freezing1.Forward.transitionLaw_vertex_survival
#print axioms Freezing1.Forward.continuationLaw_vertex_survival_measure
#print axioms Freezing1.Forward.continuationLaw_vertex_survival
#print axioms Freezing1.Forward.freezingHazard
#print axioms Freezing1.Forward.printedFreezingReciprocal
#print axioms Freezing1.Forward.freezing_reciprocal_comparison
#print axioms Freezing1.Forward.freezingHazard_nonneg
#print axioms Freezing1.Forward.printedFreezingReciprocal_nonneg
#print axioms Freezing1.Forward.freezingHazard_le_half
#print axioms Freezing1.Forward.freezingHazard_lt_one
#print axioms Freezing1.Forward.freezingHazard_comparison
#print axioms Freezing1.Forward.summable_freezingHazard_iff
#print axioms Freezing1.survivalProduct_le_exp_neg_sum
#print axioms Freezing1.tendsto_survivalProduct_of_summable
#print axioms Freezing1.tendsto_survivalProduct_zero_iff_not_summable
#print axioms Freezing1.tendsto_survivalProduct_tail_zero_iff_not_summable
#print axioms Freezing1.Forward.vertexSurvivalFactor_succ
#print axioms Freezing1.Forward.vertexSurvivalFactor_product
#print axioms Freezing1.Forward.continuationLaw_vertex_survival_tendsto_zero_iff
#print axioms Freezing1.Forward.treeLaw_eq_continuation_initial
#print axioms Freezing1.Forward.treeLaw_root_survival_tendsto_zero_iff
#print axioms Freezing1.Forward.treeLaw_root_survival_tendsto_zero_iff_sum_atTop
