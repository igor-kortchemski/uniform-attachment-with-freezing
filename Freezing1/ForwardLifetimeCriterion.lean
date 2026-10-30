module

public import Freezing1.ForwardVertexLifetime
public import Freezing1.FreezingReciprocalSeries
public import Freezing1.SurvivalProduct

/-!
# Vanishing of actual vertex-survival probabilities

The corrected finite survival law, the scalar product criterion, and the
comparison with the printed reciprocal series give a criterion for the
actual finite-horizon probabilities. Identifying their limit with an event
on an infinite path remains a separate construction.
-/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Topology BigOperators Classical

theorem vertexSurvivalFactor_succ (x : SignSequence) (i : ℕ) :
    vertexSurvivalFactor x (i + 1) = 1 - freezingHazard x i := by
  cases hx : x (i + 1) <;> simp [vertexSurvivalFactor, freezingHazard, hx]

theorem vertexSurvivalFactor_product (x : SignSequence) (a k : ℕ) :
    (∏ i ∈ Finset.Ioc a (a + k), vertexSurvivalFactor x i) =
      ∏ i ∈ Finset.Ico a (a + k), (1 - freezingHazard x i) := by
  symm
  apply Finset.prod_bij (fun i _ => i + 1)
  · intro i hi
    have := Finset.mem_Ico.mp hi
    apply Finset.mem_Ioc.mpr
    omega
  · intro i hi j hj hij
    omega
  · intro j hj
    have := Finset.mem_Ioc.mp hj
    refine ⟨j - 1, ?_, ?_⟩
    · apply Finset.mem_Ico.mpr
      omega
    · omega
  · intro i _
    exact (vertexSurvivalFactor_succ x i).symm

/-- For an active vertex in any genuine phase state, vanishing of its
actual continuation-survival probabilities is equivalent to divergence of
the reciprocal series printed in the local-limit theorem. -/
theorem continuationLaw_vertex_survival_tendsto_zero_iff
    {x : SignSequence} {a : ℕ} {s : State} (hs : PhaseData x a s)
    (hτ : extinctionTime x = ⊤) {r : ℕ} (hr : r ∈ s.active) :
    Tendsto (fun k => (continuationLaw x a k s).real {q | r ∈ q.active}) atTop (𝓝 0) ↔
      ¬Summable (printedFreezingReciprocal x) := by
  have hbound : r ≤ a := hs.valid.vertices_le r (hs.valid.active_subset hr)
  have he : (fun k => (continuationLaw x a k s).real {q | r ∈ q.active}) =
      (fun k => ∏ i ∈ Finset.Ico a (a + k), (1 - freezingHazard x i)) := by
    funext k
    rw [continuationLaw_vertex_survival hs (by simp [hτ]) hbound,
      ite_eq_left hr, one_mul, vertexSurvivalFactor_product]
  rw [he]
  exact (tendsto_survivalProduct_tail_zero_iff_not_summable
    (freezingHazard_nonneg x hτ) (freezingHazard_lt_one x hτ) a).trans
      (not_congr (summable_freezingHazard_iff x hτ))

theorem treeLaw_eq_continuation_initial (x : SignSequence) (n : ℕ) :
    treeLaw x n = continuationLaw x 0 n initial := by
  have hh := treeLaw_add_eq_bind_continuation x 0 n
  simpa only [Nat.zero_add, treeLaw,
    Measure.dirac_bind measurable_from_top] using hh

theorem treeLaw_root_survival_tendsto_zero_iff (x : SignSequence)
    (hτ : extinctionTime x = ⊤) :
    Tendsto (fun n => (treeLaw x n).real {s | 0 ∈ s.active}) atTop (𝓝 0) ↔
      ¬Summable (printedFreezingReciprocal x) := by
  simpa only [treeLaw_eq_continuation_initial] using
    continuationLaw_vertex_survival_tendsto_zero_iff (initial_phaseData x) hτ
      (show 0 ∈ initial.active by simp [initial])

/-- The reciprocal divergence criterion written as divergence to infinity
of the paper's actual partial sums over freezing steps. -/
theorem treeLaw_root_survival_tendsto_zero_iff_sum_atTop (x : SignSequence)
    (hτ : extinctionTime x = ⊤) :
    Tendsto (fun n => (treeLaw x n).real {s | 0 ∈ s.active}) atTop (𝓝 0) ↔
      Tendsto (fun n => ∑ i ∈ Finset.range n, printedFreezingReciprocal x i) atTop atTop :=
  (treeLaw_root_survival_tendsto_zero_iff x hτ).trans
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (printedFreezingReciprocal_nonneg x hτ))

end Freezing1.Forward
