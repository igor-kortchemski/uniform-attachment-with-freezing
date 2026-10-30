module

public import Freezing1.IidScheduleDrift
public import Freezing1.FreezingDensityCriterion
public import Freezing1.MainLocalLimit
public import Freezing1.ForwardLocalExtinction

/-!
# The source iid walk satisfies the local-limit condition on nonextinction

The strong-law assertions are proved unconditionally under the actual iid
product, then restricted to surviving schedules. No conditional independence
is assumed after conditioning on nonextinction.
-/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open Filter MeasureTheory ProbabilityTheory Forward ForwardInfiniteHistory
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

theorem iid_freezing_divergence_on_nonextinction (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ x ∂iidSignLaw p, extinctionTime x = ⊤ →
      ¬Summable (printedFreezingReciprocal x) := by
  filter_upwards [iid_freezing_density p] with x hx
  intro hτ
  exact not_summable_printedFreezingReciprocal_of_density x hτ (by linarith) hx

/-- The exact source assertion in A28: on nonextinction in the supercritical
regime, the integer walk has positive drift and satisfies T01's reciprocal
criterion, so its genuine fixed-schedule tree process converges locally. -/
theorem iid_nonextinction_local_criterion (p : unitInterval)
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ x ∂iidSignLaw p, extinctionTime x = ⊤ →
      (0 < 2 * (p : ℝ) - 1) ∧
      Tendsto (fun n : ℕ => (activeCount x n : ℝ) / n) atTop (𝓝 (2 * (p : ℝ) - 1)) ∧
      Tendsto (freezingReciprocalSum x) atTop atTop ∧
      (∀ᵐ H ∂ForwardInfiniteHistory.fullLaw x,
        Tendsto (fun n => Forward.localTreeOfState (H n)) atTop (𝓝 (localLimit H))) := by
  filter_upwards [iid_activeCount_drift p, iid_freezing_divergence_on_nonextinction p hp1]
    with x hdrift hfreezing
  intro hτ
  have hdiv := hfreezing hτ
  exact ⟨by linarith, hdrift, (freezingReciprocalSum_tendsto_iff x hτ).mpr hdiv,
    fullLaw_tendsto_localLimit x hτ hdiv⟩

/-- The source's full local-convergence assertion for almost every iid
schedule, proved by T01 on nonextinction and actual holding after extinction. -/
theorem iid_schedules_local_converge (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ x ∂iidSignLaw p, ∀ᵐ H ∂ForwardInfiniteHistory.fullLaw x,
      Tendsto (fun n => Forward.localTreeOfState (H n)) atTop (𝓝 (localLimit H)) := by
  filter_upwards [iid_freezing_divergence_on_nonextinction p hp] with x hfreezing
  by_cases hτ : extinctionTime x = ⊤
  · exact fullLaw_tendsto_localLimit x hτ (hfreezing hτ)
  · obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hτ
    exact fullLaw_tendsto_localLimit_of_extinction ha.symm

end Freezing1.ForwardAnnealed
