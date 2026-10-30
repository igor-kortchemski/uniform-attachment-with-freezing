module

import Freezing1.IidScheduleLocalCriterion
import Freezing1.IidScheduleExtinction

open Freezing1 Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical Topology

namespace A28IndependentAudit

example (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ => ForwardAnnealed.signLaw p),
      ∃ k, activeCount x k = 0 := ForwardAnnealed.iid_extinction_of_le_half p hp

example (p : unitInterval) (hp0 : (1 : ℝ) / 2 < p) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ => ForwardAnnealed.signLaw p),
      (∀ k, 0 < activeCount x k) →
      Tendsto (fun n : ℕ => (activeCount x n : ℝ) / n) atTop (nhds (2 * (p : ℝ) - 1)) ∧
      Tendsto (freezingReciprocalSum x) atTop atTop ∧
      (∀ᵐ H ∂ForwardInfiniteHistory.fullLaw x,
        Tendsto (fun n => Forward.localTreeOfState (H n)) atTop
          (nhds (ForwardInfiniteHistory.localLimit H))) := by
  filter_upwards [ForwardAnnealed.iid_nonextinction_local_criterion p hp0 hp1] with x hx
  intro hpos
  exact (hx ((extinctionTime_eq_top_iff x).mpr hpos)).2

#print axioms ForwardAnnealed.iid_extinction_of_le_half
#print axioms ForwardAnnealed.iid_nonextinction_local_criterion
#print axioms ForwardAnnealed.iid_schedules_local_converge

end A28IndependentAudit
