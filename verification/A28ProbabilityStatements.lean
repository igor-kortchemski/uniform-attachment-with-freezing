module

public import Freezing1.IidScheduleExtinction
public import Freezing1.IidScheduleLocalCriterion

/-! Author statement and trust checks for the probability part of A28. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory ProbabilityTheory Forward ForwardInfiniteHistory ForwardAnnealed
open scoped ENNReal Classical Topology

example (p : unitInterval) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ => signLaw p),
      Tendsto (fun n : ℕ => (activeCount x n : ℝ) / n) atTop (𝓝 (2 * (p : ℝ) - 1)) :=
  iid_activeCount_drift p

example (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ => signLaw p), ∃ k, activeCount x k = 0 :=
  iid_extinction_of_le_half p hp

example (p : unitInterval) (hp : (p : ℝ) = 1 / 2) :
    ∀ᵐ x ∂iidSignLaw p, ∃ k, activeCount x k = 0 :=
  iid_extinction_of_le_half p hp.le

example (p : unitInterval) (hp0 : (1 : ℝ) / 2 < p) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ x ∂iidSignLaw p, extinctionTime x = ⊤ →
      (0 < 2 * (p : ℝ) - 1) ∧
      Tendsto (fun n : ℕ => (activeCount x n : ℝ) / n) atTop (𝓝 (2 * (p : ℝ) - 1)) ∧
      Tendsto (freezingReciprocalSum x) atTop atTop ∧
      (∀ᵐ H ∂ForwardInfiniteHistory.fullLaw x,
        Tendsto (fun n => Forward.localTreeOfState (H n)) atTop (𝓝 (localLimit H))) :=
  iid_nonextinction_local_criterion p hp0 hp1

example (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ x ∂iidSignLaw p, ∀ᵐ H ∂ForwardInfiniteHistory.fullLaw x,
      Tendsto (fun n => Forward.localTreeOfState (H n)) atTop (𝓝 (localLimit H)) :=
  iid_schedules_local_converge p hp

#print axioms SIR.BiasedWalk.coupledFullLaw_fst
#print axioms SIR.BiasedWalk.coupledFullLaw_order
#print axioms SIR.BiasedWalk.everZero_probability_eq_one
#print axioms PlaneForward.fullLaw_ever_absorbed_ae_of_le_half
#print axioms PlaneForward.geometricBienayme_finite_probability_of_le_half
#print axioms iidSignLaw_prefix
#print axioms iid_activeCount_drift
#print axioms iid_freezing_density
#print axioms iid_extinction_of_le_half
#print axioms iid_nonextinction_probability_supercritical
#print axioms Forward.not_summable_printedFreezingReciprocal_of_density
#print axioms iid_nonextinction_local_criterion
#print axioms iid_schedules_local_converge

end Freezing1
