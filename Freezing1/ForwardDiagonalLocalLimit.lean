module

public import Freezing1.ForwardDiagonalBalls
public import Freezing1.LocalTreeCylinders
public import Freezing1.ForwardLocalLimit

/-!
# Diagonal local convergence to the same infinite-tree law

Pointwise eventual agreement of deterministic schedules gives common finite
prefixes. Frozen-ball comparison makes every cylinder probability of the
diagonal sequence asymptotic to the fixed-schedule probability. The local
cylinder basis then gives weak convergence to the already constructed actual
infinite-tree limit law.
-/

@[expose] public section

namespace Freezing1.ForwardInfiniteHistory

open Forward Filter MeasureTheory
open scoped Topology Classical

set_option backward.isDefEq.respectTransparency false

theorem localProbabilityLaw_cylinder_real (x : SignSequence) (n r : ℕ)
    (B : LocalTree.Ball) :
    ((localProbabilityLaw x n : Measure LocalTree.Tree).real (LocalTree.cylinder r B)) =
      (treeLaw x n).real {s | localBall s r = B} := by
  change (localTreeLaw x n).real (LocalTree.cylinder r B) = _
  rw [localTreeLaw, measureReal_def, Measure.map_apply measurable_from_top
    (LocalTree.cylinder_isClopen r B).isOpen.measurableSet]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [treeLaw_valid x n] with s hs
  apply propext
  change (localTreeOfState s).val r = B ↔ localBall s r = B
  rw [hs.localTreeOfState_balls]

/-- T01's diagonal convergence, including the identification of the limit
with the fixed-schedule almost-sure limit. No survival condition is imposed
on the approximating schedules. -/
theorem tendsto_diagonal_localProbabilityLaw
    (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤) (hdiv : ¬Summable (printedFreezingReciprocal y)) :
    Tendsto (fun n => localProbabilityLaw (x n) n) atTop (𝓝 (localLimitLaw y)) := by
  apply LocalTree.tendsto_probabilityMeasure_of_cylinders
  intro r B
  have hf := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    (tendsto_localProbabilityLaw y hτ hdiv) (LocalTree.cylinder_isClopen r B)
  have hfR := NNReal.tendsto_coe.mpr hf
  have hd := diagonal_localBall_event_difference_tendsto_zero x y hxy hτ hdiv r {B}
  have hdR : Tendsto (fun n =>
      ((localProbabilityLaw (x n) n) (LocalTree.cylinder r B) : ℝ) -
      ((localProbabilityLaw y n) (LocalTree.cylinder r B) : ℝ)) atTop (𝓝 0) := by
    simpa only [← ProbabilityMeasure.measureReal_eq_coe_coeFn,
      localProbabilityLaw_cylinder_real, Set.mem_singleton_iff] using hd
  apply NNReal.tendsto_coe.mp
  simpa only [sub_add_cancel, zero_add] using hdR.add hfR

end Freezing1.ForwardInfiniteHistory
