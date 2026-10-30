module

import Freezing1.MainGeometricLimit
import Freezing1.PlaneTreeLocalTopology

/-!
Independent reconstruction of T02, Introduction thm:BGW (lines 277--280),
and its chronological-ordering interpretation in the proof (978--1012).
The concrete law is expanded to independent potential offspring counts and
canonical pruning, while the source limit is on the actual annealed path
space. These are source-statement checks, not Comparator/deposit evidence.
-/

open Freezing1 Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Classical

set_option backward.isDefEq.respectTransparency false

private theorem actualLimitLaw_eq (p : unitInterval) (hp : (p : ℝ) < 1) :
    (ForwardAnnealed.fullLaw p).map
      (fun H => LocalTree.toPlaneTree (ForwardInfiniteHistory.localLimit H)) =
      (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree) := by
  rw [ForwardAnnealed.planeLimitLaw_eq_map p hp]
  rfl

-- The actual history law averages the original fixed-schedule histories
-- over the genuine iid attachment/freezing signs indexed one through n.
example (p : unitInterval) (n : ℕ) :
    (ForwardAnnealed.fullLaw p).map (Preorder.frestrictLe n) =
      (Measure.pi (fun _ : Fin n => bernoulliMeasure true false p)).bind
        (fun w => (ForwardInfiniteHistory.fullLaw (ForwardAnnealed.wordSchedule w)).map
          (Preorder.frestrictLe n)) :=
  ForwardAnnealed.map_prefix_eq_iid_sign_mixture p n

-- Exact canonical-process form of the source theorem, with every semantic
-- operation determining the limit law visible in the conclusion.
example (p : unitInterval) (hp : (p : ℝ) < 1) :
    (∀ᵐ H ∂ForwardAnnealed.fullLaw p,
      Tendsto (fun n => LocalTree.toPlaneTree (Forward.localTreeOfState (H n))) atTop
        (𝓝 (LocalTree.toPlaneTree (ForwardInfiniteHistory.localLimit H)))) ∧
      (ForwardAnnealed.fullLaw p).map
        (fun H => LocalTree.toPlaneTree (ForwardInfiniteHistory.localLimit H)) =
      (Measure.infinitePi (fun _ : PlaneTree.Address =>
        geometricMeasure (unitInterval.symm p))).map PlaneTree.prune :=
  ForwardAnnealed.iid_signs_geometric_local_limit p hp

-- In the actual local topology this is eventual equality of every complete
-- finite Ulam--Harris ball, with one common limit for all radii.
example (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ H ∂ForwardAnnealed.fullLaw p, ∀ h : ℕ, ∀ᶠ n in atTop,
      PlaneTree.ball (LocalTree.toPlaneTree (Forward.localTreeOfState (H n))) h =
        PlaneTree.ball (LocalTree.toPlaneTree (ForwardInfiniteHistory.localLimit H)) h := by
  filter_upwards [(ForwardAnnealed.iid_signs_geometric_local_limit p hp).1] with H hH
  exact (PlaneTree.tendsto_iff_balls _ _).mp hH

-- Full Bienaymé property: the root law and the joint conditional law of
-- all k child subtrees, not only one-dimensional subtree marginals.
example (p : unitInterval) (hp : (p : ℝ) < 1) :
    ((ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree).map PlaneTree.degree =
      geometricMeasure (unitInterval.symm p)) ∧
      ∀ k : ℕ, (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree)
        {T | PlaneTree.degree T = k} ≠ 0 →
        (ProbabilityTheory.cond (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree)
          {T | PlaneTree.degree T = k}).map
          (fun T (i : Fin k) => PlaneTree.child T (i.val + 1)) =
          Measure.pi (fun _ : Fin k => (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree)) :=
  ForwardAnnealed.planeLimitLaw_isBienayme p hp

-- The literal offspring mass in the Introduction, with the actual limit
-- pushforward rather than a generic law satisfying an assumed fixed point.
example (p : unitInterval) (hp : (p : ℝ) < 1) (k : ℕ) :
    ((ForwardAnnealed.fullLaw p).map
      (fun H => LocalTree.toPlaneTree (ForwardInfiniteHistory.localLimit H)))
        {T | PlaneTree.degree T = k} =
      ENNReal.ofReal ((1 - (p : ℝ)) * (p : ℝ) ^ k) := by
  rw [actualLimitLaw_eq p hp]
  exact ForwardAnnealed.planeLimitLaw_offspring_mass p hp k

-- The proved first-child fixed point refers to the same actual limit law
-- twice, and takes no branching, survival, or fairness hypothesis.
example (p : unitInterval) (hp : (p : ℝ) < 1) :
    let μ : Measure PlaneTree.Tree := (ForwardAnnealed.fullLaw p).map
      (fun H => LocalTree.toPlaneTree (ForwardInfiniteHistory.localLimit H))
    μ = ENNReal.ofReal (1 - (p : ℝ)) • Measure.dirac PlaneTree.leaf +
      ENNReal.ofReal (p : ℝ) • (μ.prod μ).map (fun q => PlaneTree.graft q.1 q.2) := by
  dsimp only
  rw [actualLimitLaw_eq p hp]
  exact ForwardAnnealed.planeLimitLaw_fixedPoint p hp

-- Boundary case p=0 is within the theorem's domain and carries root mass1
-- at offspring count0; no conditioning on a null positive-degree event.
example : (ForwardAnnealed.planeLimitLaw (0 : unitInterval) : Measure PlaneTree.Tree)
    {T | PlaneTree.degree T = 0} = 1 := by
  simpa using ForwardAnnealed.planeLimitLaw_offspring_mass (0 : unitInterval) (by norm_num) 0

#print axioms Freezing1.ForwardAnnealed.fullLaw
#print axioms Freezing1.ForwardAnnealed.planeLimit
#print axioms Freezing1.ForwardAnnealed.planeLimitLaw
#print axioms Freezing1.PlaneTree.geometricBienaymeLaw
#print axioms Freezing1.PlaneTree.prune
#print axioms Freezing1.ForwardAnnealed.map_fullLaw_toPlaneState
#print axioms Freezing1.PlaneForward.interleaving_fair
#print axioms Freezing1.InterleavedChain.extracted_pair_map_eq_prod
#print axioms Freezing1.PlaneForward.map_fullLaw_chainLimit
#print axioms Freezing1.PlaneForward.map_interleaved_fullLaw_graft
#print axioms Freezing1.PlaneForward.map_extractedLimitPair
#print axioms Freezing1.ForwardAnnealed.planeLimitLaw_fixedPoint
#print axioms Freezing1.ForwardAnnealed.planeLimitLaw_isBienayme
#print axioms Freezing1.ForwardAnnealed.planeLimitLaw_eq_geometricBienaymeLaw
#print axioms Freezing1.ForwardAnnealed.planeLimitLaw_offspring_mass
#print axioms Freezing1.ForwardAnnealed.iid_signs_geometric_local_limit
