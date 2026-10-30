module

import Freezing1.MainLocalAmbient

open Filter MeasureTheory Topology
open scoped Topology

noncomputable section

namespace Freezing1.ChronologicalAmbientStatementAudit

example (T U : LocalTree.Tree) (h : ℕ) :
    UnorderedLocal.finiteBall (UnorderedLocal.ofPlane (LocalTree.toLabelledPlaneTree T)) h =
      UnorderedLocal.finiteBall (UnorderedLocal.ofPlane (LocalTree.toLabelledPlaneTree U)) h ↔
        T.val h = U.val h :=
  LocalTree.finiteBall_toUnordered_eq_iff T U h

example (T U : LocalTree.Tree) (h : ℕ) :
    Nonempty (PlaneLabelled.BallIso (LocalTree.toLabelledPlaneTree T)
      (LocalTree.toLabelledPlaneTree U) h) ↔ T.val h = U.val h :=
  LocalTree.nonempty_ballIso_iff_rawBall_eq T U h

example : IsClosedEmbedding (fun T : LocalTree.Tree =>
    UnorderedLocal.ofPlane (LocalTree.toLabelledPlaneTree T)) :=
  LocalTree.isClosedEmbedding_toUnordered

example {ι : Type*} {L : Filter ι} (S : ι → LocalTree.Tree) (T : LocalTree.Tree) :
    Tendsto (fun i => UnorderedLocal.ofPlane (LocalTree.toLabelledPlaneTree (S i))) L
      (𝓝 (UnorderedLocal.ofPlane (LocalTree.toLabelledPlaneTree T))) ↔ Tendsto S L (𝓝 T) :=
  LocalTree.tendsto_toUnordered_iff S T

example {ι : Type*} {L : Filter ι} [L.NeBot] (S : ι → LocalTree.Tree) :
    (∃ T : LocalTree.Tree, Tendsto S L (𝓝 T)) ↔
      ∃ q : UnorderedLocal.Tree,
        Tendsto (fun i => UnorderedLocal.ofPlane (LocalTree.toLabelledPlaneTree (S i))) L (𝓝 q) :=
  LocalTree.exists_localLimit_iff_ambient S

example : IsClosedEmbedding (fun μ : ProbabilityMeasure LocalTree.Tree =>
    μ.map (fun T => UnorderedLocal.ofPlane (LocalTree.toLabelledPlaneTree T))) :=
  LocalTree.isClosedEmbedding_probabilityLaw_toUnordered

example {ι : Type*} {L : Filter ι} [L.NeBot]
    (μs : ι → ProbabilityMeasure LocalTree.Tree) :
    (∃ μ : ProbabilityMeasure LocalTree.Tree, Tendsto μs L (𝓝 μ)) ↔
      ∃ ν : ProbabilityMeasure UnorderedLocal.Tree,
        Tendsto (fun i => (μs i).map
          (fun T => UnorderedLocal.ofPlane (LocalTree.toLabelledPlaneTree T))) L (𝓝 ν) :=
  LocalTree.exists_weakLimit_iff_ambient μs

example (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤) :
    ((∃ ν : ProbabilityMeasure UnorderedLocal.Tree,
      Tendsto (fun n => (ForwardInfiniteHistory.localProbabilityLaw (x n) n).map
        (fun T => UnorderedLocal.ofPlane (LocalTree.toLabelledPlaneTree T))) atTop (𝓝 ν)) ↔
      (∀ᵐ H ∂ForwardInfiniteHistory.fullLaw y, ∃ q : UnorderedLocal.Tree,
        Tendsto (fun n => UnorderedLocal.ofPlane
          (LocalTree.toLabelledPlaneTree (Forward.localTreeOfState (H n)))) atTop (𝓝 q))) ∧
    ((∀ᵐ H ∂ForwardInfiniteHistory.fullLaw y, ∃ q : UnorderedLocal.Tree,
      Tendsto (fun n => UnorderedLocal.ofPlane
        (LocalTree.toLabelledPlaneTree (Forward.localTreeOfState (H n)))) atTop (𝓝 q)) ↔
      Tendsto (fun n => ∑ i ∈ Finset.Icc 1 n,
        if y i then (0 : ℝ) else 1 / (activeCount y i : ℝ)) atTop atTop) :=
  source_local_convergence_equivalences x y hxy hτ

example (p : unitInterval) (hp : (p : ℝ) < 1) :
    (∀ᵐ H ∂ForwardAnnealed.fullLaw p,
      Tendsto (fun n => LocalTree.toUnordered (Forward.localTreeOfState (H n))) atTop
        (𝓝 (LocalTree.toUnordered (ForwardInfiniteHistory.localLimit H)))) ∧
    Tendsto (fun n => (ForwardAnnealed.localProbabilityLaw p n).map LocalTree.toUnordered) atTop
      (𝓝 ((ForwardAnnealed.localLimitLaw p).map LocalTree.toUnordered)) ∧
    (ForwardAnnealed.fullLaw p).map
      (fun H => LocalTree.toPlaneTree (ForwardInfiniteHistory.localLimit H)) =
        PlaneTree.geometricBienaymeLaw p :=
  ForwardAnnealed.iid_signs_source_ambient_local_limit p hp

#print axioms LocalTree.chronologicalAddressEquiv
#print axioms LocalTree.chronologicalBallVertexEquiv
#print axioms LocalTree.ballIso_record
#print axioms LocalTree.ballIsoOfRawBallEq
#print axioms LocalTree.finiteBall_toUnordered_eq_iff
#print axioms LocalTree.toUnordered_injective
#print axioms LocalTree.exists_chronological_of_finite_support
#print axioms LocalTree.isClosedEmbedding_toUnordered
#print axioms LocalTree.exists_localLimit_iff_ambient
#print axioms LocalTree.isClosedEmbedding_probabilityLaw_toUnordered
#print axioms LocalTree.exists_weakLimit_iff_ambient
#print axioms LocalTree.ambient_weakLimit_supported
#print axioms source_local_convergence_equivalences
#print axioms source_local_convergence_common_limit
#print axioms ForwardAnnealed.iid_signs_source_ambient_local_limit

end Freezing1.ChronologicalAmbientStatementAudit
