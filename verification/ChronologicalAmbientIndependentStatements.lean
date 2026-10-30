module

import Freezing1.MainLocalAmbient

/-! Independent exact-source checks by the integrating reviewer. -/

open Filter MeasureTheory Topology
open scoped Topology
open Freezing1 Freezing1.Forward Freezing1.ForwardInfiniteHistory

example (T U : LocalTree.Tree) (h : ℕ) :
    UnorderedLocal.finiteBall (LocalTree.toUnordered T) h =
      UnorderedLocal.finiteBall (LocalTree.toUnordered U) h ↔ T.val h = U.val h :=
  LocalTree.finiteBall_toUnordered_eq_iff T U h

example : IsClosedEmbedding (LocalTree.toUnordered : LocalTree.Tree → UnorderedLocal.Tree) :=
  LocalTree.isClosedEmbedding_toUnordered

example (μs : ℕ → ProbabilityMeasure LocalTree.Tree) (ν : ProbabilityMeasure UnorderedLocal.Tree)
    (hν : Tendsto (fun n => (μs n).map LocalTree.toUnordered) atTop (𝓝 ν)) :
    ∃ μ : ProbabilityMeasure LocalTree.Tree, μ.map LocalTree.toUnordered = ν ∧
      Tendsto μs atTop (𝓝 μ) :=
  LocalTree.ambient_weakLimit_supported μs ν hν

example (rows : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i)
    (hτ : extinctionTime y = ⊤) :
    ((∃ ν : ProbabilityMeasure UnorderedLocal.Tree,
        Tendsto (fun n => (localProbabilityLaw (rows n) n).map LocalTree.toUnordered)
          atTop (𝓝 ν)) ↔
      (∀ᵐ H ∂fullLaw y, ∃ T : UnorderedLocal.Tree,
        Tendsto (fun n => LocalTree.toUnordered (localTreeOfState (H n))) atTop (𝓝 T))) ∧
    ((∀ᵐ H ∂fullLaw y, ∃ T : UnorderedLocal.Tree,
        Tendsto (fun n => LocalTree.toUnordered (localTreeOfState (H n))) atTop (𝓝 T)) ↔
      Tendsto (freezingReciprocalSum y) atTop atTop) :=
  source_local_convergence_equivalences rows y hxy hτ

example (rows : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i)
    (hτ : extinctionTime y = ⊤) (hdiv : Tendsto (freezingReciprocalSum y) atTop atTop) :
    AEMeasurable (fun H => LocalTree.toUnordered (localLimit H)) (fullLaw y) ∧
    (∀ᵐ H ∂fullLaw y,
      Tendsto (fun n => LocalTree.toUnordered (localTreeOfState (H n))) atTop
        (𝓝 (LocalTree.toUnordered (localLimit H)))) ∧
    Tendsto (fun n => (localProbabilityLaw y n).map LocalTree.toUnordered) atTop
      (𝓝 ((localLimitLaw y).map LocalTree.toUnordered)) ∧
    Tendsto (fun n => (localProbabilityLaw (rows n) n).map LocalTree.toUnordered) atTop
      (𝓝 ((localLimitLaw y).map LocalTree.toUnordered)) :=
  source_local_convergence_common_limit rows y hxy hτ hdiv

example (p : unitInterval) (hp : (p : ℝ) < 1) :
    (∀ᵐ H ∂ForwardAnnealed.fullLaw p,
      Tendsto (fun n => LocalTree.toUnordered (localTreeOfState (H n))) atTop
        (𝓝 (LocalTree.toUnordered (localLimit H)))) ∧
    Tendsto (fun n => (ForwardAnnealed.localProbabilityLaw p n).map LocalTree.toUnordered)
      atTop (𝓝 ((ForwardAnnealed.localLimitLaw p).map LocalTree.toUnordered)) ∧
    (ForwardAnnealed.fullLaw p).map (fun H => LocalTree.toPlaneTree (localLimit H)) =
      PlaneTree.geometricBienaymeLaw p :=
  ForwardAnnealed.iid_signs_source_ambient_local_limit p hp

#print axioms LocalTree.finiteBall_toUnordered_eq_iff
#print axioms LocalTree.toLabelledPlaneTree
#print axioms LocalTree.isClosedEmbedding_toUnordered
#print axioms LocalTree.ambient_weakLimit_supported
#print axioms source_local_convergence_equivalences
#print axioms source_local_convergence_common_limit
#print axioms ForwardAnnealed.iid_signs_source_ambient_local_limit
