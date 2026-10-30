module

public import Freezing1.ChronologicalAmbientEmbedding
public import Freezing1.ForwardLocalTree
public import Freezing1.ProbabilityMeasureClosedEmbedding

/-! Weak-law transport to the full unordered source ambient. Closedness of the
chronological image is proved structurally, so ambient limits require no
additional support assumption. -/

@[expose] public section

namespace Freezing1.LocalTree

open Filter MeasureTheory Topology
open scoped Topology

theorem isClosedEmbedding_probabilityLaw_toUnordered :
    IsClosedEmbedding (fun μ : ProbabilityMeasure Tree => μ.map toUnordered) :=
  Freezing1.isClosedEmbedding_probabilityMeasure_map isClosedEmbedding_toUnordered

theorem tendsto_probabilityLaw_toUnordered_iff {ι : Type*} {L : Filter ι}
    (μs : ι → ProbabilityMeasure Tree) (μ : ProbabilityMeasure Tree) :
    Tendsto (fun i => (μs i).map toUnordered) L (𝓝 (μ.map toUnordered)) ↔
      Tendsto μs L (𝓝 μ) :=
  isClosedEmbedding_probabilityLaw_toUnordered.isEmbedding.tendsto_nhds_iff.symm

theorem exists_weakLimit_iff_ambient {ι : Type*} {L : Filter ι} [L.NeBot]
    (μs : ι → ProbabilityMeasure Tree) :
    (∃ μ : ProbabilityMeasure Tree, Tendsto μs L (𝓝 μ)) ↔
      ∃ ν : ProbabilityMeasure UnorderedLocal.Tree,
        Tendsto (fun i => (μs i).map toUnordered) L (𝓝 ν) :=
  Freezing1.exists_weakLimit_iff_map isClosedEmbedding_toUnordered μs

theorem ambient_weakLimit_supported {ι : Type*} {L : Filter ι} [L.NeBot]
    (μs : ι → ProbabilityMeasure Tree) (ν : ProbabilityMeasure UnorderedLocal.Tree)
    (hν : Tendsto (fun i => (μs i).map toUnordered) L (𝓝 ν)) :
    ∃ μ : ProbabilityMeasure Tree, μ.map toUnordered = ν ∧ Tendsto μs L (𝓝 μ) := by
  obtain ⟨μ, hμ⟩ := isClosedEmbedding_probabilityLaw_toUnordered.isClosed_range.mem_of_tendsto hν
    (Eventually.of_forall fun i => ⟨μs i, rfl⟩)
  change μ.map toUnordered = ν at hμ
  refine ⟨μ, hμ, ?_⟩
  apply (tendsto_probabilityLaw_toUnordered_iff μs μ).mp
  rwa [hμ]

end Freezing1.LocalTree
