module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! Closed embeddings of state spaces induce closed embeddings of probability
laws. In particular, ambient weak limits of laws supported on a closed embedded
model still come from that model. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory Set Topology
open scoped Topology

variable {A B : Type*} [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A]
  [MeasurableSpace B] [TopologicalSpace B] [BorelSpace B] [NormalSpace B]
  {f : A → B}

theorem isEmbedding_probabilityMeasure_map (hf : IsClosedEmbedding f) :
    IsEmbedding (fun μ : ProbabilityMeasure A => μ.map f) := by
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding B).of_comp_iff.mp
  change IsEmbedding ((fun μ : FiniteMeasure A => μ.map f) ∘
    ProbabilityMeasure.toFiniteMeasure)
  exact (FiniteMeasure.Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure f hf).comp
    (ProbabilityMeasure.toFiniteMeasure_isEmbedding A)

omit [NormalSpace B] in
theorem range_probabilityMeasure_map (hf : IsClosedEmbedding f) :
    range (fun μ : ProbabilityMeasure A => μ.map f) =
      {ν : ProbabilityMeasure B | (ν : Measure B) (range f)ᶜ = 0} := by
  ext ν
  constructor
  · rintro ⟨μ, rfl⟩
    change ((μ : Measure A).map f) (range f)ᶜ = 0
    rw [Measure.map_apply hf.continuous.measurable
      hf.isClosed_range.isOpen_compl.measurableSet]
    simp
  · intro hν
    have hsupport : ∀ᵐ b ∂(ν : Measure B), b ∈ range f := by
      exact hν
    have : IsProbabilityMeasure ((ν : Measure B).comap f) :=
      hf.measurableEmbedding.isProbabilityMeasure_comap hsupport
    refine ⟨⟨(ν : Measure B).comap f, inferInstance⟩, ?_⟩
    apply ProbabilityMeasure.toMeasure_injective
    change ((ν : Measure B).comap f).map f = (ν : Measure B)
    rw [hf.measurableEmbedding.map_comap, Measure.restrict_eq_self_of_ae_mem hsupport]

variable [HasOuterApproxClosed B]

omit [NormalSpace B] in
theorem isClosed_probabilityMeasure_supported (S : Set B) (hS : IsClosed S) :
    IsClosed {ν : ProbabilityMeasure B | (ν : Measure B) Sᶜ = 0} := by
  rw [isClosed_iff_forall_filter]
  intro ν L hL hsupport hlim
  have : L.NeBot := hL
  have hevent : ∀ᶠ μ : ProbabilityMeasure B in L, (μ : Measure B) Sᶜ = 0 :=
    hsupport (by simp)
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (μs := id) hlim hS.isOpen_compl
  have hzero : L.liminf (fun μ : ProbabilityMeasure B => (μ : Measure B) Sᶜ) = 0 := by
    rw [liminf_congr hevent]
    simp
  exact le_antisymm (hzero ▸ hle) zero_le

theorem isClosedEmbedding_probabilityMeasure_map (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (fun μ : ProbabilityMeasure A => μ.map f) := by
  exact ⟨isEmbedding_probabilityMeasure_map hf,
    (range_probabilityMeasure_map hf).symm ▸
      isClosed_probabilityMeasure_supported (range f) hf.isClosed_range⟩

theorem exists_weakLimit_iff_map {ι : Type*} {L : Filter ι} [L.NeBot]
    (hf : IsClosedEmbedding f) (μs : ι → ProbabilityMeasure A) :
    (∃ μ : ProbabilityMeasure A, Tendsto μs L (𝓝 μ)) ↔
      ∃ ν : ProbabilityMeasure B, Tendsto (fun i => (μs i).map f) L (𝓝 ν) := by
  constructor
  · rintro ⟨μ, hμ⟩
    exact ⟨μ.map f, ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      μs μ hμ hf.continuous⟩
  · rintro ⟨ν, hν⟩
    have hclosed := isClosedEmbedding_probabilityMeasure_map hf
    have hmem : ν ∈ range (fun μ : ProbabilityMeasure A => μ.map f) :=
      hclosed.isClosed_range.mem_of_tendsto hν (Eventually.of_forall fun i => ⟨μs i, rfl⟩)
    obtain ⟨μ, rfl⟩ := hmem
    exact ⟨μ, hclosed.isEmbedding.tendsto_nhds_iff.mpr hν⟩

end Freezing1
