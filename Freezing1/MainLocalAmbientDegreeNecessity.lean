module

public import Freezing1.MainLocalAmbient
public import Freezing1.MainLocalDegreeNecessity

/-! The all-vertex degree obstruction in the full unordered source ambient.
Closedness of the chronological image supplies the source of any ambient
weak limit; no support hypothesis is assumed. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open Forward ForwardInfiniteHistory
open scoped Topology

theorem source_local_limit_of_diagonal_tendsto_via_degrees
    (rows : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i)
    {ν : ProbabilityMeasure UnorderedLocal.Tree}
    (hconv : Tendsto (fun n => sourceLocalProbabilityLaw (rows n) n) atTop (𝓝 ν)) :
    SourceAlmostSureLocalConvergence y := by
  obtain ⟨μ, _, hμ⟩ := LocalTree.ambient_weakLimit_supported
    (fun n => localProbabilityLaw (rows n) n) ν hconv
  apply (source_almostSureLocalConvergence_iff y).mpr
  exact ae_local_limit_of_diagonal_tendsto_via_degrees rows y hxy hμ

end Freezing1
