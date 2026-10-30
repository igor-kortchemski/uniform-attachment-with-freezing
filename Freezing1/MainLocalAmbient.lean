module

public import Freezing1.ChronologicalAmbientLaws
public import Freezing1.MainLocalLimit
public import Freezing1.MainGeometricLimit

/-!
# The local main results in the full source ambient

The closed embedding retains every actual incoming birth-time label and
every frozen/active vertex label. Existence of pathwise and weak limits in
the unrestricted unordered labelled-tree ambient is equivalent to existence
in the original chronological model.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open Forward ForwardInfiniteHistory
open scoped Topology

noncomputable def sourceLocalProbabilityLaw (x : SignSequence) (n : ℕ) :
    ProbabilityMeasure UnorderedLocal.Tree :=
  (ForwardInfiniteHistory.localProbabilityLaw x n).map LocalTree.toUnordered

noncomputable def sourceLocalLimitLaw (x : SignSequence) :
    ProbabilityMeasure UnorderedLocal.Tree :=
  (ForwardInfiniteHistory.localLimitLaw x).map LocalTree.toUnordered

def SourceDiagonalLocalConvergence (x : ℕ → SignSequence) : Prop :=
  ∃ ν : ProbabilityMeasure UnorderedLocal.Tree,
    Tendsto (fun n => sourceLocalProbabilityLaw (x n) n) atTop (𝓝 ν)

def SourceAlmostSureLocalConvergence (x : SignSequence) : Prop :=
  ∀ᵐ H ∂ForwardInfiniteHistory.fullLaw x, ∃ q : UnorderedLocal.Tree,
    Tendsto (fun n => LocalTree.toUnordered (localTreeOfState (H n))) atTop (𝓝 q)

theorem source_diagonalLocalConvergence_iff (x : ℕ → SignSequence) :
    SourceDiagonalLocalConvergence x ↔ DiagonalLocalConvergence x :=
  (LocalTree.exists_weakLimit_iff_ambient
    (fun n => ForwardInfiniteHistory.localProbabilityLaw (x n) n)).symm

theorem source_almostSureLocalConvergence_iff (x : SignSequence) :
    SourceAlmostSureLocalConvergence x ↔ AlmostSureLocalConvergence x := by
  constructor
  · intro hc
    exact hc.mono (fun H hH =>
      (LocalTree.exists_localLimit_iff_ambient (fun n => localTreeOfState (H n))).mpr hH)
  · intro hc
    exact hc.mono (fun H hH =>
      (LocalTree.exists_localLimit_iff_ambient (fun n => localTreeOfState (H n))).mp hH)

theorem source_local_convergence_equivalences
    (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤) :
    (SourceDiagonalLocalConvergence x ↔ SourceAlmostSureLocalConvergence y) ∧
      (SourceAlmostSureLocalConvergence y ↔
        Tendsto (freezingReciprocalSum y) atTop atTop) := by
  rw [source_diagonalLocalConvergence_iff, source_almostSureLocalConvergence_iff]
  exact local_convergence_equivalences x y hxy hτ

theorem source_local_convergence_common_limit
    (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤)
    (hdiv : Tendsto (freezingReciprocalSum y) atTop atTop) :
    AEMeasurable (fun H => LocalTree.toUnordered (localLimit H)) (fullLaw y) ∧
    (∀ᵐ H ∂fullLaw y,
      Tendsto (fun n => LocalTree.toUnordered (localTreeOfState (H n))) atTop
        (𝓝 (LocalTree.toUnordered (localLimit H)))) ∧
    Tendsto (sourceLocalProbabilityLaw y) atTop (𝓝 (sourceLocalLimitLaw y)) ∧
    Tendsto (fun n => sourceLocalProbabilityLaw (x n) n) atTop (𝓝 (sourceLocalLimitLaw y)) := by
  obtain ⟨hm, ha, hf, hd⟩ := local_convergence_common_limit x y hxy hτ hdiv
  refine ⟨LocalTree.continuous_toUnordered.measurable.comp_aemeasurable hm, ?_, ?_, ?_⟩
  · exact ha.mono (fun H hH => (LocalTree.tendsto_toUnordered_iff _ _).mpr hH)
  · exact (LocalTree.tendsto_probabilityLaw_toUnordered_iff _ _).mpr hf
  · exact (LocalTree.tendsto_probabilityLaw_toUnordered_iff _ _).mpr hd

namespace ForwardAnnealed

/-- The actual iid-sign history also converges in the unrestricted labelled
source ambient; the same chronological limit gives the geometric plane tree. -/
theorem iid_signs_source_ambient_local_limit (p : unitInterval) (hp : (p : ℝ) < 1) :
    (∀ᵐ H ∂fullLaw p,
      Tendsto (fun n => LocalTree.toUnordered (localTreeOfState (H n))) atTop
        (𝓝 (LocalTree.toUnordered (ForwardInfiniteHistory.localLimit H)))) ∧
    Tendsto (fun n => (localProbabilityLaw p n).map LocalTree.toUnordered) atTop
      (𝓝 ((localLimitLaw p).map LocalTree.toUnordered)) ∧
    (fullLaw p).map
      (fun H => LocalTree.toPlaneTree (ForwardInfiniteHistory.localLimit H)) =
        PlaneTree.geometricBienaymeLaw p := by
  refine ⟨?_, ?_, (iid_signs_geometric_local_limit p hp).2⟩
  · exact (fullLaw_tendsto_localLimit p hp).mono
      (fun H hH => (LocalTree.tendsto_toUnordered_iff _ _).mpr hH)
  · exact (LocalTree.tendsto_probabilityLaw_toUnordered_iff _ _).mpr
      (tendsto_localProbabilityLaw p hp)

end ForwardAnnealed

end Freezing1
