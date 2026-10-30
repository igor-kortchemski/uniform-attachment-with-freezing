module

public import Freezing1.ForwardDegreeCoupling
public import Freezing1.LocalBallTightness
public import Freezing1.ForwardDegreeLocalCriterion

/-! The source's all-vertex obstruction to diagonal local convergence.
Fixed-prefix coupling and degree growth transfer a positive mass to large
finite balls, which is incompatible with any local weak limit. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace Forward

theorem localProbabilityLaw_ballCard_tail_real (x : SignSequence) (n r d : ℕ) :
    (ForwardInfiniteHistory.localProbabilityLaw x n : Measure LocalTree.Tree).real
        {T | d < LocalTree.ballCard r T} =
      (treeLaw x n).real {s | d < LocalTree.ballCard r (localTreeOfState s)} := by
  change (localTreeLaw x n).real _ = _
  unfold localTreeLaw Measure.real
  rw [Measure.map_apply measurable_from_top
    (LocalTree.natObservable_tail_isClopen _ (LocalTree.continuous_ballCard r) d).isClosed.measurableSet]
  rfl

theorem treeLaw_vertexDegree_tail_le_local_ball_tail (x : SignSequence) (n r d : ℕ) :
    (treeLaw x n).real {s | d < vertexDegree s r} ≤
      (ForwardInfiniteHistory.localProbabilityLaw x n : Measure LocalTree.Tree).real
        {T | d < LocalTree.ballCard (r + 1) T} := by
  rw [localProbabilityLaw_ballCard_tail_real]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [treeLaw_valid x n] with s hs hdeg
  exact hdeg.trans_le (hs.vertexDegree_le_ballCard r)

theorem diagonal_ballCard_not_tight_of_degree_unbounded
    (rows : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i) (r : ℕ)
    (hE : (ForwardInfiniteHistory.fullLaw y) (ForwardInfiniteHistory.degreeUnbounded r) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℕ, ∀ᶠ n in atTop,
      δ ≤ (ForwardInfiniteHistory.localProbabilityLaw (rows n) n : Measure LocalTree.Tree).real
        {T | d < LocalTree.ballCard (r + 1) T} := by
  obtain ⟨δ, hδ, hd⟩ := ForwardInfiniteHistory.degree_tails_positive_of_unbounded_probability y r hE
  refine ⟨δ, hδ, fun d => ?_⟩
  obtain ⟨m, hm⟩ := (hd d).exists
  filter_upwards [eventually_ge_atTop m, eventually_treeLaw_eq hxy m] with n hmn hprefix
  calc
    δ ≤ (treeLaw y m).real {s | d < vertexDegree s r} := hm
    _ = (treeLaw (rows n) m).real {s | d < vertexDegree s r} := by rw [hprefix]
    _ ≤ (treeLaw (rows n) n).real {s | d < vertexDegree s r} :=
      ForwardInfiniteHistory.treeLaw_vertexDegree_tail_real_mono (rows n) r d hmn
    _ ≤ _ := treeLaw_vertexDegree_tail_le_local_ball_tail (rows n) n r d

end Forward

namespace ForwardInfiniteHistory

open Forward

theorem degreeUnbounded_null_of_diagonal_local_tendsto
    (rows : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i)
    {ν : ProbabilityMeasure LocalTree.Tree}
    (hconv : Tendsto (fun n => localProbabilityLaw (rows n) n) atTop (𝓝 ν)) (r : ℕ) :
    (fullLaw y) (degreeUnbounded r) = 0 := by
  by_contra hE
  obtain ⟨δ, hδ, htail⟩ := diagonal_ballCard_not_tight_of_degree_unbounded rows y hxy r hE
  obtain ⟨d, hd⟩ := LocalTree.eventually_natObservable_tail_lt_of_tendsto hconv
    (LocalTree.ballCard (r + 1)) (LocalTree.continuous_ballCard _) hδ
  obtain ⟨n, hn, hn'⟩ := ((htail d).and hd).exists
  exact (not_lt_of_ge hn) hn'

/-- Source A24 / (I)⇒(II), using all vertex degrees and local-ball
tightness directly. The source's main freezing-series theorem is not used
as a premise or invoked to obtain this conclusion. -/
theorem ae_local_limit_of_diagonal_tendsto_via_degrees
    (rows : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i)
    {ν : ProbabilityMeasure LocalTree.Tree}
    (hconv : Tendsto (fun n => localProbabilityLaw (rows n) n) atTop (𝓝 ν)) :
    ∀ᵐ H ∂fullLaw y, ∃ T : LocalTree.Tree,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 T) := by
  have hnot : ∀ᵐ H ∂fullLaw y, ∀ r, H ∉ degreeUnbounded r := by
    apply ae_all_iff.mpr
    intro r
    rw [ae_iff]
    have he : {H : History | H ∈ degreeUnbounded r} = degreeUnbounded r := by
      ext H
      rfl
    simpa only [not_not, he] using degreeUnbounded_null_of_diagonal_local_tendsto rows y hxy hconv r
  filter_upwards [fullLaw_valid y, fullLaw_legalOrHeld y, hnot] with H hv hl hH
  apply exists_local_limit_of_degree_bounded hv hl
  intro r
  have he := hH r
  change ¬∀ d : ℕ, ∃ n : ℕ, d < vertexDegree (H n) r at he
  push Not at he
  exact he

end ForwardInfiniteHistory
end Freezing1
