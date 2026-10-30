module

public import Freezing1.LocalDegreeTightness
public import Freezing1.ForwardVertexDegree
public import Freezing1.ForwardHeight

/-! Finite local balls control the degree of every named vertex, including
vertices other than the root. Their cardinalities are continuous observables. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology ENNReal Classical

namespace LocalTree

def ballCard (r : ℕ) (T : Tree) : ℕ := (T.val r).card

theorem continuous_ballCard (r : ℕ) : Continuous (ballCard r) :=
  (continuous_of_discreteTopology : Continuous (fun B : Ball => B.card)).comp
    ((continuous_apply r).comp continuous_subtype_val)

theorem natObservable_tail_isClopen (F : Tree → ℕ) (hF : Continuous F) (d : ℕ) :
    IsClopen {T | d < F T} := (isClopen_discrete {k : ℕ | d < k}).preimage hF

theorem natObservable_tail_tendsto_zero (F : Tree → ℕ) (hF : Continuous F)
    (ν : ProbabilityMeasure Tree) :
    Tendsto (fun d : ℕ => (ν : Measure Tree).real {T | d < F T}) atTop (𝓝 0) := by
  have he : (⋂ d : ℕ, {T | d < F T}) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro T hT
    exact (lt_irrefl (F T)) (Set.mem_iInter.mp hT (F T))
  have hm : Antitone (fun d : ℕ => {T | d < F T}) :=
    fun a b hab T hT => lt_of_le_of_lt hab hT
  have hh := tendsto_measure_iInter_atTop (μ := (ν : Measure Tree))
    (fun d => (natObservable_tail_isClopen F hF d).isClosed.measurableSet.nullMeasurableSet)
    hm ⟨0, measure_ne_top _ _⟩
  simp only [he, measure_empty, Function.comp_def] at hh
  exact ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _) |>.mpr hh

theorem eventually_natObservable_tail_lt_of_tendsto
    {μ : ℕ → ProbabilityMeasure Tree} {ν : ProbabilityMeasure Tree}
    (hμ : Tendsto μ atTop (𝓝 ν)) (F : Tree → ℕ) (hF : Continuous F)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ d : ℕ, ∀ᶠ n in atTop, (μ n : Measure Tree).real {T | d < F T} < δ := by
  obtain ⟨d, hd⟩ := ((natObservable_tail_tendsto_zero F hF ν).eventually
    (gt_mem_nhds hδ)).exists
  have hh := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ
    (natObservable_tail_isClopen F hF d)
  have hR := NNReal.tendsto_coe.mpr hh
  simp only [← ProbabilityMeasure.measureReal_eq_coe_coeFn] at hR
  exact ⟨d, hR.eventually (gt_mem_nhds hd)⟩

end LocalTree

namespace Forward

theorem ValidAt.vertexDegree_le_ballCard {n : ℕ} {s : State} (hs : ValidAt n s) (r : ℕ) :
    vertexDegree s r ≤ LocalTree.ballCard (r + 1) (localTreeOfState s) := by
  have hsub : vertexNeighbors s r ⊆ s.vertices.filter (fun v => s.height v ≤ r + 1) := by
    intro v hv
    obtain ⟨hvm, hadj⟩ := Finset.mem_filter.mp hv
    have hrm := (hs.adj_mem hadj).1
    have hrh := hs.height_le_id r hrm
    have hh := hs.adj_height hadj
    exact Finset.mem_filter.mpr ⟨hvm, by omega⟩
  rw [LocalTree.ballCard, hs.localTreeOfState_balls, card_localBall]
  exact Finset.card_le_card hsub

end Forward
end Freezing1
