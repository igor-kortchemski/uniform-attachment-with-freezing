module

public import Freezing1.LocalTreeRootDegree
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# A necessary tightness condition for local weak convergence

The degree of the root is a continuous natural-valued observable. Portmanteau
on its clopen tails and continuity from above give eventual tightness for
any weakly convergent sequence of locally finite tree laws.
-/

@[expose] public section

namespace Freezing1.LocalTree

open Filter MeasureTheory
open scoped Topology Classical ENNReal

theorem rootDegree_tail_isClopen (d : ℕ) :
    IsClopen {T : Tree | d < rootDegree T} :=
  (isClopen_discrete {k : ℕ | d < k}).preimage continuous_rootDegree

theorem rootDegree_tail_tendsto_zero (ν : ProbabilityMeasure Tree) :
    Tendsto (fun d : ℕ => (ν : Measure Tree).real {T | d < rootDegree T})
      atTop (𝓝 0) := by
  have he : (⋂ d : ℕ, {T : Tree | d < rootDegree T}) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro T hT
    have hh := Set.mem_iInter.mp hT (rootDegree T)
    exact (lt_irrefl (rootDegree T)) hh
  have hm : Antitone (fun d : ℕ => {T : Tree | d < rootDegree T}) :=
    fun a b hab T hT => lt_of_le_of_lt hab hT
  have hh := tendsto_measure_iInter_atTop (μ := (ν : Measure Tree))
    (fun d => (rootDegree_tail_isClopen d).isClosed.measurableSet.nullMeasurableSet)
    hm ⟨0, measure_ne_top _ _⟩
  simp only [he, measure_empty, Function.comp_def] at hh
  exact ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _) |>.mpr hh

theorem eventually_rootDegree_tail_lt_of_tendsto
    {μ : ℕ → ProbabilityMeasure Tree} {ν : ProbabilityMeasure Tree}
    (hμ : Tendsto μ atTop (𝓝 ν)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ d : ℕ, ∀ᶠ n in atTop,
      (μ n : Measure Tree).real {T | d < rootDegree T} < δ := by
  obtain ⟨d, hd⟩ := ((rootDegree_tail_tendsto_zero ν).eventually
    (gt_mem_nhds hδ)).exists
  have hh := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ
    (rootDegree_tail_isClopen d)
  have hR := NNReal.tendsto_coe.mpr hh
  simp only [← ProbabilityMeasure.measureReal_eq_coe_coeFn] at hR
  exact ⟨d, hR.eventually (gt_mem_nhds hd)⟩

end Freezing1.LocalTree
